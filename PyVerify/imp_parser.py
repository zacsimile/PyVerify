import sys
import re
from lark import Lark, Transformer, Tree
from lark.lexer import Token
from itertools import chain



class ImpParser:
    def __init__(self):
        """
        Lark parser, activate!
        """
        self.imp_parser = Lark.open('imp.lark', parser='earley', lexer='standard')

    def parse_file(self, fn):
        """
        Opens a .imp file, splits it into a list of commands, passes the commands to parse().

        Parameters
        ----------
        fn : string
            IMP file to read.

        Returns
        -------
        ast : list
            Abstract syntax tree for IMP program.
        """

        # Check that we have an IMP file
        if not (isinstance(fn, str) and fn.split('.')[1] == 'imp'):
            raise ValueError('File must be .imp.')

        # Read the file data in
        stream = open(fn, 'r')
        data = stream.read()
        stream.close()

        #print(data)

        # Parse the commands to an AST
        ast = self.parse(data)

        return ast

    def parse(self, prog):
        """
        Converts a series of IMP commands to an AST.

        Parameters
        ----------
        prog : string
            IMP program.

        Returns
        -------
        ast : list
            Abstract syntax tree for IMP program.
        """
        return self.imp_parser.parse(prog)


class ImpToGC(Transformer):
    def __init__(self):
        Transformer.__init__(self)
        self.tmpcount = -1

    def _not(self, b):
        """
        Negate a boolean.
        """
        if type(b) == list:
            out = []
            for t in b:
                out.extend(self._not(t))
            return out

        if b.data == 'bparen':
            return self._not(b.children)
        if b.data == 'eq':
            return [Tree('neq', b.children)]
        if b.data == 'neq':
            return [Tree('eq', b.children)]
        if b.data == 'geq':
            return [Tree('lt', b.children)]
        if b.data == 'lt':
            return [Tree('geq', b.children)]
        if b.data == 'leq':
            return [Tree('gt', b.children)]
        if b.data == 'gt':
            return [Tree('leq', b.children)]
        if b.data == 'bor':
            return [Tree('band', self._not(b.children))]
        if b.data == 'band':
            return [Tree('bor', self._not(b.children))]
        if b.data == 'not':
            return [b.children]
        else:
            # Do not fail silently
            print(b)
            raise NotImplemented

    def assemble_pre(self, l):
        """
        Group preconditions.
        """
        pre = []
        for t in l:
            if type(t) == Tree and t.data == 'pre':
                pre.extend(t.children)
        if len(pre) > 1:
            previous = pre.pop()
            while len(pre) > 0:
                current = pre.pop()
                previous = [Tree('band', [current, previous])]
            return Tree('assume', previous)
        if len(pre) == 1:
            return Tree('assume', pre)

    def assemble_post(self, l):
        """
        Group postconditions.
        """
        post = []
        for t in l:
            if type(t) == Tree and t.data == 'post':
                post.extend(t.children)
        if len(post) > 1:
            postvious = post.pop()
            while len(post) > 0:
                current = post.pop()
                postvious = [Tree('band', [current, postvious])]
            return Tree('assert', postvious)
        return Tree('assert', post)

    def assemble_invariants(self, l):
        """
        Group invariants.
        """
        inv = []
        for t in l:
            if type(t) == Tree and t.data == 'inv':
                inv.extend(t.children)
        if len(inv) > 1:
            invious = inv.pop()
            while len(inv) > 0:
                current = inv.pop()
                invious = [Tree('band', [current, invious])]
            return invious
        return inv

    def assemble_havoc(self, l):
        """
        Group havoc.
        """
        hav = []
        for t in l:
            if type(t) == Tree:
                if t.data == 'havoc':
                    hav.extend([Tree('havoc', t.children)])
                else:
                    hav.extend(self.assemble_havoc(t.children))
            if type(t) == list:
                hav.extend(self.assemble_havoc(t))
        return hav

    def replacetree(self, t, find_token, replace_token):
        """
        Recursively iterate through tree t and replace find_token with replace_token. Used for replacement rule.

        Parameters
        ----------
        t : Tree
            A tree over which to iterate.
        find_token : Token
            Variable to find.
        replace_token : str
            Replacement variable.

        Returns
        -------
        Tree
            Tree with replaced token.
        """
        out = []
        for v in t.children:
            if type(v) == Token:
                if v.value == find_token.value:
                    out.extend([Token('NAME', replace_token)])
                else:
                    out.extend([Token(v.type, v.value)])
            if type(v) == Tree:
                out.extend([Tree(v.data, self.replacetree(v, find_token, replace_token))])
        return out

    def assign(self, a):
        """
        Rule for parsing ?assign: NAME ":=" aexp ";" to guarded command.

        Parameters
        ----------
        a : list
           [Token.NAME, Tree('aexp', _)]

        Returns
        -------
        List of guarded commands.
        """
        self.tmpcount += 1
        varstring = 'tmp_' + str(self.tmpcount)
        out = []
        out.append(Tree('assume', [Tree('eq', [Token('NAME', varstring), Token(a[0].type, a[0].value)])]))
        out.append(Tree('havoc', [Token(a[0].type, a[0].value)]))
        if type(a[1]) == Tree:
            replacetree = Tree(a[1].data, self.replacetree(a[1], a[0], varstring))
            out.append(Tree('assume', [Tree('eq', [Token(a[0].type, a[0].value), replacetree])]))
        else:
            try:
                if a[0].value != a[1].value:
                    out.append(Tree('assume', [Tree('eq', [Token(a[0].type, a[0].value), Token(a[1].type, a[1].value)])]))
                if a[0].value == a[1].value:
                    out.append(Tree('assume', [Tree('eq', [Token(a[0].type, a[0].value), Token('NAME', varstring)])]))
            except AttributeError:
                # Don't fail silently
                print(a)
                raise
        return out

    def block(self, b):
        """
        Returns a tree block. Had to use this to "in place" clear out extra brackets generated from assign, etc.
        """
        out = []
        for v in b:
            if isinstance(type(v), type(None)):
                continue
            if type(v) == list:
                for a in v:
                    out.extend([a])
            else:
                out.extend([v])
        return Tree('block', out)

    def write(self, a):
        """
        Convert array write to a guaraded command.
        """
        return self.assign([a[0], Tree('write', a)])

    def flatten(self, l):
        out = []
        for a in l:
            if type(a) == Tree or type(a) == Token:
                out.extend([a])
            else:
                out.extend(a)
        return out

    def whilestmt(self, w):
        """
        Convert while statement to guarded command.
        """
        invs = self.assemble_invariants(w)
        b = self.flatten([Tree('assert', invs), self.assemble_havoc(w), Tree('assume', invs),
             Tree('wpor', [Tree('block', [Tree('assume', [w[0]]), w[-1], Tree('assert', invs), Tree('assume', [Token('const_false', False)])]),
                           Tree('assume', self._not(w[0]))])])
        out = []
        for v in b:
            if isinstance(type(v), type(None)):
                continue
            if type(v) == list:
                for a in v:
                    out.extend([a])
            else:
                out.extend([v])
        if len(out) > 0:
            return out

    def ifstmt(self, i):
        b = [Tree('assume', [i[0]]), i[1]]
        out = []
        for v in b:
            if isinstance(type(v), type(None)):
                continue
            if type(v) == list:
                for a in v:
                    out.extend([a])
            else:
                out.extend([v])
        if len(i) > 2:
            out = Tree('wpor', [Tree('block', [Tree('assume', [i[0]]), i[1]]),
                                Tree('block', [Tree('assume', self._not(i[0])), i[2]])])
        return out

    def program(self, p):
        """
        Assemble program in the correct order.
        """
        b = [p[0], self.assemble_pre(p), p[-1], self.assemble_post(p)]
        out = []
        for v in b:
            if isinstance(type(v), type(None)):
                continue
            if type(v) == list:
                for a in v:
                    out.extend([a])
            else:
                out.extend([v])
        return Tree('program', out)

    def parassign(self, p):
        """
        Split pairwise assignment into two assign statements.
        """
        out = []
        out.extend(self.assign([p[0], p[2]]))
        out.extend(self.assign([p[1], p[3]]))
        return out

    def neg(self, n):
        return Tree('sub', [Token('NUMBER', 0), n[0]])

class WpCalc:
    def __init__(self):
        self.tmpcount = -1

    def replacetree(self, t, find_token, replace_token):
        """
        Recursively iterate through tree t and replace find_token with replace_token. Used for replacement rule.

        Parameters
        ----------
        t : Tree
            A tree over which to iterate.
        find_token : Token
            Variable to find.
        replace_token : str
            Replacement variable.

        Returns
        -------
        Tree
            Tree with replaced token.
        """
        out = []
        for v in t.children:
            if type(v) == Token:
                if v.value == find_token.value:
                    out.extend([Token('NAME', replace_token)])
                else:
                    out.extend([Token(v.type, v.value)])
            if type(v) == Tree:
                out.extend([Tree(v.data, self.replacetree(v, find_token, replace_token))])
        #print(out)
        return out

    def flatten(self, l):
        out = []
        for a in l:
            if type(a) == Tree or type(a) == Token:
                out.extend([a])
            else:
                out.extend(a)
        return out

    def wpify(self, gc, wp):
        #print(wp)
        if type(gc) == Tree:
            if gc.data == 'assert':
                return Tree('band', self.flatten([gc.children, wp]))
            if gc.data == 'assume':
                return Tree('implies', self.flatten([gc.children, wp]))
            if gc.data == 'havoc':
                self.tmpcount += 1
                varstring = 'pa_' + str(self.tmpcount)
                return self.wpify(gc.children, self.replacetree(wp, gc.children[0], varstring))
            if gc.data == 'wpor':
                return Tree('band', self.flatten([self.wpify(gc.children[0], wp), self.wpify(gc.children[1], wp)]))
            else:
                return self.wpify(gc.children, wp)
        if type(gc) == list:
            try:
                current = gc.pop()
                return self.wpify(gc, self.wpify(current, wp))
            except IndexError:
                return wp
        if type(gc) == Token:
            return wp

class VcToSMT(Transformer):

    def read(self, r):
        return "(select " + ' '.join(str(v) for v in r) + ")"

    def write(self, w):
        return "(store " + ' '.join(str(v) for v in w) + ")"

    def implies(self, i):
        return "(=> " + ' '.join(str(v) for v in i) + ")"

    def band(self, a):
        return "(and " + ' '.join(str(v) for v in a) + ")"

    def eq(self, e):
        return "(= " + ' '.join(str(v) for v in e) + ")"

    def neq(self, e):
        return "(not (= " + ' '.join(str(v) for v in e) + "))"

    def gt(self, ge):
        return "(> " + ' '.join(str(v) for v in ge) + ")"

    def lt(self, le):
        return "(< " + ' '.join(str(v) for v in le) + ")"

    def geq(self, ge):
        return "(>= " + ' '.join(str(v) for v in ge) + ")"

    def leq(self, le):
        return "(<= " + ' '.join(str(v) for v in le) + ")"

    def mult(self, m):
        return "(* " + ' '.join(str(v) for v in m) + ")"

    def add(self, a):
        return "(+ " + ' '.join(str(v) for v in a) + ")"

    def sub(self, s):
        return "(- " + ' '.join(str(v) for v in s) + ")"

    def div(self, d):
        return "(div " + ' '.join(str(v) for v in d) + ")"

    def mod(self, m):
        return "(mod " + ' '.join(str(v) for v in m) + ")"

    def bparen(self, b):
        return ''.join(str(v) for v in b)

    def forall(self, f):
        return "(forall (" + ' '.join('(%s Int)' % v for v in f[:-1]) + ') ' + str(f[-1]) + ')'

    def const_false(self, f):
        return "false"

    def const_true(self, t):
        return "true"

    def program(self, p):
        return '(assert ' + ' '.join(str(v) for v in p) + ')(check-sat)(exit)'

def get_variables(vc):
    out = []
    for t in list(vc.iter_subtrees()):
        for a in t.children:
            try:
                if a.type == 'NAME':
                    out.extend([a])
            except AttributeError:
                pass
    return ' '.join('(declare-fun %s () Int)' % v for v in list(set(out)))

if __name__ == '__main__':
    imp_parser = ImpParser()
    tree = imp_parser.parse_file(sys.argv[1])
    try:
        #print(tree.pretty())
        gc = ImpToGC().transform(tree)
        #print(gc.pretty())
        #print(gc)
        #print(wpify(gc).pretty())
        #print(ComputeWP().compute(gc.children))
        vc = WpCalc().wpify(gc, Token('const_true', True))
        var_string = get_variables(vc)
        #print(vc.pretty())
        vc_string = VcToSMT().transform(vc)
        vc_string = vc_string.replace('False', 'false')
        vc_string = vc_string.replace('True', 'true')
        program = var_string + "(assert " + vc_string + ") (check-sat) (exit)"
        with open('current.smt2', 'w') as file:
            file.write(program)
        import subprocess
        res = subprocess.check_output("z3 current.smt2", shell=True)
        if res.strip() == b'sat':
            print("valid")
        else:
            print("invalid")
        #print(gc.pretty())
        #print(str(wp) + '\n')
        # vc = gc + ', true'
        # vc_list = vc.split(';')
        # vc_prev = vc_list.pop().strip()
        # vc_nested = 'wp(' + vc_prev + ')'
        # while len(vc_list) > 0:
        #     vc_new = vc_list.pop().strip()
        #     vc_anded = vc_new.split('|||')
        #     if len(vc_anded) > 1:
        #         res = vc_prev.split(',')[-1]
        #         vc_nested = 'wp(' + vc_anded[0] + ', ' + res + ') && ' + vc_nested
        #     else:
        #         vc_nested = 'wp(' + vc_new + ', ' + vc_nested + ')'
        #     vc_prev = vc_new
        # print(vc_nested)

    except AttributeError:
        raise

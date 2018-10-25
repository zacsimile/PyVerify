import os
import sys
from lark import Lark, Transformer, Tree
from lark.lexer import Token


class ImpParser:
    def __init__(self):
        """
        Lark parser, activate!
        """
        self.imp_parser = Lark.open(os.path.join(os.path.dirname(__file__), 'imp.lark'), parser='earley', lexer='standard')

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
        _, extension = os.path.splitext(fn)
        if not (isinstance(fn, str) and extension == '.imp'):
            raise ValueError('File must be .imp.')

        # Read the file data in
        stream = open(fn, 'r')
        data = stream.read()
        stream.close()

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
            return self.flatten([Tree('neq', b.children)])
        if b.data == 'neq':
            return self.flatten([Tree('eq', b.children)])
        if b.data == 'geq':
            return self.flatten([Tree('lt', b.children)])
        if b.data == 'lt':
            return self.flatten([Tree('geq', b.children)])
        if b.data == 'leq':
            return self.flatten([Tree('gt', b.children)])
        if b.data == 'gt':
            return self.flatten([Tree('leq', b.children)])
        if b.data == 'forall':
            return self.flatten([Tree('exists', b.children)])
        if b.data == 'exists':
            return self.flatten([Tree('forall', b.children)])
        if b.data == 'bor':
            return self.flatten([Tree('band', self._not(b.children))])
        if b.data == 'band':
            return self.flatten([Tree('bor', self._not(b.children))])
        if b.data == 'not':
            return self.flatten([b.children])
        else:
            # Do not fail silently
            print(b)
            raise NotImplemented

    def assemble_pre(self, l):
        """
        Group conditions.
        """
        pre = []
        for t in l:
            if type(t) == Tree and t.data == 'pre':
                pre.extend(t.children)
        if len(pre) > 1:
            previous = pre.pop()
            while len(pre) > 0:
                current = pre.pop()
                previous = [Tree('band', self.flatten([current, previous]))]
            return Tree('assume', previous)
        if len(pre) == 1:
            return Tree('assume', pre)
        return pre

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
                postvious = [Tree('band', self.flatten([current, postvious]))]
            return Tree('assert', postvious)
        if len(post) == 1:
            return Tree('assert', post)
        return post

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
                invious = [Tree('band', self.flatten([current, invious]))]
            return invious
        if len(inv) == 1:
            return inv
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

    def replace_tree(self, t, find_token, replace_token):
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
                out.extend([Tree(v.data, self.replace_tree(v, find_token, replace_token))])
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
            # if a[1].data == 'write':
            #     self.tmpcount += 1
            #     varstring = 'tmp_' + str(self.tmpcount)
            replace_tree = Tree(a[1].data, self.replace_tree(a[1], a[0], varstring))
            out.append(Tree('assume', [Tree('eq', [Token(a[0].type, a[0].value), replace_tree])]))
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
        return self.flatten(b)

    def write(self, a):
        """
        Convert array write to a guaraded command.
        """
        #print('write', a)
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
        b_mid = self.flatten([Tree('assume', [w[0]]), w[-1], Tree('assert', invs), Tree('assume', [Tree('const_false', [])])])
        b = self.flatten([Tree('assert', invs),
                          self.assemble_havoc(w),
                          Tree('assume', invs),
                          Tree('wpor', [Tree('block', b_mid), Tree('assume', self._not(w[0]))])])
        return b

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
            out = Tree('wpor', self.flatten([Tree('block', self.flatten([Tree('assume', [i[0]]), i[1]])),
                                             Tree('block', self.flatten([Tree('assume', self._not(i[0])), i[2]]))]))
        return out

    def program(self, p):
        """
        Assemble program in the correct order.
        """
        return Tree('program', self.flatten([p[0], self.assemble_pre(p), p[-1], self.assemble_post(p)]))

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

    def replace_tree(self, t, find_token, replace_token):
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
                out.extend([Tree(v.data, self.replace_tree(v, find_token, replace_token))])
        return out

    def flatten(self, l):
        out = []
        for a in l:
            if type(a) == Tree or type(a) == Token:
                out.extend([a])
            else:
                out.extend(a)
        #print(out)
        return out

    def wpify(self, gc, wp):
        """
        Convert guarded commands to weakest pres.
        """
        if type(gc) == Tree:
            if gc.data == 'assert':
                return Tree('band', self.flatten([gc.children, wp]))
            if gc.data == 'assume':
                return Tree('implies', self.flatten([gc.children, wp]))
            if gc.data == 'havoc':
                self.tmpcount += 1
                varstring = 'pa_' + str(self.tmpcount)
                return Tree(wp.data, self.replace_tree(wp, gc.children[0], varstring))
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
        return "(and " + " ".join(str(v) for v in a) + ")"

    def bor(self, a):
        return "(or " + " ".join(str(v) for v in a) + ")"

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
        return ' '.join(str(v) for v in b)

    def bnot(self, b):
        return '(not' + ' '.join(str(v) for v in b) + ')'

    def forall(self, f):
        return "(forall (" + ' '.join('(%s Int)' % v for v in f[:-1]) + ') ' + str(f[-1]) + ')'

    def exists(self, f):
        return "(exists (" + ' '.join('(%s Int)' % v for v in f[:-1]) + ') ' + str(f[-1]) + ')'

    def const_true(self, t):
        return 'true'

    def const_false(self, f):
        return 'false'


def get_variables(vc):
    out = []
    arr = []
    eq = []
    return_str = ''

    for t in list(vc.iter_subtrees()):
        if t.data == 'eq':
            eq.extend([t.children])

        if t.data == 'read' or t.data == 'write':
            arr.extend([t.children[0]])
        else:
            for a in t.children:
                try:
                    if a.type == 'NAME':
                        out.extend([a])
                except AttributeError:
                    pass

    # Make sure we don't misclassify arrays as variables
    for t in eq:
        if (t[0] in out and t[1] in arr):
            arr.extend([t[0]])
            while t[0] in out:
                out.remove(t[0])
        if (t[1] in out and t[0] in arr):
            arr.extend([t[1]])
            while t[1] in out:
                out.remove(t[1])

    return_str += ' '.join('(declare-fun %s () Int)' % v for v in list(set(out)-set(arr)))
    return_str += ' ' + ' '.join('(declare-const %s (Array Int Int))' % v for v in list(set(arr)))
    return return_str


def unit_parse(file):
    imp_parser = ImpParser()
    tree = imp_parser.parse_file(file)
    try:
        #print(tree)
        gc = ImpToGC().transform(tree)
        #print(gc.pretty())
        vc = WpCalc().wpify(gc, [Tree('const_true', [])])
        # print(vc)
        var_string = get_variables(vc)
        vc_string = VcToSMT().transform(vc)
        program = var_string + " (push) (assert (not " + vc_string + ")) (check-sat) (pop) (exit)"
        print(program)
        #print(gc.pretty())
        #print('\n' + vc_string + '\n')
        with open('current.smt2', 'w') as fp:
            fp.write(program)
        import subprocess
        try:
            res = subprocess.check_output("z3 current.smt2", shell=True)
            if res.strip() == b'unsat':
                print("valid")
                return 0
            else:
                print("invalid")
                return 1
        except subprocess.CalledProcessError:
            print("SMT couldn't run")
            #print("invalid")
    except AttributeError:
        raise


if __name__ == '__main__':
    unit_parse(sys.argv[1])
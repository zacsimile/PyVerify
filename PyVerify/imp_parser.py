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

        print(data)

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
                out.append(self._not(t))
            return out

        if b.data == 'bparen':
            return self._not(b.children)
        if b.data == 'eq':
            return Tree('neq', b.children)
        if b.data == 'neq':
            return Tree('eq', b.children)
        if b.data == 'geq':
            return Tree('lt', b.children)
        if b.data == 'lt':
            return Tree('geq', b.children)
        if b.data == 'leq':
            return Tree('gt', b.children)
        if b.data == 'gt':
            return Tree('leq', b.children)
        if b.data == 'bor':
            return Tree('band', self._not(b.children))
        if b.data == 'band':
            return Tree('bor', self._not(b.children))
        if b.data == 'not':
            return b.children
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
                previous = Tree('band', [current, previous])
            return previous
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
                postvious = Tree('band', [current, postvious])
            return postvious
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
                invious = Tree('band', [current, invious])
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
                    hav.extend(self.assemble_havoc([t.children]))
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
        out.append(Tree('assume', Tree('eq', [Token('NAME', varstring), Token(a[0].type, a[0].value)])))
        out.append(Tree('havoc', Token(a[0].type, a[0].value)))
        if type(a[1]) == Tree:
            replacetree = Tree(a[1].data, self.replacetree(a[1], a[0], varstring))
            out.append(Tree('assume', Tree('eq', [Token(a[0].type, a[0].value), replacetree])))
        else:
            try:
                if a[0].value != a[1].value:
                    out.append(Tree('assume', Tree('eq', [Token(a[0].type, a[0].value), Token(a[1].type, a[1].value)])))
                if a[0].value == a[1].value:
                    out.append(Tree('assume', Tree('eq', [Token(a[0].type, a[0].value), Token('NAME', varstring)])))
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
                    out.append(a)
            else:
                out.append(v)
        return Tree('block', out)

    def write(self, a):
        """
        Convert array write to a guaraded command.
        """
        return self.assign([a[0], Tree('write', a)])

    def whilestmt(self, w):
        """
        Convert while statement to guarded command.
        """
        invs = self.assemble_invariants(w)
        b = [Tree('assert', invs), self.assemble_havoc(w), Tree('assume', invs),
             Tree('wpor', [Tree('block', [Tree('assume', w[0]), w[-1], Tree('assert', invs), Tree('assume', False)]),
                   Tree('assume', self._not(w[0]))])]
        out = []
        for v in b:
            if type(v) == list:
                for a in v:
                    out.append(a)
            else:
                out.append(v)
        return out

    def ifstmt(self, i):
        b = [Tree('assume', i[0]), i[1]]
        out = []
        for v in b:
            if type(v) == list:
                for a in v:
                    out.append(a)
            else:
                out.append(v)
        if len(i) > 2:
            out = Tree('wpor', [Tree('block', [Tree('assume', i[0]), i[1]]),
                              Tree('block', [Tree('assume', self._not(i[0])), i[2]])])
        return out

    def program(self, p):
        """
        Assemble program in the correct order.
        """
        b = [[Token(p[0].type, p[0].value)], self.assemble_pre(p), p[-1], self.assemble_post(p)]
        out = []
        for v in b:
            if type(v) == list:
                for a in v:
                    out.append(a)
            else:
                out.append(v)
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

if __name__ == '__main__':
    imp_parser = ImpParser()
    tree = imp_parser.parse_file(sys.argv[1])
    print(str(tree) + '\n')
    try:
        #print(tree.pretty())
        gc = ImpToGC().transform(tree)
        print(str(gc) + '\n')
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
        #print('imp attribute error')
        #print(tree)
    # vc_parser = Lark.open('vc.lark', parser='earley', lexer='standard')
    # try:
    #     print(vc_parser.parse(vc_nested).pretty())
    # except AttributeError:
    #     print('vc attribute error')

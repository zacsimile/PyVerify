import sys
from lark import Lark, Transformer, Tree
from lark.lexer import Token


class ImpParser:
    def __init__(self):
        """
        Lark parser, activate!
        """
        self.imp_parser = Lark.open('imp.lark', parser='lalr', lexer='standard')

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
            raise ValueError("File must be .imp.")

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
        if type(b) == list:
            return Tree('not', b)

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
        if b.data == 'or':
            return Tree('and', self._not(b.children))
        if b.data == 'and':
            return Tree('or', self._not(b.children))
        if b.data == 'not':
            return b.children
        else:
            return Tree('not', b.children)

    def block(self, b):
        return b

    def program(self, p):
        if len(p) > 2 and p[2].data == 'post':
            return [p[0].value, p[1], p[3:], p[2]]
        else:
            return [p[0].value, p[1:]]

    def assign(self, a):
        self.tmpcount += 1
        varstring = 'tmp_' + str(self.tmpcount)
        return [Tree('assume', Tree('eq', [Token('NAME', varstring), a[0]])), Tree('havoc', a[0]),
                Tree('assume', Tree('eq', [a[0], Tree('replace', [a[1], Token('NAME', varstring), a[0]])]))]

    def write(self, a):
        self.tmpcount += 1
        varstring = 'tmp_' + str(self.tmpcount)
        return [Tree('assume', Tree('eq', [Token('NAME', varstring), a[0]])), Tree('havoc', a[0]),
                Tree('assume', Tree('eq', [a[0], Tree('write', ['tmp_' + str(self.tmpcount), a[1], a[2]])]))]

    def inv(self, i):
        return i

    def parassign(self, p):
        return [self.assign([p[0], p[2]]), self.assign([p[1], p[3]])]

    def ifstmt(self, b):
        if len(b) == 2:
            return [Tree('assume', b[0]), b[1]]
        if len(b) == 3:
            return Tree('choice', [Tree('assume', b[0]), b[1]], [Tree('assume', self._not(b[0])), b[2]])

    def neg(self, n):
        return Tree('sub', [Token('NUMBER', 0), n])

    def whilestmt(self, w):
        out = []
        inv = []
        # Assert/assume invariant
        if type(w) == list:
            for c in w:
                if type(c) == Tree:
                    if c.data == 'inv':
                        inv.append(c.children)
        else:
            if w.data == 'inv':
                inv.append(w.children)
        if len(inv) > 0:
            out.append(Tree('assert', inv))
        # Havoc variables
        if type(w) == list:
            for c in w:
                if type(c) == Tree:
                    if c.data == 'havoc':
                        out.append(c)
        else:
            if w.data == 'havoc':
                out.append(w)
        if len(inv) > 0:
            out.append(Tree('assume', inv))
            out.append(Tree('choice', [[Tree('assume', w[0]), w[1], Tree('assert', inv), Tree('assume', 'false')], Tree('assume', self._not(w[0]))]))
        else:
            out.append(Tree('choice', [[Tree('assume', w[0]), w[1], Tree('assume', 'false')], Tree('assume', self._not(w[0]))]))
        return out

if __name__ == '__main__':
    parser = ImpParser()
    tree = parser.parse_file(sys.argv[1])
    try:
        print(ImpToGC().transform(tree))
    except AttributeError:
        print(tree)

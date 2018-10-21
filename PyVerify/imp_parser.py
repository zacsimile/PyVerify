import sys
from lark import Lark, Transformer, Tree
from lark.lexer import Token


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

    # def _not(self, b):
    #     if type(b) == list:
    #         out = []
    #         for t in b:
    #             out.append(self._not(t))
    #         return out
    #
    #     if b.data == 'eq':
    #         return Tree('neq', b.children)
    #     if b.data == 'neq':
    #         return Tree('eq', b.children)
    #     if b.data == 'geq':
    #         return Tree('lt', b.children)
    #     if b.data == 'lt':
    #         return Tree('geq', b.children)
    #     if b.data == 'leq':
    #         return Tree('gt', b.children)
    #     if b.data == 'gt':
    #         return Tree('leq', b.children)
    #     if b.data == 'or':
    #         return Tree('and', self._not(b.children))
    #     if b.data == 'and':
    #         return Tree('or', self._not(b.children))
    #     if b.data == 'not':
    #         return b.children
    #     else:
    #         return Tree('not', b.children)
    #
    # def block(self, b):
    #     return b
    #
    # def program(self, p):
    #     if len(p) > 2 and p[2].data == 'assert':
    #         return [p[0].value, p[1], p[3:], p[2]]
    #     else:
    #         return [p[0].value, p[1:]]
    #
    # def assign(self, a):
    #     self.tmpcount += 1
    #     varstring = 'tmp_' + str(self.tmpcount)
    #     return [Tree('assume', Tree('eq', [Token('NAME', varstring), a[0]])), Tree('havoc', a[0]),
    #             Tree('assume', Tree('eq', [a[0], Tree('replace', [a[1], Token('NAME', varstring), a[0]])]))]
    #
    # def write(self, a):
    #     self.tmpcount += 1
    #     varstring = 'tmp_' + str(self.tmpcount)
    #     return [Tree('assume', Tree('eq', [Token('NAME', varstring), a[0]])), Tree('havoc', a[0]),
    #             Tree('assume', Tree('eq', [a[0], Tree('write', ['tmp_' + str(self.tmpcount), a[1], a[2]])]))]
    #
    # def pre(self, p):
    #     return Tree('assume', p)
    #
    # def post(self, p):
    #     return Tree('assert', p)
    #
    # def parassign(self, p):
    #     return [self.assign([p[0], p[2]]), self.assign([p[1], p[3]])]
    #
    # def ifstmt(self, b):
    #     if len(b) == 2:
    #         return [Tree('assume', b[0]), b[1]]
    #     if len(b) == 3:
    #         return Tree('choice', [Tree('assume', b[0]), b[1]], [Tree('assume', self._not(b[0])), b[2]])
    #
    # def neg(self, n):
    #     return Tree('sub', [Token('NUMBER', 0), n])
    #
    # def find_tree_data(self, data, l):
    #     out = []
    #     if type(l) == list:
    #         for c in l:
    #             if type(c) == Tree:
    #                 if c.data == data:
    #                     out.append(c.children)
    #     if type(l) == Tree:
    #         if c.data == data:
    #             out.append(c.children)
    #     return out
    #
    # def construct_invariant(self, l):
    #     inv = self.find_tree_data('inv', l)
    #     if len(inv) > 0:
    #         i_and = []
    #         for i in inv:
    #             i_and.append(i)
    #         if len(i_and) > 1:
    #             return Tree('and', i_and)
    #         else:
    #             return i_and
    #     else:
    #         return []

    def program(self, p):
        print('---program')
        print(p)
        print(type(p))
        print('----program')

    def lt(self, p):
        print('---lt')
        print(p)
        print(type(p))
        print('---lt')

    def neg(self, p):
        print('---neg')
        print(p)
        print(type(p))
        print('---neg')

    def whilestmt(self, w):
        print('---while')
        print(w)
        print(type(w))
        print('---endwhile')
        # out = []
        # # Assert/assume invariant
        # inv = self.construct_invariant(w)
        # out.append(Tree('assert', inv))
        # # Havoc variables
        # havoc = self.find_tree_data('havoc', w)
        # for h in havoc:
        #     out.append(Tree('havoc', h))
        # if type(inv) == Tree:
        #     out.append(Tree('assume', inv))
        #     out.append(Tree('choice', [[Tree('assume', w[0]), w[1], Tree('assert', inv), Tree('assume', 'false')], Tree('assume', self._not(w[0]))]))
        # else:
        #     out.append(Tree('choice', [[Tree('assume', w[0]), w[1], Tree('assume', 'false')], Tree('assume', self._not(w[0]))]))
        # return out

if __name__ == '__main__':
    parser = ImpParser()
    tree = parser.parse_file(sys.argv[1])
    try:
        print(tree)
        #ImpToGC().transform(tree)
    except AttributeError:
        print('yes')
        #print(tree)

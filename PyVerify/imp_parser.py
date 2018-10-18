import sys
from lark import Lark


class ImpParser:
    def __init__(self):
        """
        This is a top-down parser for IMP, built in the style of http://effbot.org/zone/simple-top-down-parsing.htm.
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
        print(self.imp_parser.parse(prog))

if __name__ == '__main__':
    parser = ImpParser()
    parser.parse_file(sys.argv[1])
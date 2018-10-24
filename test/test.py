import unittest
import os

from PyVerify.imp_parser import unit_parse

class TestBenchmarks(unittest.TestCase):

    def test_valid(self):
        path = os.path.join(os.path.dirname(__file__), '../Benchmarks/valid/')
        for file in os.listdir(path):
            with self.subTest(file=file):
                if file.endswith(".imp"):
                    assert unit_parse(os.path.join(path, file)) == 0

if __name__ == '__main__':
    unittest.main()

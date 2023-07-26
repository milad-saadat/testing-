import unittest
from src.UnknownVariable import UnknownVariable


class MyTestCase(unittest.TestCase):
    def test_converting_to_string(self):
        a = UnknownVariable('testing')
        self.assertEqual('testing', str(a))


if __name__ == '__main__':
    unittest.main()

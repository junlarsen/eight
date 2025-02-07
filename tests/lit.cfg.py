import lit.formats
import os

config.name = "Eight"
config.test_format = lit.formats.ShTest()

config.suffixes = ['.eight']
config.test_source_root = os.path.dirname(__file__)

config.substitutions.append(('%eightc', os.path.join(os.getcwd(), 'target', 'debug', 'eightc')))

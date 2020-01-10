## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests

try:
    import sage.env
except ImportError:
    raise ValueError("this package requires SageMath")


# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t --force-lib sage_sample")
        if errno != 0:
            sys.exit(1)

setup(
    name = "fos",
    version = "0.1",
    description='Package for various operations on first order linear differential and difference systems',
    long_description = readfile("README.md"),
    long_description_content_type="text/markdown",
    url='https://www.mjaroschek.com/fos/',
    author = "Maximilian Jaroschek",
    author_email = "maximilian@mjaroschek.com",
    license = "GPLv2+",
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 3 - Alpha',
      'Intended Audience :: Science/Research',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)',
      'Programming Language :: Python :: 3.7',
    ],
    packages = [
        "fos",
    ],
    package_dir = {'': 'src/'},
    include_dirs = sage.env.sage_include_directories(),
    cmdclass = {'test': SageTest},
    )

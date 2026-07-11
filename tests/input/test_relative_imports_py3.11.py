# Python 3.11 relative-import regression test (PEP 328).
from . import sibling
from ..package import member
from ...package.submodule import item

import pglast
from pglast import parser, parse_sql, Missing
from pglast.visitors import Visitor
from top_level_analyzer import TopLevelAnalyzer
from common import find_involved_tables
from full_analyzer import FullAnalyzer, FullContext
from pglast.stream import RawStream


def rotate_safe_table_to_leftmost(node: pglast.ast.JoinExpr, table_name: str):
    
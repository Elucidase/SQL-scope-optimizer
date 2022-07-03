
import json
from pglast.stream import RawStream
from common import TOP
from full_analyzer import FullAnalyzer
from branch_builder import BranchBuilder
from instantiator import Instantiator

def main(sql, schema):
    # analyze incoming sql
    full_analyzer=FullAnalyzer(sql, schema)
    context=full_analyzer()
    root = context.table_node[TOP] 
    branch_builder = BranchBuilder(root, context)
    id_to_branch = branch_builder.build()
    instantiator = Instantiator(id_to_branch, context)
    return id_to_branch, instantiator.instantiate()

if __name__ == "__main__":
    # try 1633, 1699, 1364, 1212
    problemNo = 1212
    schema_file=f"schema/{problemNo}.json"
    with open(schema_file) as file:
        schema = json.load(file)
    with open(f"sql/{problemNo}.sql") as file:
        sql = file.read()
    id_to_branch, instbranches = main(sql, schema)
    for id, branches in id_to_branch.items():
        print(id)
        for branch in branches:
            print(RawStream()(branch.root))
            print(
                f"children ({branch.children_type}):", branch.children, 
                "free:", branch.free,
                "links:", branch.translation_payload.links, 
                "value_map:", branch.translation_payload.value_map
            )
    print("instantiated results:")
    for instbranch in instbranches:
        print(RawStream()(instbranch.root))

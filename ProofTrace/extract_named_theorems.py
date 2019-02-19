import os
import re

walk_dir = os.path.abspath(".")

FILENAME_REGEXP = re.compile('\\.[hm]l$')
PROVE_1_REGEXP = re.compile('(let|and)\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*' +
                            '=\\s*(' +
                            'prove|' +
                            'prove_by_refinement|' +
                            'new_definition|' +
                            'new_basic_definition|' +
                            'new_axiom|define|' +
                            'new_infix_definition|' +
                            'INT_OF_REAL_THM|' +
                            'define_finite_type|' +
                            'TAUT|' +
                            'INT_ARITH|' +
                            'new_recursive_definition'
                            ')')
PROVE_2_REGEXP = re.compile('(let|and)\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*,\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*' +
                            '=\\s*(' +
                            'define_type|' +
                            '\\(CONJ_PAIR o prove\\)' +
                            ')')
PROVE_3_REGEXP = re.compile('(let|and)\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*,\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*,\\s*' +
                            '([a-zA-Z0-9_-]+)\\s*' +
                            '=\\s*(' +
                            'new_inductive_definition' +
                            ')')

for root, subdirs, files in os.walk(walk_dir):
    for filename in files:
        if re.search(FILENAME_REGEXP, filename):
            file_path = os.path.join(root, filename)
            with open(file_path, 'rb') as f:
                content = f.read()

                matches_1 = re.findall(PROVE_1_REGEXP, str(content))
                for m in matches_1:
                    if m[1] != "_":
                        print("{}".format(m[1]))

                matches_2 = re.findall(PROVE_2_REGEXP, str(content))
                for m in matches_2:
                    if m[1] != "_":
                        print("{}".format(m[1]))
                    if m[2] != "_":
                        print("{}".format(m[2]))

                matches_3 = re.findall(PROVE_3_REGEXP, str(content))
                for m in matches_3:
                    if m[1] != "_":
                        print("{}".format(m[1]))
                    if m[2] != "_":
                        print("{}".format(m[2]))
                    if m[3] != "_":
                        print("{}".format(m[2]))

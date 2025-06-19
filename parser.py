import xml.etree.ElementTree as ET
from collections import defaultdict
import re

def extract_atoms(root):
    """Extract atoms."""
    atoms = set()
    for sig in root.findall(".//sig[@label='this/Atom']"):
        for atom in sig.findall("atom"):
            atoms.add(atom.attrib["label"])
    return atoms

def extract_field_tuples(field_label):
    """Extract field tuples."""
    result = []
    for field in root.findall(f".//field[@label='{field_label}']"):
        for tuple_elem in field.findall("tuple"):
            result.append([atom.attrib["label"] for atom in tuple_elem.findall("atom")])
    return result


def parse_formula(root_label, vars_map, quant_map, child_map, left_map, right_map):
    """Recursively convert formula tree into FOL."""
    if root_label.startswith("Atom"):
        relation = atom_relation_map[root_label]
        var0 = vars_map[root_label][0]
        var1 = vars_map[root_label][1]
        return f"{relation}({var0}, {var1})"
    elif root_label.startswith("Not"):
        child = child_map[root_label]
        return f"¬({parse_formula(child, vars_map, quant_map, child_map, left_map, right_map)})"
    elif root_label.startswith("Forall") or root_label.startswith("Exists"):
        quantifier = "∀" if root_label.startswith("Forall") else "∃"
        var = quant_map[root_label]
        body = quant_body_map[root_label]
        return f"{quantifier}{var}.({parse_formula(body, vars_map, quant_map, child_map, left_map, right_map)})"
    elif (
        root_label.startswith("Implies")
        or root_label.startswith("And")
        or root_label.startswith("Or")
    ):
        left = left_map[root_label]
        right = right_map[root_label]
        op = (
            "→"
            if root_label.startswith("Implies")
            else ("∧" if root_label.startswith("And") else "∨")
        )
        return f"({parse_formula(left, vars_map, quant_map, child_map, left_map, right_map)} {op} {parse_formula(right, vars_map, quant_map, child_map, left_map, right_map)})"
    else:
        return root_label


def clean_formula(formula: str) -> str:
    # Replace variable names with letters.
    var_map = {}
    var_counter = 0

    def replace_var(match):
        nonlocal var_counter
        orig = match.group()
        if orig not in var_map:
            var_map[orig] = chr(ord("x") + var_counter)
            var_counter += 1
        return var_map[orig]

    formula = re.sub(r"V\d+\$\d+", replace_var, formula)

    # Simplify relation names by removing relation IDs (e.g., E$0 → E).
    formula = re.sub(r"E\$\d+", "E", formula)

    # Simplify quantifiers like "∀x." or "∃y."
    formula = re.sub(r"\((∀|∃)([a-z])\.\(", r"\1\2.(", formula)

    return formula


# Load and parse the XML.
tree = ET.parse("folgoal2.xml")
root = tree.getroot()

# Load useful mappings.
atom_vars_raw = extract_field_tuples("vars")
atom_relation_raw = extract_field_tuples("relation")
quant_bound_raw = extract_field_tuples("bound_var")
quant_body_raw = extract_field_tuples("body")
child_raw = extract_field_tuples("child")
left_raw = extract_field_tuples("left")
right_raw = extract_field_tuples("right")
separator_root_raw = extract_field_tuples("root")

# Build maps.
atom_relation_map = {a: r for a, r in atom_relation_raw}
vars_map = defaultdict(lambda: ["_", "_"])
for a, idx, var in atom_vars_raw:
    vars_map[a][int(idx)] = var

quant_bound_map = {q: v for q, v in quant_bound_raw}
quant_body_map = {q: f for q, f in quant_body_raw}
child_map = {p: c for p, c in child_raw}
left_map = {p: l for p, l in left_raw}
right_map = {p: r for p, r in right_raw}

# Get formula root.
separator_root = separator_root_raw[0][1]

# Convert tree to FOL.
fol_formula = parse_formula(
    separator_root, vars_map, quant_bound_map, child_map, left_map, right_map
)

# Pretty-print FOL.
pretty = clean_formula(fol_formula)
print(pretty)

import subprocess
import re
import statistics
from tqdm import tqdm

NUM_RUNS = 30
BASE_CMD = [
    "lake",
    "env",
    "lean",
    "-Dtrace.profiler=true",
]
FILES = [
    "Palamedes/Examples/Simple/Eq2.lean",
    "Palamedes/Examples/Simple/Eq2'.lean",
    "Palamedes/Examples/Simple/Eq2Or5.lean",
    "Palamedes/Examples/Simple/Eq2Or5'.lean",
    "Palamedes/Examples/Simple/ThreePlusOne.lean",
    "Palamedes/Examples/Range/Between5And10.lean",
    "Palamedes/Examples/Range/BetweenLoAndHi.lean",
    "Palamedes/Examples/Range/Gt5.lean",
    "Palamedes/Examples/Range/ZeroOrInRange.lean",
    "Palamedes/Examples/Arbitrary.lean",
    "Palamedes/Examples/List/AllTwos/AllTwos.lean",
    "Palamedes/Examples/List/AllTwosEvenLen/AllTwosEvenLen.lean",
    "Palamedes/Examples/List/EvenLen/EvenLen.lean",
    "Palamedes/Examples/List/IncreasingByOne/IncreasingByOne.lean",
    "Palamedes/Examples/List/LengthK/LengthK.lean",
    "Palamedes/Examples/List/LengthKAllTwos/LengthKAllTwos.lean",
    "Palamedes/Examples/List/SortedBetween/SortedBetween.lean",
    "Palamedes/Examples/List/True/True.lean",
    "Palamedes/Examples/List/AllTwos/Fold.lean",
    "Palamedes/Examples/List/AllEvens/Fold.lean",
    "Palamedes/Examples/List/AllTwosEvenLen/Fold.lean",
    "Palamedes/Examples/List/EvenLen/Fold.lean",
    "Palamedes/Examples/List/IncreasingByOne/Fold.lean",
    "Palamedes/Examples/List/LengthK/Fold.lean",
    "Palamedes/Examples/List/LengthKAllTwos/Fold.lean",
    "Palamedes/Examples/List/SortedBetween/Fold.lean",
    "Palamedes/Examples/List/True/Fold.lean",
    "Palamedes/Examples/List/EvenLen/Fold.lean",
    "Palamedes/Examples/List/EvenLen/EvenLen.lean",
    "Palamedes/Examples/Tree/AllTwos/AllTwos.lean",
    "Palamedes/Examples/List/AllEvens/AllEvens.lean",
    "Palamedes/Examples/Tree/AVL/AVL.lean",
    "Palamedes/Examples/Tree/BST/BST.lean",
    "Palamedes/Examples/Tree/RBT/RBT.lean",
    "Palamedes/Examples/Tree/CompleteTree/CompleteTree.lean",
    "Palamedes/Examples/Tree/IncreasingByOne/IncreasingByOne.lean",
    "Palamedes/Examples/Tree/Nonempty/Nonempty.lean",
    "Palamedes/Examples/Tree/AllTwos/Fold.lean",
    "Palamedes/Examples/Tree/AVL/Fold.lean",
    "Palamedes/Examples/Tree/BST/Fold.lean",
    "Palamedes/Examples/Tree/RBT/Fold.lean",
    "Palamedes/Examples/Tree/CompleteTree/Fold.lean",
    "Palamedes/Examples/Tree/IncreasingByOne/Fold.lean",
    "Palamedes/Examples/Tree/Nonempty/Fold.lean",
    "Palamedes/Examples/Stack/GoodStack.lean",
    "Palamedes/Examples/Stack/Fold.lean",
    "Palamedes/Examples/STLC/WellScoped/WellScoped.lean",
    "Palamedes/Examples/STLC/WellTyped/WellTyped.lean",
    "Palamedes/Examples/STLC/WellTyped/Fold.lean",
    "Palamedes/Examples/STLC/WellScoped/Fold.lean",
    "Palamedes/Examples/Tree/MaxDepth/MaxDepth.lean",
    "Palamedes/Examples/Tree/MaxDepth/Fold.lean",
]

# Regular expression to match the desired output
pattern = re.compile(r'\[palamedes\.trace\] \[(\d+(?:\.\d+)?)\] ⟪(.+)⟫⟪(.+)⟫')

# Dictionary to store extracted numbers by string
data = dict()

# Run the external script multiple times
iter = tqdm(FILES * NUM_RUNS, dynamic_ncols=True)
for file in iter:
    iter.set_description(file)
    try:
        result = subprocess.run(BASE_CMD + [file],
                                capture_output=True,
                                text=True,
                                check=True)
        output = result.stdout
        matches = pattern.findall(output)
        for (numRepr, typ, pred) in matches:
            label = (typ, pred)
            if label in data:
                data[label]["times"].append(float(numRepr))
            else:
                total = True
                with open(file, "r") as f:
                    if any(
                            map(lambda line: line.find("allow_partial") != -1,
                                f.readlines())):
                        total = False
                data[label] = {"times": [float(numRepr)], "total": total}
    except subprocess.CalledProcessError as e:
        print(f"\nError running script: {e} \n")

label_pattern = re.compile(r"fun (.+) => (.+)")

total_lines = []
partial_lines = []

# Compute and print mean and standard deviation
for label, numbers in [item for item in data.items()]:
    mean = statistics.mean(numbers["times"])
    stdev = statistics.stdev(numbers["times"])
    total = numbers["total"]

    (typ, pred) = label

    pred = pred.replace("∃", "`$\\exists$`")
    pred = pred.replace("∨", "`$\\lor$`")
    pred = pred.replace("∧", "`$\\land$`")
    pred = pred.replace("Γ", "`$\\Gamma$`")
    pred = pred.replace("τ", "`$\\tau$`")
    pred = pred.replace("≤", "<=")

    typ = typ.replace("ℕ", "Nat")

    pred = pred.replace("TARGET", "`\\textbf{v}`")

    line = ("\\mintinline[mathescape=true,escapeinside=``]{text}|" + pred +
            "| & \\mintinline[mathescape=true,escapeinside=``]{text}|" + typ +
            "| & " + f"${mean:.2f}$ & (${stdev:.2f}$) \\\\")

    if total:
        total_lines.append(line)
    else:
        partial_lines.append(line)

with open("final-data.txt", "w") as f:
    for line in total_lines:
        f.write(line + "\n")
    f.write("\\hline\n")
    for line in partial_lines:
        f.write(line + "\n")

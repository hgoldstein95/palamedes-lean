import sys

for line in sys.stdin.readlines():
    line = line.replace("∃", "`$\\exists$`")
    line = line.replace("∨", "`$\\lor$`")
    line = line.replace("∧", "`$\\land$`")
    line = line.replace("Γ", "`$\\Gamma$`")
    line = line.replace("τ", "`$\\tau$`")
    line = line.replace("≤", "<=")
    line = line.replace("→", "->")
    line = line.replace("α", "`$\\alpha$`")
    line = line.replace("β", "`$\\beta$`")
    line = line.replace("₁", "1")
    line = line.replace("₂", "2")
    print(line, end="")

#!/bin/bash

echo "Running Palamedes kick-the-tires..."
cd Palamedes
python scripts/profile.py --ktt
cat palamedes-data.csv
rm palamedes-data.csv
rm palamedes-latex-chart.txt
cd ..

echo ""
echo "Running Cobb kick-the-tires..."
bash cobb_ktt.sh

echo ""
echo "Running QuickChick kick-the-tires..."
~/.opam/5.3.0/bin/coqc QC/QC.v

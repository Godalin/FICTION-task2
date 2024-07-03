#!/usr/bin/env python3

import os
import re
import sys
import subprocess

def parse_coq_file(file_path):
    with open(file_path, 'r') as file:
        content = file.read()

    # Find all exercises
    exercises = re.findall(r'\(\*\* \*\*\*\* Exercise: (\d+) stars,.*?\*\)\s*(.*?)\(\*\* \[\] \*\)', content, re.DOTALL)

    return exercises

def calculate_score(exercises):
    total_score = 0
    for stars, body in exercises:
        stars = int(stars)
        # Check if the exercise contains 'magic' or 'Admitted'
        if re.search(r'magic|Admitted', body):
            print(f"Exercise worth {stars} stars is not completed.")
        else:
            total_score += stars
            print(f"Exercise worth {stars} stars is completed.")
    return total_score

def main():
    if len(sys.argv) != 2:
        print("Usage: check_scores.py <file_path>")
        sys.exit(1)

    file_path = sys.argv[1]

    # Run Coq type checker
    try:
        subprocess.run(["coqc", file_path], check=True)
    except subprocess.CalledProcessError:
        print(f"Error: {file_path} did not pass the Coq type checker.")
        sys.exit(1)

    exercises = parse_coq_file(file_path)
    score = calculate_score(exercises)
    print(f"Total Score: {score}")

    # Clean up temporary Coq files
    base_name = os.path.splitext(file_path)[0]
    temp_files = ([base_name + ext for ext in ['.vo', '.glob', '.vok', '.vos']]
        + ["." + base_name + ext for ext in ['.aux']])
    for temp_file in temp_files:
        # print(temp_file)
        if os.path.exists(temp_file):
            os.remove(temp_file)

if __name__ == '__main__':
    main()

import argparse
import sys

from .error import ParsingError
from .thy_lexer import lexer
from .thy_parser import parse


# Increase the recursion limit if needed

def main():
    # Set up argument parser
    arg_parser = argparse.ArgumentParser(description="Parse input using PLY")
    arg_parser.add_argument(
            'input',
            type=str,
            help="Input file or string to parse")
    arg_parser.add_argument(
            '-f', '--file',
            action='store_true',
            help="Interpret input as a filename")

    # Parse arguments
    args = arg_parser.parse_args()

    # Read input
    if args.file:
        try:
            with open(args.input, 'r') as file:
                data = file.read()
        except FileNotFoundError:
            print(f"File '{args.input}' not found.")
            return
    else:
        data = args.input  # Treat as direct input

    # Lex and parse
    try:
        lexer.input(data)
        result = parse(data)
    except ParsingError as e:
        print("Parsing failed due to errors.")
        print(f"Error: {e.with_source_code(data)}")
        sys.exit(1)

    # Print result
    if result:
        print("Parsing successful.")
        print("Parsed structure:", result)
    else:
        print("Parsing failed due to errors.")


if __name__ == "__main__":
    main()

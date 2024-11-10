class ParsingError(Exception):
    def __init__(self, message, line=None, column=None, token=" "):
        self.message = message
        self.line = line
        self.column = column
        self.token = token
        self.source_code = None
        super().__init__(self.__str__())

    def with_source_code(self, source_code):
        self.source_code = source_code
        return self

    def _source_hint(self):
        if self.source_code and self.line is not None and self.column is not None:
            lines = self.source_code.split("\n")
            if (self.line >= 0 and self.line <= len(lines) and self.column >= 0):
                line = lines[self.line]
                print(line)
                underline = " " * (self.column - 1) + "^" * len(self.token)
                return f"\n\n{line}\n{underline}\n"
        return "source_hint"

    def __str__(self):
        location_info = ""
        if self.line is not None and self.column is not None:
            location_info = f" at line {self.line}, column {self.column}"
        elif self.line is not None:
            location_info = f" at line {self.line}"
        elif self.column is not None:
            location_info = f" at column {self.column}"
        source_hint = self._source_hint()
        return f"{self.message}{location_info}{source_hint}"

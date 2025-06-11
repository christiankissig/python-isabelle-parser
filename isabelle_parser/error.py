class ParsingError(Exception):
    source_code: str | None = None

    def __init__(
        self,
        message: str,
        line: int | None = None,
        column: int | None = None,
        token: str = " ",
    ) -> None:
        self.message = message
        self.line = line
        self.column = column
        self.token = token
        super().__init__(self.__str__())

    def with_source_code(self, source_code: str) -> "ParsingError":
        self.source_code = source_code
        return self

    def _source_hint(self) -> str:
        if self.source_code and self.line is not None and self.column is not None:
            lines = self.source_code.split("\n")
            if self.line >= 0 and self.line <= len(lines) and self.column >= 0:
                line = lines[self.line]
                print(line)
                underline = " " * (self.column - 1) + "^" * len(self.token)
                return f"\n\n{line}\n{underline}\n"
        return "source_hint"

    def __str__(self) -> str:
        location_info = ""
        if self.line is not None and self.column is not None:
            location_info = f" at line {self.line}, column {self.column}"
        elif self.line is not None:
            location_info = f" at line {self.line}"
        elif self.column is not None:
            location_info = f" at column {self.column}"
        source_hint = self._source_hint()
        return f"{self.message}{location_info}{source_hint}"

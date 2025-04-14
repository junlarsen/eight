class Diagnostic<string Format, int AC> {
  string Message = Format;
  int ArgumentCount = AC;
}

def IncompletePipeSymbol
    : Diagnostic<"Could not find secondary '|' symbol. A single '|' is "
                 "insufficient to form a token.", 0>;

def UnrecognizedCharacter : Diagnostic<"Found unrecognized character {0}", 0>;

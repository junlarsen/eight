class Diagnostic<string Format> { string Message = Format; }

def IncompletePipeSymbol
    : Diagnostic<"Could not find secondary '|' symbol. A single '|' is "
                 "insufficient to form a token.">;

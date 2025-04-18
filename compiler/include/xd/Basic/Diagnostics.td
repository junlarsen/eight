class DiagnosticArgType<string CxxType, string InputType> {
  string cxxType = CxxType;
  string inputType = InputType;
}

def CharacterArg : DiagnosticArgType<"char", "char">;
def StringArg : DiagnosticArgType<"std::string", "std::string_view">;
def IntegerArg : DiagnosticArgType<"int32_t", "int32_t">;

class DiagnosticArg<string Name, DiagnosticArgType Type> {
  string name = Name;
  DiagnosticArgType type = Type;
}

class Diagnostic<string Format, list<DiagnosticArg> Arguments> {
  string format = Format;
  list<DiagnosticArg> arguments = Arguments;
}

def IncompletePipeSymbol
    : Diagnostic<"Could not find secondary '|' symbol. A single '|' is "
                 "insufficient to form a token.",
                 []>;

def UnrecognizedCharacter
    : Diagnostic<"Found unrecognized character {0}",
                 [DiagnosticArg<"Character", CharacterArg>]>;

def UnexpectedToken : Diagnostic<"encountered unexpected token {0}",
                                 [DiagnosticArg<"Token", StringArg>]>;

def ExpectedFunctionParameter
    : Diagnostic<"expected function parameter, but received {0}",
                 [DiagnosticArg<"Token", StringArg>]>;

def ExpectedFunctionTypeParameter
    : Diagnostic<"expected function type parameter, but received {0}",
                 [DiagnosticArg<"Token", StringArg>]>;

def ExpectedCallExpressionArgument
    : Diagnostic<"expected function call argument, but received {0}",
                 [DiagnosticArg<"Token", StringArg>]>;

def ExpectedConstructionExprMember
    : Diagnostic<"expected construction member, but received {0}",
                 [DiagnosticArg<"Token", StringArg>]>;

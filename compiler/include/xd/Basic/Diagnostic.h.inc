//===----- Diagnostic.h.inc ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file does not declare a namespace or a header guard because it's
// included in-place by the Diagnostic TableGen emitter.
//
//===----------------------------------------------------------------------===//

class Diagnostic {
  DiagnosticKind Kind;
  SourceLocation Loc;

public:
  /// Create a Diagnostic without location information. Note that the location
  /// info will have to be attached later in order to become printable.
  explicit Diagnostic(DiagnosticKind Kind)
      : Kind(Kind), Loc(SourceLocation(0, 0)) {}
  explicit Diagnostic(DiagnosticKind Kind, SourceLocation Loc)
      : Kind(Kind), Loc(Loc) {}

  auto setLocation(SourceLocation Loc) -> void { this->Loc = Loc; }
  auto getLocation() const -> SourceLocation { return Loc; }
  auto getKind() const -> DiagnosticKind { return Kind; }
  static bool classof(const Diagnostic *Diag) {
    return Diag->getKind() >= FirstDiagnosticKind &&
           Diag->getKind() <= LastDiagnosticKind;
  }
};

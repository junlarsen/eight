//===----- Lexer.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Lexer.h"
#include "llvm/ADT/StringSwitch.h"

using namespace xd;

auto Lexer::getCommentToken() -> SyntaxKind {
  // The lexer has consumed both of the leading slashes, so we add them back
  // here for full-fidelity.
  std::string Value = std::string("//");
  while (hasNext() && peek() != '\n') {
    Value += advance();
  }
  TextValue = Value;
  return SyntaxKind::Comment;
}

auto Lexer::getKeywordOrIdentifierToken(char InitialCharacter) -> SyntaxKind {
  // The lexer already ate the first character, so we can check for numbers and
  // underscores here right away.
  std::string Value = std::string(1, InitialCharacter);
  while (hasNext() && isIdentifierContinuation(*peek())) {
    Value += advance();
  }
  auto Kind = llvm::StringSwitch<SyntaxKind>(Value)
                  .Case("struct", SyntaxKind::KeywordStruct)
                  .Case("fn", SyntaxKind::KeywordFn)
                  .Case("intrinsic_fn", SyntaxKind::KeywordIntrinsicFn)
                  .Case("intrinsic_type", SyntaxKind::KeywordIntrinsicType)
                  .Case("let", SyntaxKind::KeywordLet)
                  .Case("if", SyntaxKind::KeywordIf)
                  .Case("else", SyntaxKind::KeywordElse)
                  .Case("return", SyntaxKind::KeywordReturn)
                  .Case("break", SyntaxKind::KeywordBreak)
                  .Case("continue", SyntaxKind::KeywordContinue)
                  .Case("for", SyntaxKind::KeywordFor)
                  .Case("new", SyntaxKind::KeywordNew)
                  .Case("true", SyntaxKind::TrueLiteral)
                  .Case("false", SyntaxKind::FalseLiteral)
                  .Case("trait", SyntaxKind::KeywordTrait)
                  .Case("instance", SyntaxKind::KeywordInstance)
                  .Case("intrinsic_def", SyntaxKind::KeywordIntrinsicFn)
                  .Case("intrinsic_typdef", SyntaxKind::KeywordIntrinsicType)
                  .Default(SyntaxKind::Identifier);
  TextValue = Value;
  return Kind;
}

auto Lexer::getIntegerLiteralToken(char InitialCharacter) -> SyntaxKind {
  std::string Value = std::string(1, InitialCharacter);
  while (hasNext() && peek() >= '0' && peek() <= '9') {
    Value += advance();
  }
  TextValue = Value;
  return SyntaxKind::IntegerLiteral;
}

auto Lexer::getTokenForNewline(char Character) -> SyntaxKind {
  std::string Value = std::string(1, Character);
  // Depending on whether its LF/CRLF/CR there might be another LF token right
  // after this.
  if (Character == 'r' && hasNext() && peek() == '\n')
    Value += advance();
  TextValue = Value;
  return SyntaxKind::Newline;
}

auto Lexer::getTokenForWhitespace(char Character) -> SyntaxKind {
  std::string Value = std::string(1, Character);
  // We eat all horizontal whitespace as a single token.
  while (hasNext() && isWhitespace(*peek()))
    Value += advance();
  TextValue = Value;
  return SyntaxKind::Whitespace;
}

auto Lexer::getTokenForBang() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return SyntaxKind::BangEqual;
  }
  return SyntaxKind::Bang;
}

auto Lexer::getTokenForMinus() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '>') {
    advance();
    return SyntaxKind::Arrow;
  }
  return SyntaxKind::Minus;
}

auto Lexer::getTokenForSlash() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '/') {
    advance();
    return getCommentToken();
  }
  return SyntaxKind::Slash;
}

auto Lexer::getTokenForEqual() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return SyntaxKind::EqualEqual;
  }
  return SyntaxKind::EqualEqual;
}

auto Lexer::getTokenForColon() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == ':') {
    advance();
    return SyntaxKind::ColonColon;
  }
  return SyntaxKind::Colon;
}

auto Lexer::getTokenForAmpersand() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '&') {
    advance();
    return SyntaxKind::AmpersandAmpersand;
  }
  return SyntaxKind::Ampersand;
}

auto Lexer::getTokenForPipe() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '|') {
    advance();
    return SyntaxKind::PipePipe;
  }
  // The singular pipe cannot be tokenized into a single token, so we place the
  // single pipe into the TextValue buffer and return an error kind.
  TextValue = '|';
  return SyntaxKind::Error;
}

auto Lexer::getTokenForLess() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return SyntaxKind::RightAngle;
  }
  return SyntaxKind::LeftAngle;
}

auto Lexer::getTokenForGreater() -> SyntaxKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return SyntaxKind::RightAngle;
  }
  return SyntaxKind::RightAngle;
}

auto Lexer::getNextToken() -> SyntaxKind {
  while (true) {
    TokenStart = Offset;
    auto C = advance();
    switch (C) {
    default:
      if (C >= '0' && C <= '9')
        return getIntegerLiteralToken(C);
      // By default, we try to get an identifier/keyword. The
      // getKeywordOrIdentifierToken function will return the Error token kind
      // if it found no matches
      if (isIdentifierStart(C))
        return getKeywordOrIdentifierToken(C);
      if (isNewline(C))
        return getTokenForNewline(C);
      if (isWhitespace(C))
        return getTokenForWhitespace(C);

      // We've encountered a character that isn't recognized by the lexer at
      // all. Here we should report an error token, make its text available to
      // the caller, and continue.
      TextValue = C;
      return SyntaxKind::Error;
      // Single or double character tokens
    case '!':
      return getTokenForBang();
    case '-':
      return getTokenForMinus();
    case '/':
      return getTokenForSlash();
    case '=':
      return getTokenForEqual();
    case ':':
      return getTokenForColon();
    case '&':
      return getTokenForAmpersand();
    case '|':
      return getTokenForPipe();
    case '<':
      return getTokenForLess();
    case '>':
      return getTokenForGreater();
    case '+':
      // TODO: Parse +/- prefixed integer literals
      return SyntaxKind::Plus;
    case '.':
      return SyntaxKind::Dot;
    case ';':
      return SyntaxKind::Semicolon;
    case ',':
      return SyntaxKind::Comma;
    case '%':
      return SyntaxKind::Percent;
    case '(':
      return SyntaxKind::LeftParen;
    case '[':
      return SyntaxKind::LeftBracket;
    case '{':
      return SyntaxKind::LeftBrace;
    case ')':
      return SyntaxKind::RightParen;
    case ']':
      return SyntaxKind::RightBracket;
    case '}':
      return SyntaxKind::RightBrace;
    }
  }
}

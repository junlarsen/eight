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

static auto getLiteralToken(SyntaxKind SK, llvm::StringRef S) -> GreenToken {
  return GreenToken(SK, S);
}

auto Lexer::getCommentToken() -> GreenToken {
  // The lexer has consumed both of the leading slashes, so we add them back
  // here for full-fidelity.
  auto Value = llvm::SmallString<8>("//");
  while (hasNext() && peek() != '\n') {
    Value += advance();
  }
  return GreenToken(SyntaxKind::Comment, Value);
}

auto Lexer::getKeywordOrIdentifierToken(char InitialCharacter) -> GreenToken {
  // The lexer already ate the first character, so we can check for numbers and
  // underscores here right away.
  llvm::SmallString<8> Keyword;
  Keyword += InitialCharacter;
  while (hasNext() && isIdentifierContinuation(*peek())) {
    Keyword += advance();
  }
  auto Kind = llvm::StringSwitch<SyntaxKind>(Keyword)
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
                  .Case("import", SyntaxKind::KeywordImport)
                  .Case("package", SyntaxKind::KeywordPackage)
                  .Default(SyntaxKind::Identifier);
  return GreenToken(Kind, Keyword);
}

auto Lexer::getIntegerLiteralToken(char InitialCharacter) -> GreenToken {
  llvm::SmallString<8> Value;
  Value += InitialCharacter;
  while (hasNext() && peek() >= '0' && peek() <= '9') {
    Value += advance();
  }
  return GreenToken(SyntaxKind::IntegerLiteral, Value);
}

auto Lexer::getTokenForNewline(char Character) -> GreenToken {
  llvm::SmallString<8> Value;
  Value += Character;
  // Depending on whether its LF/CRLF/CR there might be another LF token right
  // after this.
  if (Character == 'r' && hasNext() && peek() == '\n')
    Value += advance();
  return GreenToken(SyntaxKind::Newline, Value);
}

auto Lexer::getTokenForWhitespace(char Character) -> GreenToken {
  llvm::SmallString<8> Value;
  Value += Character;
  // We eat all horizontal whitespace as a single token.
  while (hasNext() && isWhitespace(*peek()))
    Value += advance();
  return GreenToken(SyntaxKind::Whitespace, Value);
}

auto Lexer::getTokenForBang() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return getLiteralToken(SyntaxKind::BangEqual, "!=");
  }
  return getLiteralToken(SyntaxKind::Bang, "!");
}

auto Lexer::getTokenForMinus() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '>') {
    advance();
    return getLiteralToken(SyntaxKind::Arrow, "->");
  }
  return getLiteralToken(SyntaxKind::Minus, "-");
}

auto Lexer::getTokenForSlash() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '/') {
    advance();
    return getCommentToken();
  }
  return getLiteralToken(SyntaxKind::Slash, "/");
}

auto Lexer::getTokenForEqual() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return getLiteralToken(SyntaxKind::EqualEqual, "==");
  }
  return getLiteralToken(SyntaxKind::Equal, "=");
}

auto Lexer::getTokenForColon() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == ':') {
    advance();
    return getLiteralToken(SyntaxKind::ColonColon, "::");
  }
  return getLiteralToken(SyntaxKind::Colon, ":");
}

auto Lexer::getTokenForAmpersand() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '&') {
    advance();
    return getLiteralToken(SyntaxKind::AmpersandAmpersand, "&&");
  }
  return getLiteralToken(SyntaxKind::Ampersand, "&");
}

auto Lexer::getTokenForPipe() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '|') {
    advance();
    return getLiteralToken(SyntaxKind::PipePipe, "||");
  }
  // The singular pipe cannot be tokenized into a single token, so we place the
  // single pipe into the TextValue buffer and return an error kind.
  return getLiteralToken(SyntaxKind::Error, "|");
}

auto Lexer::getTokenForLess() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return getLiteralToken(SyntaxKind::LeftAngleEqual, "<=");
  }
  return getLiteralToken(SyntaxKind::LeftAngle, "<");
}

auto Lexer::getTokenForGreater() -> GreenToken {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return getLiteralToken(SyntaxKind::RightAngleEqual, ">=");
  }
  return getLiteralToken(SyntaxKind::RightAngle, ">");
}

auto Lexer::getNextToken() -> GreenToken {
  while (true) {
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
      return getLiteralToken(SyntaxKind::Error, &C);
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
      return getLiteralToken(SyntaxKind::Plus, "+");
    case '*':
      return getLiteralToken(SyntaxKind::Star, "*");
    case '.':
      return getLiteralToken(SyntaxKind::Dot, ".");
    case ';':
      return getLiteralToken(SyntaxKind::Semicolon, ";");
    case ',':
      return getLiteralToken(SyntaxKind::Comma, ",");
    case '%':
      return getLiteralToken(SyntaxKind::Percent, "%");
    case '(':
      return getLiteralToken(SyntaxKind::LeftParen, "(");
    case '[':
      return getLiteralToken(SyntaxKind::LeftBracket, "[");
    case '{':
      return getLiteralToken(SyntaxKind::LeftBrace, "{");
    case ')':
      return getLiteralToken(SyntaxKind::RightParen, ")");
    case ']':
      return getLiteralToken(SyntaxKind::RightBracket, "]");
    case '}':
      return getLiteralToken(SyntaxKind::RightBrace, "]");
    }
  }
}

auto Lexer::drain() -> std::vector<GreenToken> {
  std::vector<GreenToken> Tokens;
  while (hasNext()) {
    auto Tok = getNextToken();
    Tokens.push_back(Tok);
  }
  return Tokens;
}

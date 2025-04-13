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

auto Lexer::getCommentToken() -> TokenKind {
  // The lexer has consumed both of the leading slashes.
  std::string Value = std::string();
  while (hasNext() && peek() != '\n') {
    Value += advance();
  }
  Identifier = Value;
  return TokenKind::Comment;
}

auto Lexer::getKeywordOrIdentifierToken(char InitialCharacter) -> TokenKind {
  // The lexer already ate the first character, so we can check for numbers and
  // underscores here right away.
  std::string Value = std::string(1, InitialCharacter);
  while (hasNext() && (isalnum(*peek()) || *peek() == '_')) {
    Value += advance();
  }
  auto Kind = llvm::StringSwitch<TokenKind>(Value)
                  .Case("struct", TokenKind::KeywordStruct)
                  .Case("fn", TokenKind::KeywordFn)
                  .Case("intrinsic_fn", TokenKind::KeywordIntrinsicFn)
                  .Case("intrinsic_type", TokenKind::KeywordIntrinsicType)
                  .Case("let", TokenKind::KeywordLet)
                  .Case("if", TokenKind::KeywordIf)
                  .Case("else", TokenKind::KeywordElse)
                  .Case("return", TokenKind::KeywordReturn)
                  .Case("break", TokenKind::KeywordBreak)
                  .Case("continue", TokenKind::KeywordContinue)
                  .Case("for", TokenKind::KeywordFor)
                  .Case("new", TokenKind::KeywordNew)
                  .Case("true", TokenKind::TrueLiteral)
                  .Case("false", TokenKind::FalseLiteral)
                  .Case("trait", TokenKind::KeywordTrait)
                  .Case("instance", TokenKind::KeywordInstance)
                  .Case("intrinsic_def", TokenKind::KeywordIntrinsicFn)
                  .Case("intrinsic_typdef", TokenKind::KeywordIntrinsicType)
                  .Default(TokenKind::Identifier);
  // We have special cases for identifiers and literal values that also update
  // internal lexer state.
  if (Kind == TokenKind::Identifier)
    Identifier = Value;
  if (Kind == TokenKind::TrueLiteral)
    IntVal = llvm::APInt(32, 1);
  if (Kind == TokenKind::FalseLiteral)
    IntVal = llvm::APInt(32, 0);
  return Kind;
}

auto Lexer::getIntegerLiteralToken(char InitialCharacter) -> TokenKind {
  std::string Value = std::string(1, InitialCharacter);
  while (hasNext() && peek() >= '0' && peek() <= '9') {
    Value += advance();
  }
  IntVal = llvm::APInt(32, Value, 10);
  return TokenKind::IntegerLiteral;
}

auto Lexer::getTokenForBang() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return TokenKind::BangEqual;
  }
  return TokenKind::Bang;
}

auto Lexer::getTokenForMinus() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '>') {
    advance();
    return TokenKind::Arrow;
  }
  return TokenKind::Minus;
}

auto Lexer::getTokenForSlash() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '/') {
    advance();
    return getCommentToken();
  }
  return TokenKind::Slash;
}

auto Lexer::getTokenForEqual() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return TokenKind::EqualEqual;
  }
  return TokenKind::EqualEqual;
}

auto Lexer::getTokenForColon() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == ':') {
    advance();
    return TokenKind::ColonColon;
  }
  return TokenKind::Colon;
}

auto Lexer::getTokenForAmpersand() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '&') {
    advance();
    return TokenKind::LogicalAnd;
  }
  return TokenKind::Ampersand;
}

auto Lexer::getTokenForPipe() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '|') {
    advance();
    return TokenKind::LogicalOr;
  }
  // TODO: Report diagnostic here
  return TokenKind::Error;
}

auto Lexer::getTokenForLess() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return TokenKind::RightAngle;
  }
  return TokenKind::LeftAngle;
}

auto Lexer::getTokenForGreater() -> TokenKind {
  auto Ahead = peek();
  if (Ahead == '=') {
    advance();
    return TokenKind::RightAngle;
  }
  return TokenKind::RightAngle;
}

auto Lexer::getNextToken() -> TokenKind {
  while (true) {
    TokenStart = Offset;
    auto Character = advance();
    switch (Character) {
    default:
      if (Character >= '0' && Character <= '9')
        return getIntegerLiteralToken(Character);
      // By default, we try to get an identifier/keyword. The
      // getKeywordOrIdentifierToken function will return the Error token kind
      // if it found no matches
      return getKeywordOrIdentifierToken(Character);
      // Whitespace is ignored
    case ' ':
    case '\t':
    case '\r':
    case '\n':
      continue;
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
      return TokenKind::Plus;
    case '.':
      return TokenKind::Dot;
    case ';':
      return TokenKind::Semicolon;
    case ',':
      return TokenKind::Comma;
    case '%':
      return TokenKind::Percent;
    case '(':
      return TokenKind::LeftParen;
    case '[':
      return TokenKind::LeftBracket;
    case '{':
      return TokenKind::LeftBrace;
    case ')':
      return TokenKind::RightParen;
    case ']':
      return TokenKind::RightBracket;
    case '}':
      return TokenKind::RightBrace;
    case 0:
      // This StringRef comes from an llvm::MemoryBuffer which is guaranteed to
      // be zero-padded. It should be fair to assume this is the end of the
      // file.
      return TokenKind::EndOfFile;
    }
  }
}

//===----- LexerTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Lexer.h"
#include "llvm/Support/MemoryBuffer.h"
#include <gtest/gtest.h>

using namespace llvm;
using namespace xd;

TEST(LexerTest, BufferNavigation) {
  auto Buf = MemoryBuffer::getMemBuffer("ab");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_TRUE(Lex.hasNext());
  EXPECT_EQ(Lex.advance(), 'a');
  EXPECT_TRUE(Lex.hasNext());
  EXPECT_EQ(Lex.peek(), 'b');
  EXPECT_EQ(Lex.advance(), 'b');
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIntegerLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("123");
  auto Lex = Lexer(Buf->getBufferStart());
  SyntaxKind TK = Lex.getNextToken();
  EXPECT_EQ(TK, SyntaxKind::IntegerLiteral);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(0, 3));
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseCommentLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("// this is a comment\nidentifier");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Comment);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(0, 20));
  EXPECT_EQ(Lex.getTextValue(), "// this is a comment");

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Newline);
  EXPECT_EQ(Lex.getTextValue(), "\n");
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(20, 21));

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Identifier);
  EXPECT_EQ(Lex.getTextValue(), "identifier");
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(21, 31));
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIdentifier) {
  auto Buf = MemoryBuffer::getMemBuffer("abc a1_cd");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Identifier);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(0, 3));
  EXPECT_EQ(Lex.getTextValue(), "abc");

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Whitespace);
  EXPECT_EQ(Lex.getTextValue(), " ");
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(3, 4));

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Identifier);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(4, 9));
  EXPECT_EQ(Lex.getTextValue(), "a1_cd");
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseSingularOperators) {
  auto Buf = MemoryBuffer::getMemBuffer("+.;,");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Plus);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Dot);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Semicolon);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Comma);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseUnfinishedPipe) {
  auto Buf = MemoryBuffer::getMemBuffer("|");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Error);
}

TEST(LexerTest, ParseDecisionTokens) {
  auto Buf = MemoryBuffer::getMemBuffer("!!=:::");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Bang);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::BangEqual);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::ColonColon);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Colon);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseWhitespaceSensitive) {
  auto Buf = MemoryBuffer::getMemBuffer("- > ->");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Minus);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Whitespace);

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::RightAngle);
  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Whitespace);

  EXPECT_EQ(Lex.getNextToken(), SyntaxKind::Arrow);
  EXPECT_FALSE(Lex.hasNext());
}

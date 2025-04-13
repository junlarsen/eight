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
  EXPECT_EQ('a', Lex.advance());
  EXPECT_TRUE(Lex.hasNext());
  EXPECT_EQ('b', Lex.peek());
  EXPECT_EQ('b', Lex.advance());
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIntegerLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("123");
  auto Lex = Lexer(Buf->getBufferStart());
  TokenKind TK = Lex.getNextToken();
  EXPECT_EQ(TK, TokenKind::IntegerLiteral);
  ASSERT_EQ(Lex.getSourceLocation(), SourceLocation(0, 3));
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseCommentLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("// this is a comment\nidentifier");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Comment);
  ASSERT_EQ(Lex.getSourceLocation(), SourceLocation(0, 20));
  EXPECT_EQ(" this is a comment", Lex.getIdentifier());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Identifier);
  EXPECT_EQ("identifier", Lex.getIdentifier());
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIdentifier) {
  auto Buf = MemoryBuffer::getMemBuffer("abc a1_cd");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Identifier);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(0, 3));
  EXPECT_EQ("abc", Lex.getIdentifier());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Identifier);
  EXPECT_EQ(Lex.getSourceLocation(), SourceLocation(4, 9));
  EXPECT_EQ("a1_cd", Lex.getIdentifier());
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseSingularOperators) {
  auto Buf = MemoryBuffer::getMemBuffer("+.;,");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Plus);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Dot);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Semicolon);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Comma);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseUnfinishedPipe) {
  auto Buf = MemoryBuffer::getMemBuffer("|");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Error);
}

TEST(LexerTest, ParseDecisionTokens) {
  auto Buf = MemoryBuffer::getMemBuffer("! != :: :");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Bang);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::BangEqual);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::ColonColon);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Colon);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseWhitespaceSensitive) {
  auto Buf = MemoryBuffer::getMemBuffer("- > ->");
  auto Lex = Lexer(Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Minus);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::RightAngle);
  EXPECT_EQ(Lex.getNextToken(), TokenKind::Arrow);
  EXPECT_FALSE(Lex.hasNext());
}

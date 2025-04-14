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
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("ab");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  EXPECT_TRUE(Lex.hasNext());
  EXPECT_EQ(Lex.advance(), 'a');
  EXPECT_TRUE(Lex.hasNext());
  EXPECT_EQ(Lex.peek(), 'b');
  EXPECT_EQ(Lex.advance(), 'b');
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIntegerLiteral) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("123");
  auto Lex = Lexer(DM, Buf->getBufferStart());

  EXPECT_EQ(Lex.getByteOffset(), 0);
  auto TK = Lex.getNextToken();
  EXPECT_EQ(TK.getKind(), SyntaxKind::IntegerLiteral);
  EXPECT_EQ(TK.getText(), "123");
  EXPECT_EQ(Lex.getByteOffset(), 3);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseCommentLiteral) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("// this is a comment\nidentifier");
  auto Lex = Lexer(DM, Buf->getBufferStart());

  EXPECT_EQ(Lex.getByteOffset(), 0);
  auto TK1 = Lex.getNextToken();
  EXPECT_EQ(TK1.getKind(), SyntaxKind::Comment);
  EXPECT_EQ(TK1.getText(), "// this is a comment");
  EXPECT_EQ(Lex.getByteOffset(), 20);

  EXPECT_EQ(Lex.getByteOffset(), 20);
  auto TK2 = Lex.getNextToken();
  EXPECT_EQ(TK2.getKind(), SyntaxKind::Newline);
  EXPECT_EQ(TK2.getText(), "\n");
  EXPECT_EQ(Lex.getByteOffset(), 21);

  EXPECT_EQ(Lex.getByteOffset(), 21);
  auto TK3 = Lex.getNextToken();
  EXPECT_EQ(TK3.getKind(), SyntaxKind::Identifier);
  EXPECT_EQ(TK3.getText(), "identifier");
  EXPECT_EQ(Lex.getByteOffset(), 31);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIdentifier) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("abc a1_cd");
  auto Lex = Lexer(DM, Buf->getBufferStart());

  EXPECT_EQ(Lex.getByteOffset(), 0);
  auto TK1 = Lex.getNextToken();
  EXPECT_EQ(TK1.getKind(), SyntaxKind::Identifier);
  EXPECT_EQ(TK1.getText(), "abc");
  EXPECT_EQ(Lex.getByteOffset(), 3);

  EXPECT_EQ(Lex.getByteOffset(), 3);
  auto TK2 = Lex.getNextToken();
  EXPECT_EQ(TK2.getKind(), SyntaxKind::Whitespace);
  EXPECT_EQ(TK2.getText(), " ");
  EXPECT_EQ(Lex.getByteOffset(), 4);

  EXPECT_EQ(Lex.getByteOffset(), 4);
  auto TK3 = Lex.getNextToken();
  EXPECT_EQ(TK3.getKind(), SyntaxKind::Identifier);
  EXPECT_EQ(TK3.getText(), "a1_cd");
  EXPECT_EQ(Lex.getByteOffset(), 9);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseSingularOperators) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("+.;,");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Plus);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Dot);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Semicolon);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Comma);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseUnfinishedPipe) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("|");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Error);
  EXPECT_FALSE(DM.isEmpty());
}

TEST(LexerTest, ParseDecisionTokens) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("!!=:::");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Bang);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::BangEqual);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::ColonColon);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Colon);
  EXPECT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseWhitespaceSensitive) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("- > ->");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Minus);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Whitespace);

  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::RightAngle);
  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Whitespace);

  EXPECT_EQ(Lex.getNextToken().getKind(), SyntaxKind::Arrow);
  EXPECT_FALSE(Lex.hasNext());
}

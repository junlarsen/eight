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
  ASSERT_TRUE(Lex.hasNext());
  ASSERT_EQ(Lex.advance(), 'a');
  ASSERT_TRUE(Lex.hasNext());
  ASSERT_EQ(Lex.peek(), 'b');
  ASSERT_EQ(Lex.advance(), 'b');
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIntegerLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("123");
  auto Lex = Lexer(Buf->getBufferStart());

  ASSERT_EQ(Lex.getByteOffset(), 0);
  auto TK = Lex.getNextToken();
  ASSERT_EQ(TK.getSyntaxKind(), SyntaxKind::IntegerLiteral);
  ASSERT_EQ(TK.getText(), "123");
  ASSERT_EQ(Lex.getByteOffset(), 3);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseCommentLiteral) {
  auto Buf = MemoryBuffer::getMemBuffer("// this is a comment\nidentifier");
  auto Lex = Lexer(Buf->getBufferStart());

  ASSERT_EQ(Lex.getByteOffset(), 0);
  auto TK1 = Lex.getNextToken();
  ASSERT_EQ(TK1.getSyntaxKind(), SyntaxKind::Comment);
  ASSERT_EQ(TK1.getText(), "// this is a comment");
  ASSERT_EQ(Lex.getByteOffset(), 20);

  ASSERT_EQ(Lex.getByteOffset(), 20);
  auto TK2 = Lex.getNextToken();
  ASSERT_EQ(TK2.getSyntaxKind(), SyntaxKind::Newline);
  ASSERT_EQ(TK2.getText(), "\n");
  ASSERT_EQ(Lex.getByteOffset(), 21);

  ASSERT_EQ(Lex.getByteOffset(), 21);
  auto TK3 = Lex.getNextToken();
  ASSERT_EQ(TK3.getSyntaxKind(), SyntaxKind::Identifier);
  ASSERT_EQ(TK3.getText(), "identifier");
  ASSERT_EQ(Lex.getByteOffset(), 31);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseIdentifier) {
  auto Buf = MemoryBuffer::getMemBuffer("abc a1_cd");
  auto Lex = Lexer(Buf->getBufferStart());

  ASSERT_EQ(Lex.getByteOffset(), 0);
  auto TK1 = Lex.getNextToken();
  ASSERT_EQ(TK1.getSyntaxKind(), SyntaxKind::Identifier);
  ASSERT_EQ(TK1.getText(), "abc");
  ASSERT_EQ(Lex.getByteOffset(), 3);

  ASSERT_EQ(Lex.getByteOffset(), 3);
  auto TK2 = Lex.getNextToken();
  ASSERT_EQ(TK2.getSyntaxKind(), SyntaxKind::Whitespace);
  ASSERT_EQ(TK2.getText(), " ");
  ASSERT_EQ(Lex.getByteOffset(), 4);

  ASSERT_EQ(Lex.getByteOffset(), 4);
  auto TK3 = Lex.getNextToken();
  ASSERT_EQ(TK3.getSyntaxKind(), SyntaxKind::Identifier);
  ASSERT_EQ(TK3.getText(), "a1_cd");
  ASSERT_EQ(Lex.getByteOffset(), 9);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseSingularOperators) {
  auto Buf = MemoryBuffer::getMemBuffer("+.;,");
  auto Lex = Lexer(Buf->getBufferStart());
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Plus);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Dot);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Semicolon);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Comma);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseUnfinishedPipe) {
  auto Buf = MemoryBuffer::getMemBuffer("|");
  auto Lex = Lexer(Buf->getBufferStart());
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Error);
}

TEST(LexerTest, ParseDecisionTokens) {
  auto Buf = MemoryBuffer::getMemBuffer("!!=:::");
  auto Lex = Lexer(Buf->getBufferStart());
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Bang);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::BangEqual);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::ColonColon);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Colon);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, ParseWhitespaceSensitive) {
  auto Buf = MemoryBuffer::getMemBuffer("- > ->");
  auto Lex = Lexer(Buf->getBufferStart());
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Minus);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Whitespace);

  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::RightAngle);
  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Whitespace);

  ASSERT_EQ(Lex.getNextToken().getSyntaxKind(), SyntaxKind::Arrow);
  ASSERT_FALSE(Lex.hasNext());
}

TEST(LexerTest, DrainAllTokens) {
  auto Buf = MemoryBuffer::getMemBuffer("abc |a1_cd");
  auto Lex = Lexer(Buf->getBufferStart());
  auto Tokens = Lex.drain();
  // Two identifiers, one whitespace, one error
  ASSERT_EQ(Tokens.size(), 4);
}

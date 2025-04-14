//===----- ParserTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Parser.h"
#include <gtest/gtest.h>

#include <llvm/Support/MemoryBuffer.h>

using namespace llvm;
using namespace xd;

TEST(ParserTest, Navigation) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("hello world");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  auto P = Parser(Lex);

  EXPECT_TRUE(P.hasNext());
  P.advance();
  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  auto TK1 = P.get();
  EXPECT_EQ(TK1.getText(), "hello");
  EXPECT_TRUE(P.hasNext());

  P.advance();
  EXPECT_TRUE(P.at(SyntaxKind::Whitespace));
  EXPECT_TRUE(P.hasNext());
  auto TKFut = P.lookahead();
  EXPECT_EQ(TKFut.getKind(), SyntaxKind::Identifier);
  EXPECT_EQ(TKFut.getText(), "world");

  P.advance();
  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  EXPECT_FALSE(P.hasNext());
  auto TKEof = P.lookahead();
  EXPECT_EQ(TKEof.getKind(), SyntaxKind::Eof);
}

TEST(ParserTest, ConditionalEat) {
  auto DM = DiagnosticManager();
  auto Buf = MemoryBuffer::getMemBuffer("hello 123");
  auto Lex = Lexer(DM, Buf->getBufferStart());
  auto P = Parser(Lex);
  P.advance();

  EXPECT_TRUE(P.eat(SyntaxKind::Identifier));
  EXPECT_FALSE(P.eat(SyntaxKind::Identifier));
  EXPECT_TRUE(P.hasNext());
  EXPECT_TRUE(P.eat(SyntaxKind::Whitespace));

  // TODO: write tests for expect once errors are recordable
}

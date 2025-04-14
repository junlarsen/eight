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
  auto Buf = MemoryBuffer::getMemBuffer("hello world");
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(std::move(Lex.drain()));

  EXPECT_TRUE(P.hasNext());
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
  EXPECT_TRUE(P.hasNext());
  P.advance();
  auto TKEof = P.lookahead();
  EXPECT_EQ(TKEof.getKind(), SyntaxKind::Eof);
}

TEST(ParserTest, ConditionalEat) {
  auto Buf = MemoryBuffer::getMemBuffer("hello 123");
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(std::move(Lex.drain()));

  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  // Eating whitespace should not work, we need to eat identifier
  EXPECT_FALSE(P.eat(SyntaxKind::Whitespace));
  EXPECT_TRUE(P.eat(SyntaxKind::Identifier));
  // We are now at the whitespace
  EXPECT_TRUE(P.at(SyntaxKind::Whitespace));
  EXPECT_EQ(P.lookahead().getKind(), SyntaxKind::IntegerLiteral);
  P.advance();
  EXPECT_TRUE(P.eat(SyntaxKind::IntegerLiteral));
  EXPECT_FALSE(P.hasNext());
}

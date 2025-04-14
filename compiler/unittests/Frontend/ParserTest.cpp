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
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  EXPECT_TRUE(P.hasNext());
  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  auto TK1 = P.get();
  EXPECT_EQ(TK1, SyntaxKind::Identifier);
  EXPECT_TRUE(P.hasNext());

  P.advance();
  EXPECT_TRUE(P.at(SyntaxKind::Whitespace));
  EXPECT_TRUE(P.hasNext());
  auto TKFut = P.lookahead();
  EXPECT_EQ(TKFut, SyntaxKind::Identifier);

  P.advance();
  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  EXPECT_TRUE(P.hasNext());
  P.advance();
  auto TKEof = P.lookahead();
  EXPECT_EQ(TKEof, SyntaxKind::Eof);
}

TEST(ParserTest, ConditionalEat) {
  auto Buf = MemoryBuffer::getMemBuffer("hello 123");
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  EXPECT_TRUE(P.at(SyntaxKind::Identifier));
  // Eating whitespace should not work, we need to eat identifier
  EXPECT_FALSE(P.eat(SyntaxKind::Whitespace));
  EXPECT_TRUE(P.eat(SyntaxKind::Identifier));
  // We are now at the whitespace
  EXPECT_TRUE(P.at(SyntaxKind::Whitespace));
  EXPECT_EQ(P.lookahead(), SyntaxKind::IntegerLiteral);
  P.advance();
  EXPECT_TRUE(P.eat(SyntaxKind::IntegerLiteral));
  EXPECT_FALSE(P.hasNext());
}

//===----- ParserTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Parser.h"
#include "llvm/Support/MemoryBuffer.h"
#include <gtest/gtest.h>

using namespace llvm;
using namespace xd;

TEST(ParserTest, Navigation) {
  auto Buf = MemoryBuffer::getMemBuffer("hello world");
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  ASSERT_TRUE(P.hasNext());
  ASSERT_TRUE(P.at(SyntaxKind::Identifier));
  ASSERT_TRUE(P.hasNext());

  P.advance();
  ASSERT_TRUE(P.at(SyntaxKind::Identifier));
  ASSERT_FALSE(P.hasNext());
  auto TKEof = P.lookahead();
  ASSERT_EQ(TKEof, SyntaxKind::Eof);
}

TEST(ParserTest, ConditionalEat) {
  auto Buf = MemoryBuffer::getMemBuffer("hello 123");
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  ASSERT_TRUE(P.at(SyntaxKind::Identifier));
  ASSERT_EQ(P.lookahead(), SyntaxKind::IntegerLiteral);
  ASSERT_TRUE(P.eat(SyntaxKind::Identifier));
  ASSERT_TRUE(P.eat(SyntaxKind::IntegerLiteral));
  ASSERT_FALSE(P.hasNext());
  ASSERT_FALSE(P.eat(SyntaxKind::Comment));
}

TEST(ParserTest, TreeBuilder) {
  auto Buf = MemoryBuffer::getMemBuffer("fn foo(a: int)");
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  auto TU = P.open();
  P.expect(SyntaxKind::KeywordFn);
  P.expect(SyntaxKind::Identifier);
  P.expect(SyntaxKind::LeftParen);
  auto C1 = P.open();
  P.expect(SyntaxKind::Identifier);
  P.expect(SyntaxKind::Colon);
  P.expect(SyntaxKind::Identifier);
  P.close(C1, SyntaxKind::FunctionParameterList);
  P.close(TU, SyntaxKind::TranslationUnit);

  Tree T = P.build();
  ASSERT_TRUE(P.getDebugTreeBuilderComplete());
}

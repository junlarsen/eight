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

  ASSERT_FALSE(P.eof());
  ASSERT_TRUE(P.at(SyntaxKind::Identifier));
  ASSERT_FALSE(P.eof());

  P.advance();
  ASSERT_TRUE(P.at(SyntaxKind::Identifier));
  P.advance();
  ASSERT_TRUE(P.eof());
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
  ASSERT_TRUE(P.eof());
  ASSERT_FALSE(P.eat(SyntaxKind::Comment));
}

TEST(ParserTest, TreeBuilder) {
  auto Buf = MemoryBuffer::getMemBuffer("fn foo(a: int) -> { foo }");
  auto DM = DiagnosticManager();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(DM, std::move(Lex.drain()));

  auto TU = P.open();
  auto FN = P.open();
  ASSERT_TRUE(P.eat(SyntaxKind::KeywordFn));
  ASSERT_TRUE(P.eat(SyntaxKind::Identifier));
  auto C1 = P.open();
  ASSERT_TRUE(P.eat(SyntaxKind::LeftParen));
  ASSERT_TRUE(P.eat(SyntaxKind::Identifier));
  ASSERT_TRUE(P.eat(SyntaxKind::Colon));
  ASSERT_TRUE(P.eat(SyntaxKind::Identifier));
  ASSERT_TRUE(P.eat(SyntaxKind::RightParen));
  P.close(C1, SyntaxKind::FunctionParameterList);
  ASSERT_TRUE(P.eat(SyntaxKind::Arrow));
  auto Block = P.open();
  ASSERT_TRUE(P.eat(SyntaxKind::LeftBrace));
  ASSERT_TRUE(P.eat(SyntaxKind::Identifier));
  ASSERT_TRUE(P.eat(SyntaxKind::RightBrace));
  P.close(Block, SyntaxKind::FunctionBody);
  P.close(FN, SyntaxKind::Function);
  P.close(TU, SyntaxKind::TranslationUnit);

  GreenNode T = P.build();
  ASSERT_TRUE(P.getDebugTreeBuilderComplete());
  ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::TranslationUnit);
  ASSERT_EQ(T.getTextLength(), 25);
}

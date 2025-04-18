//===----- ParserTest.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/Parser.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
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

struct Context {
  std::unique_ptr<MemoryBuffer> Buf;
  std::unique_ptr<DiagnosticManager> DM;
  Lexer L;
  Parser P;
};

static auto getParser(const StringRef Input) -> std::unique_ptr<Context> {
  auto Buf = MemoryBuffer::getMemBuffer(Input);
  auto DM = std::make_unique<DiagnosticManager>();
  auto Lex = Lexer(Buf->getBufferStart());
  auto P = Parser(*DM, std::move(Lex.drain()));
  return std::make_unique<Context>(std::move(Buf), std::move(DM), Lex,
                                   std::move(P));
}

TEST(ParserTest, ParseExpression) {
  // ReferenceExpression
  {
    auto Ctx = getParser("hello");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::ReferenceExpr);
  }
  // IntegerLiteralExpression
  {
    auto Ctx = getParser("7772");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    T.debug(errs());
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::IntegerLiteralExpr);
  }
  // BooleanLiteralExpression
  {
    auto Ctx = getParser("true");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BooleanLiteralExpr);
  }
  {
    auto Ctx = getParser("false");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BooleanLiteralExpr);
  }
  // GroupExpr
  {
    auto Ctx = getParser("(0)");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::GroupExpr);
    ASSERT_TRUE(T.hasChild(SyntaxKind::IntegerLiteralExpr));
  }
  // ConstructionExpr
  {
    auto TrailingComma = getParser("new Foo { a = b, }");
    TrailingComma->P.parseExpr();
    auto T = TrailingComma->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::ConstructionExpr);
  }
  {
    auto NoMembers = getParser("new Foo {}");
    NoMembers->P.parseExpr();
    auto T = NoMembers->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::ConstructionExpr);
  }
  {
    auto MultipleMembers = getParser("new Foo { a = b, d = 28 }");
    MultipleMembers->P.parseExpr();
    auto T = MultipleMembers->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::ConstructionExpr);
  }
}

TEST(ParserTest, ParsePrefixExpression) {
  // Boolean Negation
  {
    auto Ctx = getParser("!a");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::UnaryNotExpr);
  }
  // Integral Negation
  {
    auto Ctx = getParser("-b");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::UnaryMinusExpr);
  }
  // Integral Abs
  {
    auto Ctx = getParser("+a");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::UnaryPlusExpr);
  }
  // Address Of
  {
    auto Ctx = getParser("&a");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::UnaryAddrOfExpr);
  }
  // Dereference
  {
    auto Ctx = getParser("*a");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::UnaryDerefExpr);
  }
}

TEST(ParserTest, ParsePostfixExpression) {
  // Member access
  {
    auto Ctx = getParser("x.y");
    Ctx->P.parseExpr();
    auto T = Ctx->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::ConstantIndexExpr);
  }
  {
    auto NoTypeNoArgs = getParser("x()");
    NoTypeNoArgs->P.parseExpr();
    auto T = NoTypeNoArgs->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::CallExpr);
  }
  {
    auto TypeButNoArgs = getParser("y[]()");
    TypeButNoArgs->P.parseExpr();
    auto T = TypeButNoArgs->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::CallExpr);
  }
  {
    auto Everything = getParser("Foo[A, Y](77777, *a)");
    Everything->P.parseExpr();
    auto T = Everything->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::CallExpr);
  }
  {
    auto Chained = getParser("foo()()");
    Chained->P.parseExpr();
    auto T = Chained->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::CallExpr);
    ASSERT_TRUE(T.hasChild(SyntaxKind::CallExpr));
  }
}

TEST(ParserTest, ParseBinaryExpression) {
  {
    auto Assignment = getParser("a = b");
    Assignment->P.parseExpr();
    auto T = Assignment->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryAssignExpr);
  }
  {
    auto GreaterThan = getParser("a > b");
    GreaterThan->P.parseExpr();
    auto T = GreaterThan->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryGreaterThanExpr);
  }
  {
    auto LessThan = getParser("a < b");
    LessThan->P.parseExpr();
    auto T = LessThan->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryLessThanExpr);
  }
  {
    auto GreaterThanOrEqual = getParser("a >= b");
    GreaterThanOrEqual->P.parseExpr();
    auto T = GreaterThanOrEqual->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryGreaterThanEqualExpr);
  }
  {
    auto LessThanOrEqual = getParser("a <= b");
    LessThanOrEqual->P.parseExpr();
    auto T = LessThanOrEqual->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryLessThanEqualExpr);
  }
  {
    auto EqualEqual = getParser("a == b");
    EqualEqual->P.parseExpr();
    auto T = EqualEqual->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryEqualityExpr);
  }
  {
    auto Inequal = getParser("a != b");
    Inequal->P.parseExpr();
    auto T = Inequal->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryInequalityExpr);
  }
  {
    auto LogicalAnd = getParser("a && b");
    LogicalAnd->P.parseExpr();
    auto T = LogicalAnd->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryLogicalAndExpr);
  }
  {
    auto LogicalOr = getParser("a || b");
    LogicalOr->P.parseExpr();
    auto T = LogicalOr->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryLogicalOrExpr);
  }
  {
    auto Plus = getParser("a + b");
    Plus->P.parseExpr();
    auto T = Plus->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryAddExpr);
  }
  {
    auto Minus = getParser("a - b");
    Minus->P.parseExpr();
    auto T = Minus->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinarySubExpr);
  }
  {
    auto Multiply = getParser("a * b");
    Multiply->P.parseExpr();
    auto T = Multiply->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryMulExpr);
  }
  {
    auto Divide = getParser("a / b");
    Divide->P.parseExpr();
    auto T = Divide->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryDivExpr);
  }
  {
    auto Modulo = getParser("a % b");
    Modulo->P.parseExpr();
    auto T = Modulo->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::BinaryModulusExpr);
  }
}

TEST(ParserTest, ParseFunctionDecl) {
  {
    auto Basic = getParser("fn main() {}");
    Basic->P.parseFunctionDecl();
    auto T = Basic->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Function);
  }
  {
    auto Intrinsic = getParser("intrinsic_fn malloc(size: i32) -> ptr");
    Intrinsic->P.parseFunctionDecl();
    auto T = Intrinsic->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::IntrinsicFunction);
  }
  {
    auto TypeParameters = getParser("fn id[T](x: T) -> T {}");
    TypeParameters->P.parseFunctionDecl();
    auto T = TypeParameters->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Function);
  }
}

TEST(ParserTest, ParseIntrinsicTypeDecl) {
  auto Intrinsic = getParser("intrinsic_type i32;");
  Intrinsic->P.parseIntrinsicTypeDecl();
  auto T = Intrinsic->P.build();
  ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::IntrinsicType);
}

TEST(ParserTest, ParseStructDecl) {
  {
    auto NoMembers = getParser("struct Foo {}");
    NoMembers->P.parseStructDecl();
    auto T = NoMembers->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Struct);
  }
  {
    auto TrailingComma = getParser("struct Foo { a: bool, }");
    TrailingComma->P.parseStructDecl();
    auto T = TrailingComma->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Struct);
  }
  {
    auto ManyMembers = getParser("struct Foo { a: i32, z: Vec2D }");
    ManyMembers->P.parseStructDecl();
    auto T = ManyMembers->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Struct);
  }
}

TEST(ParserTest, ParseTraitDecl) {
  {
    auto NoMembers = getParser("trait Foo[] {}");
    NoMembers->P.parseTraitDecl();
    auto T = NoMembers->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Trait);
  }
  {
    auto RegularFn = getParser("trait Foo[] { fn eat(); }");
    RegularFn->P.parseTraitDecl();
    auto T = RegularFn->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Trait);
  }
  {
    auto IntrinsicFn = getParser("trait Foo[] { intrinsic_fn bar(); }");
    IntrinsicFn->P.parseTraitDecl();
    auto T = IntrinsicFn->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::Trait);
  }
}

TEST(ParserTest, ParseTraitMemberDecl) {
  // This test is here so we can check that intrinsic/regular fn difference is
  // detected by the parser.
  {
    auto Regular = getParser("fn eat[T]();");
    Regular->P.parseTraitFunctionMember();
    auto T = Regular->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::TraitFunctionMember);
  }
  {
    auto Intrinsic = getParser("intrinsic_fn bar[T](a: T);");
    Intrinsic->P.parseTraitFunctionMember();
    auto T = Intrinsic->P.build();
    ASSERT_EQ(T.getSyntaxKind(), SyntaxKind::TraitIntrinsicFunctionMember);
  }
}

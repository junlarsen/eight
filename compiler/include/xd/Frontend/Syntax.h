//===----- Syntax.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Syntax module for representing red/green syntax trees.
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_SYNTAX_H
#define XD_FRONTEND_SYNTAX_H

#include "xd/Basic/DiagnosticManager.h"
#include "xd/Basic/Location.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include <bitset>
#include <cstdint>

namespace xd {
enum class SyntaxKind : uint8_t {
  // Keyword tokens
  KeywordStruct = 0,
  KeywordLet,
  KeywordFn,
  KeywordIntrinsicFn,
  KeywordIntrinsicType,
  KeywordTrait,
  KeywordInstance,
  KeywordIf,
  KeywordElse,
  KeywordReturn,
  KeywordBreak,
  KeywordContinue,
  KeywordFor,
  KeywordNew,
  // Textual tokens
  Identifier,
  IntegerLiteral,
  TrueLiteral,
  FalseLiteral,
  Comment,
  Whitespace,
  Newline,
  // Symbol tokens
  Ampersand,
  Bang,
  Plus,
  Dot,
  Star,
  Minus,
  Slash,
  Equal,
  EqualEqual,
  BangEqual,
  Percent,
  LeftParen,
  LeftBracket,
  LeftBrace,
  LeftAngle,
  LeftAngleEqual,
  RightParen,
  RightBracket,
  RightBrace,
  RightAngle,
  RightAngleEqual,
  Semicolon,
  Colon,
  ColonColon,
  Comma,
  Arrow,
  AmpersandAmpersand,
  PipePipe,

  Error,
  Eof,
  // Nodes
  TranslationUnit,
  IntrinsicFunction,
  Function,
  FunctionTypeParameterList,
  FunctionTypeParameter,
  FunctionParameterList,
  FunctionParameter,
  FunctionReturnType,
  FunctionBody,

  Struct,
  StructMemberList,
  StructMember,

  IntrinsicType,

  Trait,
  TraitTypeParameterList,
  TraitTypeParameter,
  TraitMemberList,
  TraitFunctionMember,

  Instance,
  InstanceTypeArgumentList,
  InstanceMemberList,

  Stmt,
  LetStmt,
  IfStmt,
  IfCondition,
  IfThenBody,
  IfElseBody,
  ForStmt,
  ForInitializer,
  ForCondition,
  ForIncrement,
  ForBody,
  ReturnStmt,
  ContinueStmt,
  BreakStmt,
  ExprStmt,

  Expr,
  IntegerLiteralExpr,
  BooleanLiteralExpr,
  ReferenceExpr,
  GroupExpr,
  ConstantIndexExpr,
  CallExpr,
  CallExprArgumentList,
  CallExprTypeArgumentList,
  UnaryNotExpr,
  UnaryMinusExpr,
  UnaryPlusExpr,
  UnaryDerefExpr,
  UnaryAddrOfExpr,
  BinaryLogicalAndExpr,
  BinaryLogicalOrExpr,
  BinaryAssignExpr,
  BinaryEqualityExpr,
  BinaryInequalityExpr,
  BinaryLessThanExpr,
  BinaryGreaterThanExpr,
  BinaryGreaterThanEqualExpr,
  BinaryLessThanEqualExpr,
  BinaryAddExpr,
  BinarySubExpr,
  BinaryMulExpr,
  BinaryDivExpr,
  BinaryModulusExpr,
  ConstructionExpr,
  ConstructionExprMember,

  Type,
  NamedType,
  PointerType,
};

inline uint64_t operator<<(uint64_t LHS, SyntaxKind RHS) {
  return LHS << static_cast<uint64_t>(RHS);
}

/// A bitset representing the possible tokens the lexer might produce.
///
/// This is fixed to 50 at the moment, because including Error and Eof there are
/// 50 significant members from SyntaxKind that can be put into this bitset.
using TokenSet = std::bitset<50>;

static const TokenSet TSDeclStart =
    1 << SyntaxKind::KeywordFn | 1 << SyntaxKind::KeywordIntrinsicFn |
    1 << SyntaxKind::KeywordIntrinsicType | 1 << SyntaxKind::KeywordStruct |
    1 << SyntaxKind::KeywordTrait | 1 << SyntaxKind::KeywordInstance;
static const TokenSet TSTraitMemberStart = 1 << SyntaxKind::KeywordFn;
static const TokenSet TSInstanceMemberStart =
    1 << SyntaxKind::KeywordFn | 1 << SyntaxKind::KeywordIntrinsicFn;
static const TokenSet TSStatementStart =
    1 << SyntaxKind::KeywordLet | 1 << SyntaxKind::KeywordIf |
    1 << SyntaxKind::KeywordFor | 1 << SyntaxKind::KeywordReturn |
    1 << SyntaxKind::KeywordContinue | 1 << SyntaxKind::KeywordBreak;
static const TokenSet TSPrimaryExpressionStart =
    1 << SyntaxKind::Identifier | 1 << SyntaxKind::IntegerLiteral |
    1 << SyntaxKind::TrueLiteral | 1 << SyntaxKind::FalseLiteral |
    1 << SyntaxKind::LeftParen | 1 << SyntaxKind::KeywordNew;
static const TokenSet TSPrefixOperator =
    1 << SyntaxKind::Plus | 1 << SyntaxKind::Minus | 1 << SyntaxKind::Bang |
    1 << SyntaxKind::Ampersand | 1 << SyntaxKind::Star;
static const TokenSet TSExpressionStart =
    TSPrimaryExpressionStart | TSPrefixOperator;
static const TokenSet TSInfixEqualOperator = 1 << SyntaxKind::Equal;
static const TokenSet TSInfixLogicalOperator =
    1 << SyntaxKind::AmpersandAmpersand | 1 << SyntaxKind::PipePipe;
static const TokenSet TSInfixComparisonOperator =
    1 << SyntaxKind::EqualEqual | 1 << SyntaxKind::BangEqual |
    1 << SyntaxKind::LeftAngleEqual | 1 << SyntaxKind::RightAngleEqual |
    1 << SyntaxKind::LeftAngle | 1 << SyntaxKind::RightAngle;
static const TokenSet TSInfixAdditiveOperator =
    1 << SyntaxKind::Plus | 1 << SyntaxKind::Minus;
static const TokenSet TSInfixMultiplicativeOperator =
    1 << SyntaxKind::Star | 1 << SyntaxKind::Slash | 1 << SyntaxKind::Percent;
static const TokenSet TSInfixOperator =
    TSInfixEqualOperator | TSInfixLogicalOperator | TSInfixComparisonOperator |
    TSInfixAdditiveOperator | TSInfixMultiplicativeOperator;
static const TokenSet TSPostfixOperator = 1 << SyntaxKind::LeftParen |
                                          1 << SyntaxKind::Dot |
                                          1 << SyntaxKind::LeftBracket;
static const TokenSet TSTypeStart =
    1 << SyntaxKind::Identifier | 1 << SyntaxKind::Star;

/// A new declaration is a fair recovery point for practically everything.
static const TokenSet TSDeclRecovery =
    1 << SyntaxKind::KeywordFn | 1 << SyntaxKind::KeywordStruct |
    1 << SyntaxKind::KeywordIntrinsicType | 1 << SyntaxKind::KeywordIntrinsicFn;

/// The parameter list can either recover on the '->' used for the return type,
/// or the '{' used for the body.
static const TokenSet TSFunctionParameterListRecovery =
    TSDeclRecovery |
    TokenSet(1 << SyntaxKind::LeftBrace | 1 << SyntaxKind::Arrow);

/// Recovery token set for function type parameter set
///
/// This parse will also trigger on the '(' used for the function parameter
/// list.
static const TokenSet TSFunctionTypeParameterListRecovery =
    TSFunctionParameterListRecovery | TokenSet(1 << SyntaxKind::LeftParen);

static const TokenSet TSStructMemberListRecovery = TSDeclRecovery;

/// The parameter list of a trait can either recover on a decl keyword, or the
/// opening brace of the member list.
static const TokenSet TSTraitTypeParameterListRecovery =
    TSDeclRecovery | TokenSet(1 << SyntaxKind::LeftBrace);
static const TokenSet TSTraitMemberListRecovery = TSDeclRecovery;

static const TokenSet TSInstanceMemberListRecovery =
    TSDeclRecovery | TokenSet(1 << SyntaxKind::LeftBrace);
/// The type argument list of an instance can either be the body, or the `for`
/// name.
static const TokenSet TSInstanceTypeArgumentListRecovery =
    TSInstanceMemberListRecovery | TokenSet(1 << SyntaxKind::KeywordFor);

/// A block can only assume to recover on a top-level decl again, or a new
/// statement.
static const TokenSet TSBlockRecovery =
    TSDeclRecovery |
    TokenSet(1 << SyntaxKind::KeywordLet | 1 << SyntaxKind::KeywordIf |
             1 << SyntaxKind::KeywordFor | 1 << SyntaxKind::ContinueStmt |
             1 << SyntaxKind::KeywordBreak | 1 << SyntaxKind::KeywordReturn);

/// A call expression's argument may recover at the next statement.
static const TokenSet TSCallExpressionArgumentListRecovery = TSBlockRecovery;
static const TokenSet TSCallExpressionTypeArgumentListRecovery =
    TSBlockRecovery;

/// The same goes for the construction expression.
static const TokenSet TSConstructionExprMemberListRecovery = TSBlockRecovery;

auto getSyntaxKindName(SyntaxKind SK) -> llvm::StringRef;

enum class GreenElementKind {
  Node,
  Token,
  Error,
};

/// Any green tree element value
class GreenElement {
  GreenElementKind Kind;

public:
  virtual ~GreenElement() = default;
  explicit GreenElement(GreenElementKind Kind) : Kind(Kind) {}
  auto getKind() const -> GreenElementKind { return Kind; }
  static bool classof(const GreenElement *E) {
    return E->getKind() >= GreenElementKind::Node &&
           E->getKind() <= GreenElementKind::Error;
  }
  virtual auto getSyntaxKind() const -> SyntaxKind = 0;
  virtual auto getTextLength() const -> size_t = 0;
};

class GreenToken : public GreenElement {
  SyntaxKind SK;
  llvm::SmallString<8> TextValue;

public:
  explicit GreenToken(SyntaxKind SK, const llvm::StringRef &Text)
      : GreenElement(GreenElementKind::Token), SK(SK), TextValue(Text) {}
  auto getText() const -> llvm::StringRef { return TextValue; }
  auto getSyntaxKind() const -> SyntaxKind override { return SK; }
  auto getTextLength() const -> size_t override { return TextValue.size(); }

  auto isTrivia() const -> bool {
    return SK == SyntaxKind::Comment || SK == SyntaxKind::Whitespace ||
           SK == SyntaxKind::Newline;
  }

  static bool classof(const GreenElement *E) {
    return E->getKind() == GreenElementKind::Token;
  }
};

class GreenError : public GreenElement {
  DiagnosticID DiagnosticID;
  uint32_t Length;

public:
  explicit GreenError(uint32_t DiagnosticID, uint32_t Length)
      : GreenElement(GreenElementKind::Error), DiagnosticID(DiagnosticID),
        Length(Length) {}
  auto getDiagnosticID() const -> uint32_t { return DiagnosticID; }
  auto getTextLength() const -> size_t override { return Length; }
  auto getSyntaxKind() const -> SyntaxKind override {
    return SyntaxKind::Error;
  }

  static bool classof(const GreenElement *E) {
    return E->getKind() == GreenElementKind::Error;
  }
};

class GreenNode : public GreenElement {
  SyntaxKind SK;
  std::vector<std::shared_ptr<GreenElement>> Children;
  size_t Length;

public:
  explicit GreenNode(SyntaxKind SK, size_t Length)
      : GreenElement(GreenElementKind::Node), SK(SK), Length(Length) {}

  auto getChildren() -> std::vector<std::shared_ptr<GreenElement>> & {
    return Children;
  }
  auto getSyntaxKind() const -> SyntaxKind override { return SK; };
  auto getTextLength() const -> size_t override { return Length; };
  auto setLength(size_t Length) -> void { this->Length = Length; }
  auto addChild(std::shared_ptr<GreenElement> Child) -> void {
    Children.push_back(Child);
  }
  auto debug(llvm::raw_ostream &OS, size_t Indent = 0) -> void;
  auto hasChild(SyntaxKind SK) const -> bool {
    for (auto &Child : Children) {
      if (Child->getSyntaxKind() == SK)
        return true;
    }
    return false;
  }

  static bool classof(const GreenElement *E) {
    return E->getKind() == GreenElementKind::Node;
  }
};

class SyntaxNode {
  std::optional<std::shared_ptr<SyntaxNode>> Parent;
  std::shared_ptr<GreenElement> Green;
  std::vector<std::shared_ptr<SyntaxNode>> Children;
  /// How far into the file is the current node?
  ///
  /// For the root, this is zero.
  uint32_t Offset;
  uint32_t Length;
  uint32_t Index;

public:
  explicit SyntaxNode(std::optional<std::shared_ptr<SyntaxNode>> Parent,
                      std::shared_ptr<GreenElement> Green, uint32_t Offset,
                      uint32_t Index)
      : Parent(std::move(Parent)), Green(Green), Offset(Offset), Length(0),
        Index(Index), Children({}) {}

  auto getTextLength() const -> uint32_t { return Green->getTextLength(); }
  auto getSyntaxKind() const -> SyntaxKind { return Green->getSyntaxKind(); }
  auto addChild(uint32_t Index, std::shared_ptr<SyntaxNode> Child) -> void {
    Children.insert(Children.begin() + Index, Child);
  }
  auto getOffset() const -> uint32_t { return Offset; }
  auto getIndex() const -> uint32_t { return Index; }
  auto getGreen() const -> std::shared_ptr<GreenElement> { return Green; }
  auto getParent() const -> std::optional<std::shared_ptr<SyntaxNode>> {
    return Parent;
  }
  auto front() -> decltype(Children.front()) { return Children.front(); }
  auto back() -> decltype(Children.back()) { return Children.back(); }
  auto getLocation() -> SourceLocation;
  auto debug(llvm::raw_ostream &OS, size_t Indent = 0) -> void;

  /// Find a direct child with the given syntax kind.
  auto findChild(SyntaxKind SK) -> std::optional<std::shared_ptr<SyntaxNode>>;

  /// Find all direct children with the given syntax kind.
  ///
  /// This is useful for heterogeneous lists, such as InstanceMemberList having
  /// either Function or IntrinsicFunction members.
  auto findChildren(const std::vector<SyntaxKind> &SKS)
      -> std::optional<std::vector<std::shared_ptr<SyntaxNode>>>;

  /// Find a sibling with the given syntax kind.
  auto findSibling(SyntaxKind SK) -> std::optional<std::shared_ptr<SyntaxNode>>;

  /// Create a root node.
  static auto
  getRoot(std::shared_ptr<GreenElement> Green) -> std::shared_ptr<SyntaxNode> {
    return std::make_shared<SyntaxNode>(std::nullopt, Green, 0, 0);
  }

  /// Create a child node.
  static auto get(std::shared_ptr<SyntaxNode> Parent,
                  std::shared_ptr<GreenElement> Green, uint32_t Offset,
                  uint32_t Index) -> std::shared_ptr<SyntaxNode> {
    auto Self = std::make_shared<SyntaxNode>(Parent, Green, Offset, Index);
    Parent->addChild(Index, Self);
    return Self;
  }
};

/// Turn a Green tree into a red tree.
auto buildSyntaxTree(std::shared_ptr<GreenNode> GreenRoot,
                     DiagnosticManager &DM) -> std::shared_ptr<SyntaxNode>;
} // namespace xd

#endif // XD_FRONTEND_SYNTAX_H

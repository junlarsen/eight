//===----- CompilerInstance.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Driver/CompilerInstance.h"
#include "xd/Frontend/Lexer.h"

#include <xd/Frontend/Parser.h>

using namespace xd;
using namespace llvm;

auto CompilerInstance::addInlineSource(const StringRef &SourceName,
                                       const StringRef &Source) const
    -> SourceFileID {
  auto Buffer = MemoryBuffer::getMemBuffer(Source);
  return SM->addNamedSource(SourceName, std::move(Buffer));
}

auto CompilerInstance::getSyntaxTree(SourceFileID SourceFile,
                                     const std::function<void(Parser &)> &Fn)
    const -> std::shared_ptr<SyntaxNode> {
  auto *Buf = SM->getSourceBuffer(SourceFile);
  auto Lex = Lexer(Buf->getBufferStart());
  auto Parse = Parser(*DM, std::move(Lex.drain()));
  Fn(Parse);
  auto GreenTree = Parse.build();
  return buildSyntaxTree(std::make_shared<GreenNode>(GreenTree), *DM);
}

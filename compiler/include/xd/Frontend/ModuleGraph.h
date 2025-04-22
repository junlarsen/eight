//===----- ModuleGraph.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_MODULEGRAPH_H
#define XD_FRONTEND_MODULEGRAPH_H

#include "xd/Basic/SourceManager.h"

namespace xd {
class ModuleGraphNode {
  SourceFileID SourceFile;

public:
  explicit ModuleGraphNode(SourceFileID SourceFile) : SourceFile(SourceFile) {}
};

class ModuleGraph {
  /// Graph of which files are related to which, using an edge list.
  llvm::DenseMap<SourceFileID, llvm::SmallVector<SourceFileID, 8>,
                 SourceFileID::DenseMapKeyInfo>
      Graph;

public:
  explicit ModuleGraph() {}

  /// Add an edge between the entry and the edges.
  ///
  /// If any of the edges in the given edges causes a cycle in the module graph,
  /// the offending node will be returned.
  auto addFileDependencies(SourceFileID Entry,
                           llvm::SmallVector<SourceFileID, 8> &Edges)
      -> std::optional<SourceFileID>;
};
} // namespace xd

#endif // XD_FRONTEND_MODULEGRAPH_H

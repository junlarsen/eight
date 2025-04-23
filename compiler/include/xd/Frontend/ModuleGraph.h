//===----- ModuleGraph.h ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef XD_FRONTEND_MODULEGRAPH_H
#define XD_FRONTEND_MODULEGRAPH_H

#include "AST.h"
#include "xd/Basic/SourceManager.h"
#include "llvm/ADT/GraphTraits.h"
#include <ranges>
#include <unordered_set>

namespace xd {
class ModuleGraph;

/// Represent a single node in the graph.
///
/// The graph owns all the nodes.
class ModuleGraphNode {
  SourceFileID FileID;
  std::unordered_set<std::shared_ptr<ModuleGraphNode>> Edges;

public:
  explicit ModuleGraphNode(SourceFileID FileID) : FileID(FileID), Edges({}) {}
  auto addEdge(const std::shared_ptr<ModuleGraphNode> &Edge) {
    Edges.insert(Edge);
  }
  auto getFileID() const { return FileID; }
  auto getEdgeCount() const { return Edges.size(); }
  auto begin() { return Edges.begin(); }
  auto end() { return Edges.end(); }
  auto edges() { return Edges; }
};

class ModuleGraph {
public:
  struct ModuleGraphNodeEqual {
    using is_transparent = void;
    bool operator()(const std::shared_ptr<ModuleGraphNode> &LHS,
                    const std::shared_ptr<ModuleGraphNode> &RHS) const {
      return LHS->getFileID() == RHS->getFileID();
    }
    bool operator()(const std::shared_ptr<ModuleGraphNode> &LHS,
                    SourceFileID RHS) const {
      return LHS->getFileID() == RHS;
    }
    bool operator()(SourceFileID LHS,
                    const std::shared_ptr<ModuleGraphNode> &RHS) const {
      return LHS == RHS->getFileID();
    }
  };
  /// Let the hash of the module graph node be the file id itself.
  struct ModuleGraphNodeHash {
    using is_transparent = void;
    using hash_type = std::hash<uint8_t>;
    size_t operator()(const std::shared_ptr<ModuleGraphNode> &Node) const {
      return hash_type{}(Node->getFileID());
    }
    size_t operator()(SourceFileID ID) const { return hash_type{}(ID); }
  };

private:
  /// Graph of which files are related to which, using an edge list.
  std::unordered_set<std::shared_ptr<ModuleGraphNode>, ModuleGraphNodeHash,
                     ModuleGraphNodeEqual>
      Graph;
  std::shared_ptr<ModuleGraphNode> EntryFile;

public:
  explicit ModuleGraph()
      // TODO: Probably use another sentinel value
      : EntryFile(nullptr) {}

  /// Get the entry node, if set.
  auto getEntryNode() const -> std::shared_ptr<ModuleGraphNode> {
    return EntryFile;
  }

  /// Count the number of nodes in the graph.
  auto getNodeCount() const -> size_t { return Graph.size(); }

  /// Add an edge between the entry and the edges.
  ///
  /// If any of the edges in the given edges causes a cycle in the module
  /// graph, the offending node will be returned.
  ///
  /// Calling addFileDependencies with the same Entry multiple times is not
  /// allowed. The caller should use hasModule() to determine whether to call
  /// this or not. Partly the reason for this is that addFileDependencies
  /// effectively runs DFS.
  auto addFileDependencies(SourceFileID Entry,
                           llvm::SmallVector<SourceFileID, 8> &Edges)
      -> std::optional<SourceFileID>;

  /// Has the given module been registered to the graph?
  auto hasNode(SourceFileID Entry) const -> bool {
    auto Node = Graph.find(Entry);
    return Node != Graph.end();
  }

  /// Get the node by its source file id.
  auto getNode(const SourceFileID Entry) -> std::shared_ptr<ModuleGraphNode> {
    auto Node = Graph.find(Entry);
    if (Node == Graph.end())
      return nullptr;
    return *Node;
  }
};
} // namespace xd

#endif // XD_FRONTEND_MODULEGRAPH_H

//===----- ModuleGraph.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/ModuleGraph.h"
#include "xd/Frontend/Syntax.h"
#include "llvm/ADT/SmallSet.h"

using namespace xd;
using namespace llvm;

auto ModuleGraph::addFileDependencies(SourceFileID Entry,
                                      SmallVector<SourceFileID, 8> &Edges)
    -> std::optional<SourceFileID> {
  // Easy case, there are no imports in the entry file, so there is nothing to
  // be done here.
  if (Edges.empty())
    return std::nullopt;
  // It shouldn't be possible to add the same file twice. It would effectively
  // be a no-op. The caller is responsible for maintaining this invariant. Here,
  // we still add all nodes to the graph with empty lists, because this gives us
  // really easy node count.
  if (!hasNode(Entry))
    Graph.insert(std::make_shared<ModuleGraphNode>(Entry));
  auto InsertionPoint = getNode(Entry);
  assert(InsertionPoint->getEdgeCount() == 0 &&
         "trying to add a file once more");
  for (auto Edge : Edges) {
    if (!hasNode(Edge))
      Graph.insert(std::make_shared<ModuleGraphNode>(Edge));
    InsertionPoint->addEdge(getNode(Edge));
  }

  // If this is the first registration, we assign entry as the entire graph's
  // entry node.
  if (EntryFile == nullptr)
    EntryFile = InsertionPoint;

  SmallSet<SourceFileID, 8> Visited;
  SmallSet<SourceFileID, 8> Queue;

  std::function<std::optional<SourceFileID>(SourceFileID)> DepthFirstSearch =
      [&](SourceFileID FileID) -> std::optional<SourceFileID> {
    Visited.insert(FileID);
    Queue.insert(FileID);
    // If this file exists in the graph, then we check all its neighbors.
    auto Node = getNode(FileID);
    if (Node != nullptr) {
      for (auto I : *Node->edges()) {
        auto NeighborID = I->getFileID();
        // If the recursion stack has the neighbor, then there's a cycle.
        if (Queue.contains(NeighborID))
          return NeighborID;

        // If we haven't already visited the neighbour, perform DFS.
        if (!Visited.contains(NeighborID))
          if (auto NeighborFault = DepthFirstSearch(NeighborID); NeighborFault)
            return NeighborID;
      }
    }
    Queue.erase(FileID);
    return std::nullopt;
  };
  return DepthFirstSearch(Entry);
}

auto ModuleGraph::debug(raw_ostream &OS, SourceManager &SM) const -> void {
  OS << "ModuleGraph output: \n";
  for (auto &Node : Graph) {
    auto *Edges = Node->edges();
    auto Name = SM.getSourcePath(Node->getFileID());
    OS << "Node " << *Name << " has " << Edges->size() << " edges\n";
    if (Edges->size() == 0)
      continue;
    for (auto &Edge : *Edges) {
      auto NeighborID = Edge->getFileID();
      auto Neighbor = SM.getSourcePath(NeighborID);
      OS << "  " << *Neighbor << "\n";
    }
  }
}

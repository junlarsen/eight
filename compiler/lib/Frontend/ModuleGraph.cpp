//===----- ModuleGraph.cpp ---===//
//
// Part of the XD Compiler Project, under the Apache License v2.0 with
// LLVM Exceptions. See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "xd/Frontend/ModuleGraph.h"
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
  // be a no-op. The caller is responsible for maintaining this invariant.
  assert(!Graph.contains(Entry) &&
         "Entry is being attempted to be registered twice");
  Graph.insert(std::make_pair(Entry, Edges));

  SmallSet<uint32_t, 8> Visited;
  SmallSet<uint32_t, 8> Queue;

  std::function<std::optional<SourceFileID>(SourceFileID)> DepthFirstSearch =
      [&](SourceFileID FileID) -> std::optional<SourceFileID> {
    Visited.insert(FileID);
    Queue.insert(FileID);
    // If this file exists in the graph, then we check all its neighbors.
    if (Graph.contains(FileID)) {
      for (auto Neighbor : Graph[FileID]) {
        // If the recursion stack has the neighbor, then there's a cycle.
        if (Queue.contains(Neighbor))
          return Neighbor;

        // If we haven't already visited the neighbour, perform DFS.
        if (!Visited.contains(Neighbor))
          if (auto NeighborFault = DepthFirstSearch(Neighbor); NeighborFault)
            return Neighbor;
      }
    }
    Queue.erase(FileID);
    return std::nullopt;
  };
  return DepthFirstSearch(Entry);
}

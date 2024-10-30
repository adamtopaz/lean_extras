import Lean

open Std

universe v u

/--
A hash graph is a directed graph where nodes and edges are stored in hash sets, 
and the source and target of each edge is stored in a hash map.
-/
structure HashGraph (ν : Type u) (ε : Type v) 
    [Hashable ν] [Hashable ε] [BEq ν] [BEq ε] where
  node : HashSet ν
  edge : HashSet ε 
  source : HashMap ε ν
  target : HashMap ε ν

namespace HashGraph

variable {ν : Type u} {ε : Type v} [Hashable ν] [Hashable ε] [BEq ν] [BEq ε]
variable (G : HashGraph ν ε)

variable (ν ε) in
/--
The empty hash graph.
-/
def empty : HashGraph ν ε where
  node := .empty
  edge := .empty
  source := .empty
  target := .empty

instance : EmptyCollection (HashGraph ν ε) where
  emptyCollection := .empty _ _

instance : Inhabited (HashGraph ν ε) where
  default := {}

/--
Insert a node into the hash graph.
-/
def insertNode (x : ν) : HashGraph ν ε where
  node := G.node.insert x
  edge := G.edge
  source := G.source
  target := G.target

instance : Singleton ν (HashGraph ν ε) where
  singleton x := HashGraph.empty _ _ |>.insertNode x

instance : Insert ν (HashGraph ν ε) where
  insert x A := A.insertNode x

/--
Insert an edge into the hash graph, with `s` as the source and `t` as the target.
-/
def insertEdge (e : ε) (s t : ν) : HashGraph ν ε where
  node := G.node.insertMany [s,t]
  edge := G.edge.insert e
  source := G.source.insert e s
  target := G.target.insert e t

/--
The union of two hash graphs. 
-/
def union (A B : HashGraph ν ε) : HashGraph ν ε where
  node := B.node.fold .insert A.node
  edge := B.edge.fold .insert A.edge
  source := B.source.fold .insert A.source
  target := B.target.fold .insert A.target

instance : Union (HashGraph ν ε) where
  union A B := A.union B

open Lean in
/--
Serialize the hash graph to a JSON object.
You must provide a function `node : ν → Json` to serialize nodes, and a function `edge : ε → Json` to serialize edges.
The resulting object has the following fields:
- `node` : an array of JSON objects representing the nodes.
- `edge` : an array of JSON objects representing the edges.
- `source` : an array of pairs `(edgeIdx, nodeIdx)` representing the source of each edge.
- `target` : an array of pairs `(edgeIdx, nodeIdx)` representing the target of each edge.
- `num_node` : the number of nodes.
- `num_edge` : the number of edges.
-/
def mkJson (node : ν → Json) (edge : ε → Json) : Json := Id.run do 
  let nodes := G.node.toArray
  let edges := G.edge.toArray
  let mut nodesMap : Std.HashMap ν Nat := .ofList nodes.zipWithIndex.toList
  let mut edgesMap : Std.HashMap ε Nat := .ofList edges.zipWithIndex.toList
  let sources := G.source.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  let targets := G.target.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  return .mkObj [
    ("node", toJson <| nodes.map node),
    ("edge", toJson <| edges.map edge),
    ("source", toJson <| sources),
    ("target", toJson <| targets),
    ("num_node", nodes.size),
    ("num_edge", edges.size)
  ]

open Lean in
/--
Serialize the hash graph to a JSON object, but retain the index of a specific node.
Similar to `HashGraph.mkJson`, but provides an additional field `idx` that contains the index of the node `idx`.
-/
def mkJsonWithIdx (idx : ν) (node : ν → Json) (edge : ε → Json) : Json := Id.run do 
  let nodes := G.node.toArray
  let edges := G.edge.toArray
  let mut nodesMap : Std.HashMap ν Nat := .ofList nodes.zipWithIndex.toList
  let mut edgesMap : Std.HashMap ε Nat := .ofList edges.zipWithIndex.toList
  let sources := G.source.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  let targets := G.target.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  return .mkObj [
    ("node", toJson <| nodes.map node),
    ("edge", toJson <| edges.map edge),
    ("source", toJson <| sources),
    ("target", toJson <| targets),
    ("num_node", nodes.size),
    ("num_edge", edges.size),
    ("idx", toJson <| nodesMap.get? idx)
  ]

open Lean in
/--
Serialize the hash graph to a JSON object, but retain the indices of a list of nodes.
Similar to `HashGraph.mkJson`, but provides an additional field `idxs` that contains the indices of the nodes in `idxs`.
-/
def mkJsonWithIdxs (idxs : List ν) (node : ν → Json) (edge : ε → Json) : Json := Id.run do 
  let nodes := G.node.toArray
  let edges := G.edge.toArray
  let mut nodesMap : Std.HashMap ν Nat := .ofList nodes.zipWithIndex.toList
  let mut edgesMap : Std.HashMap ε Nat := .ofList edges.zipWithIndex.toList
  let sources := G.source.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  let targets := G.target.toArray.filterMap fun (e,v) => do
    let edgeIdx ← edgesMap.get? e
    let nodeIdx ← nodesMap.get? v
    return (edgeIdx, nodeIdx)
  return .mkObj [
    ("node", toJson <| nodes.map node),
    ("edge", toJson <| edges.map edge),
    ("source", toJson <| sources),
    ("target", toJson <| targets),
    ("num_node", nodes.size),
    ("num_edge", edges.size),
    ("idxs", toJson <| idxs.map nodesMap.get?)
  ]

/--
Serialize the hash graph to a DOT graph.
You must provide a function `nodeLabel : ν → String` to label nodes, and a function `edgeLabel : ε → String` to label edges.
You must also provide a function `nodeId : ν → UInt64` to assign a unique ID to each node; usually this will just be `hash`.
The resulting string is a DOT graph.
-/
def mkDot
    (nodeLabel : ν → String)
    (edgeLabel : ε → String) 
    (nodeId : ν → UInt64) :
    String := Id.run do
  let mut out := "digraph {" ++ "\n"
  for node in G.node do
    out := out ++ s!"  {nodeId node} [label=\"{nodeLabel node}\"];" ++ "\n"
  for edge in G.edge do
    let some source := G.source.get? edge | continue
    let some target := G.target.get? edge | continue
    out := out ++ s!"  {nodeId source} -> {nodeId target} [label=\"{edgeLabel edge}\"]" ++ "\n"
  return out ++ "}"

/--
Serialize the hash graph to a DOT graph, but retain the index of a specific node.
Similar to `HashGraph.mkDot`, but colors the node with index `idx` red.
-/
def mkDotWithIdx
    (idx : ν)
    (nodeLabel : ν → String)
    (edgeLabel : ε → String) 
    (nodeId : ν → UInt64) :
    String := Id.run do
  let mut out := "digraph {" ++ "\n"
  for node in G.node do
    out := out ++ s!"  {nodeId node} [label=\"{nodeLabel node}\", color={if idx == node then "red" else "black"}];" ++ "\n"
  for edge in G.edge do
    let some source := G.source.get? edge | continue
    let some target := G.target.get? edge | continue
    out := out ++ s!"  {nodeId source} -> {nodeId target} [label=\"{edgeLabel edge}\"]" ++ "\n"
  return out ++ "}"

/--
Serialize the hash graph to a DOT graph, but retain the indices of a list of nodes.
Similar to `HashGraph.mkDot`, but colors the nodes with indices in `idxs` red.
-/
def mkDotWithIdxs
    (idxs : List ν)
    (nodeLabel : ν → String)
    (edgeLabel : ε → String) 
    (nodeId : ν → UInt64) :
    String := Id.run do
  let mut out := "digraph {" ++ "\n"
  for node in G.node do
    out := out ++ s!"  {nodeId node} [label=\"{nodeLabel node}\", color={if idxs.contains node then "red" else "black"}];" ++ "\n"
  for edge in G.edge do
    let some source := G.source.get? edge | continue
    let some target := G.target.get? edge | continue
    out := out ++ s!"  {nodeId source} -> {nodeId target} [label=\"{edgeLabel edge}\"]" ++ "\n"
  return out ++ "}"

/--
Compute the component of the hash graph that has a path to the node `idx`.
-/
def componentTo 
    {ν ε : Type u} 
    [Hashable ν] [BEq ν] [DecidableEq ν] 
    [Hashable ε] [BEq ε] 
    (G : HashGraph ν ε) (idx : ν) : 
    (HashGraph ν ε) := Id.run do 
  assert! G.node.contains idx
  let mut outGraph : HashGraph ν ε := {idx}
  let mut queue : Array ν := #[idx]
  let mut edgesToVisit := G.edge
  while h : queue.size ≠ 0 do
    let current := queue[queue.size-1]
    queue := queue.pop
    let mut edgesToRemove : HashSet ε := {}
    for edge in edgesToVisit do
      let some tgt := G.target.get? edge | continue
      unless tgt = current do continue
      let some src := G.source.get? edge | continue
      outGraph := outGraph.insertEdge edge src tgt
      queue := queue.push src
      edgesToRemove := edgesToRemove.insert edge
    for edge in edgesToRemove do
      edgesToVisit := edgesToVisit.erase edge
  return outGraph

/--
Compute the component of the hash graph that has a path from the node `idx`.
-/
def componentFrom 
    {ν ε : Type u} 
    [Hashable ν] [BEq ν] [DecidableEq ν] 
    [Hashable ε] [BEq ε] 
    (G : HashGraph ν ε) (idx : ν) : 
    (HashGraph ν ε) := Id.run do 
  assert! G.node.contains idx
  let mut outGraph : HashGraph ν ε := {idx}
  let mut queue : Array ν := #[idx]
  let mut edgesToVisit := G.edge
  while h : queue.size ≠ 0 do
    let current := queue[queue.size-1]
    queue := queue.pop
    let mut edgesToRemove : HashSet ε := {}
    for edge in edgesToVisit do
      let some src := G.source.get? edge | continue
      unless src = current do continue
      let some tgt := G.target.get? edge | continue
      outGraph := outGraph.insertEdge edge src tgt
      queue := queue.push tgt
      edgesToRemove := edgesToRemove.insert edge
    for edge in edgesToRemove do
      edgesToVisit := edgesToVisit.erase edge
  return outGraph

end HashGraph

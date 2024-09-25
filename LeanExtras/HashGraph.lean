import Lean

open Std

universe v u

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
def empty : HashGraph ν ε where
  node := .empty
  edge := .empty
  source := .empty
  target := .empty

instance : EmptyCollection (HashGraph ν ε) where
  emptyCollection := .empty _ _

instance : Inhabited (HashGraph ν ε) where
  default := {}

def insertNode (x : ν) : HashGraph ν ε where
  node := G.node.insert x
  edge := G.edge
  source := G.source
  target := G.target

instance : Singleton ν (HashGraph ν ε) where
  singleton x := HashGraph.empty _ _ |>.insertNode x

instance : Insert ν (HashGraph ν ε) where
  insert x A := A.insertNode x

def insertEdge (e : ε) (s t : ν) : HashGraph ν ε where
  node := G.node.insertMany [s,t]
  edge := G.edge.insert e
  source := G.source.insert e s
  target := G.target.insert e t

def union (A B : HashGraph ν ε) : HashGraph ν ε where
  node := B.node.fold .insert A.node
  edge := B.edge.fold .insert A.edge
  source := B.source.fold .insert A.source
  target := B.target.fold .insert A.target

instance : Union (HashGraph ν ε) where
  union A B := A.union B

open Lean in
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

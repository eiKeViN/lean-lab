module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion. Source spans: GradedSheaves:15.
See migration.json and MIGRATION.md for exact provenance.
Removing a vertex and splitting graph coordinates into the remaining graph and incident edges. GraphEquiv is currently supplied by the existing graded reindex source unit. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
universe um
variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

 @[expose] def removeGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    OrderedGraph {y : V // y ≠ x} {e : E // G.source e ≠ x} where
  source e := ⟨G.source e.val,e.property⟩
  target e := ⟨G.target e.val,ht e.val⟩
  increasing e := G.increasing e.val

 @[expose] def removeTarget (x : V) (ht : ∀ e, G.target e ≠ x) :
    {e : E // G.source e = x} → {y : V // y ≠ x} := fun e => ⟨G.target e.val,ht e.val⟩

@[expose] noncomputable def splitVertex (x : V) : V ≃ WithBot {y : V // y ≠ x} := by
  classical
  exact
    { toFun := fun y => if h : y=x then ⊥ else (⟨y,h⟩ : {y : V // y ≠ x})
      invFun := WithBot.recBotCoe x Subtype.val
      left_inv := by intro y; by_cases h : y=x <;> simp [h]
      right_inv := by
        intro y
        induction y using WithBot.recBotCoe with
        | bot => simp
        | coe y => simp [y.property] }

@[expose] noncomputable def splitEdge (x : V) : E ≃ {e : E // G.source e ≠ x} ⊕ {e : E // G.source e = x} := by
  classical
  exact
    { toFun := fun e => if h : G.source e=x then Sum.inr ⟨e,h⟩ else Sum.inl ⟨e,h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro e; by_cases h : G.source e=x <;> simp [h]
      right_inv := by
        intro e
        cases e with
        | inl e => simp [e.property]
        | inr e => simp [e.property] }

omit [PartialOrder V] in
@[simp] theorem splitVertex_self (x : V) : splitVertex x x = ⊥ := by
  classical
  simp [splitVertex]

omit [PartialOrder V] in
 theorem splitVertex_ne (x y : V) (hy : y ≠ x) :
    splitVertex x y = (⟨y,hy⟩ : {y : V // y ≠ x}) := by
  classical
  simp [splitVertex,hy]

@[expose] noncomputable def splitGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    GraphEquiv G (bottomGraph (removeGraph G x ht) (removeTarget G x ht)) where
  vertex := splitVertex x
  edge := splitEdge G x
  source := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,bottomGraph]
    · simp [splitEdge,splitVertex,h,bottomGraph,removeGraph]
  target := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeTarget]
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeGraph]

 theorem splitEdge_labels {A : Type*} (α : E → A) (x : V) :
    (Sum.elim (fun e : {e : E // G.source e ≠ x} => α e.val)
      (fun e : {e : E // G.source e = x} => α e.val)) ∘ (splitEdge G x) = α := by
  classical
  funext e
  by_cases h : G.source e=x <;> simp [splitEdge,h]

end KLInvariance.MomentGraph
end

end OAI

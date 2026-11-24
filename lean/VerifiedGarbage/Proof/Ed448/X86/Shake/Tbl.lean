module

public import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
public import VerifiedGarbage.Proof.Ed448.X86.CombTbl
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 on x86 (32-bit): a static for the complete operations

The complete operations read the comb's tables only through
`vg_ed448_scalar_base`: the tables are one of their inputs (`TblIn`), so a call
finds them as on entry (`TblIn.held`), at the address the static's name has,
which no code changes (`two_syms`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86
open VG.Impl.Ed448.X86 (combSym combWords)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.STK)

variable {ws : List (BitVec 64)} {E scr : BitVec 32} {n : Nat} {ins outs : List Region}

/-- A static's words `ws` at `T`, an input. -/
structure StIn (ws : List (BitVec 64)) (T : BitVec 32) (ins : List Region) (m : Mem) : Prop where
  fit : T.toNat + 8 * ws.length ≤ 2 ^ 32
  mem : StR ws (T.setWidth 64) ∈ ins
  words : StWords ws (T.setWidth 64) m

/-- The comb's tables at `T`, an input. -/
abbrev TblIn (T : BitVec 32) (ins : List Region) (m : Mem) : Prop := StIn combWords T ins m

/-- The tables, in the operation's frame. -/
theorem StIn.keep {T : BitVec 32} {g : Reg → BitVec 32} {m : Mem} {u : State} (h : StIn ws T ins m)
    (hk : Kit E scr n ins outs) (hu : Whole.Ctx E g m ins outs u) : StIn ws T ins u.mem :=
  ⟨h.fit, h.mem, h.words.frame (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_of_le_of_lt h.fit (by decide))) hu.frame fun r hr => hk.io _ h.mem r hr⟩

/-- The tables, as a callee of the operation finds them. -/
theorem StIn.held {T : BitVec 32} {g : Reg → BitVec 32} {m : Mem} {u : State} (h : StIn ws T ins u.mem)
    (hk : Kit E scr n ins outs) (hu : Whole.Ctx E g m ins outs u) {sym : String}
    (hy : u.syms sym = T) {rd wr L : List Region}
    (hL : ∀ r ∈ L, (StR ws (T.setWidth 64)).Disjoint r) : StHeld sym ws (u.callEntry.withRegions rd wr) L := by
  have e : (u.callEntry.withRegions rd wr).syms sym = T := hy
  rw [StHeld, e]
  refine ⟨?_, h.fit, hL⟩
  have w : StWords ws (T.setWidth 64) u.callEntry.mem := by
    refine h.words.frame (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_of_le_of_lt h.fit (by decide)))
      (VG.Proof.Ed25519.X86.Whole.callEntry_frame u) fun r hr => ?_
    rw [List.mem_singleton.mp hr, hu.esp]
    exact (hk.io _ h.mem _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right
      (VG.Proof.Ed25519.X86.Whole.below_sub_stack hk.below (by decide))
  exact w

/-- The regions a call of `vg_ed448_scalar_base` writes are apart from the tables. -/
theorem StIn.away {T : BitVec 32} {m : Mem} (h : StIn ws T ins m) (hk : Kit E scr n ins outs) {out sc : Region}
    (ho : ∃ R ∈ outs, Region.Sub out R) (hs : sc ∈ outs) :
    ∀ r ∈ [out, sc, ⟨(E - 4).setWidth 64 - 20#64, 20⟩], (StR ws (T.setWidth 64)).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨R, hR, hsub⟩ := ho
    exact (hk.io _ h.mem _ (List.mem_append_left _ hR)).sub_right hsub
  · exact hk.io _ h.mem _ (List.mem_append_left _ hs)
  · exact (hk.callee_in _ h.mem).symm

/-- The regions a call of `vg_ed448_verify_equation` writes are apart from the static. -/
theorem StIn.away₁ {T : BitVec 32} {m : Mem} (h : StIn ws T ins m) (hk : Kit E scr n ins outs) {sc : Region}
    (hs : sc ∈ outs) :
    ∀ r ∈ [sc, ⟨(E - 4).setWidth 64 - 20#64, 20⟩], (StR ws (T.setWidth 64)).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.io _ h.mem _ (List.mem_append_left _ hs)
  · exact (hk.callee_in _ h.mem).symm

/-- `Two`, with each state naming the static `sym` at `T`. -/
def TwoS (sym : String) (T : BitVec 32) (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) : Prop :=
  Two E ins outs g₁ g₂ m₁ m₂ P a b ∧ a.syms sym = T ∧ b.syms sym = T

abbrev TwoT (T : BitVec 32) (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) : Prop := TwoS combSym T E ins outs g₁ g₂ m₁ m₂ P a b

theorem two_syms {sym : String} {T : BitVec 32} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {P Q : State → Prop} {c : Prog isa}
    (h : RelCT isa (Two E ins outs g₁ g₂ m₁ m₂ P) c (Two E ins outs g₁ g₂ m₁ m₂ Q)) :
    RelCT isa (TwoS sym T E ins outs g₁ g₂ m₁ m₂ P) c (TwoS sym T E ins outs g₁ g₂ m₁ m₂ Q) := by
  intro a b ta tb a' b' ⟨hp, ya, yb⟩ ea eb
  obtain ⟨e, q⟩ := h _ _ _ _ _ _ hp ea eb
  exact ⟨e, q, (congrFun (Exec.syms ea) _).trans ya, (congrFun (Exec.syms eb) _).trans yb⟩

theorem TwoS.two {sym : String} {T : BitVec 32} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem} {P : State → Prop} {a b : State}
    (h : TwoS sym T E ins outs g₁ g₂ m₁ m₂ P a b) (hk : Kit E scr n ins outs) (t₁ : StIn ws T ins m₁)
    (t₂ : StIn ws T ins m₂) :
    Two E ins outs g₁ g₂ m₁ m₂ (fun t => P t ∧ t.syms sym = T ∧ StIn ws T ins t.mem) a b :=
  ⟨⟨h.1.1.1, h.1.1.2, h.2.1, t₁.keep hk h.1.1.1⟩, ⟨h.1.2.1, h.1.2.2, h.2.2, t₂.keep hk h.1.2.1⟩⟩

end VG.Proof.Ed448.X86.Shake

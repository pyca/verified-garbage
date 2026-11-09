module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Data
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the facts of the candidate's regions, which only `Call` uses

/-! # The regions of a candidate call (ARMv7)

The candidate runs on the tape from `used`, with its stack arguments in its
frame at `S2 = sp - 72` and its own stack the 112 bytes below: what its
precondition says of them, from the search's.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm

abbrev rO (p : SearchPublic) : Region := ⟨State.addr p.op, p.len⟩
abbrev rU (p : SearchPublic) : Region := ⟨State.addr p.up, 8⟩
abbrev rE (p : SearchPublic) : Region := ⟨State.addr p.ep, p.elen⟩
abbrev rP (p : SearchPublic) : Region := ⟨State.addr p.pp, p.plen⟩
abbrev rR (p : SearchPublic) (used : Nat) : Region := ⟨State.addr (p.rp + BitVec.ofNat 32 used), p.randLen - used⟩
abbrev rS (p : SearchPublic) : Region := ⟨State.addr p.B, p.words * 8⟩
abbrev rA (p : SearchPublic) : Region := ⟨State.addr p.S2, 28⟩
abbrev rF (p : SearchPublic) : Region := ⟨State.addr p.S2 - 112#64, 112⟩

/-- What the candidate's precondition says of its regions. -/
structure CallFacts (p : SearchPublic) (used : Nat) : Prop where
  spLo : 112 ≤ p.S2.toNat
  spHi : p.S2.toNat + 28 ≤ 2 ^ 32
  oU : (rO p).Disjoint (rU p)
  oE : (rO p).Disjoint (rE p)
  oP : (rO p).Disjoint (rP p)
  oR : (rO p).Disjoint (rR p used)
  oS : (rO p).Disjoint (rS p)
  oA : (rO p).Disjoint (rA p)
  uE : (rU p).Disjoint (rE p)
  uP : (rU p).Disjoint (rP p)
  uR : (rU p).Disjoint (rR p used)
  uS : (rU p).Disjoint (rS p)
  uA : (rU p).Disjoint (rA p)
  eS : (rE p).Disjoint (rS p)
  pS : (rP p).Disjoint (rS p)
  rS' : (rR p used).Disjoint (rS p)
  sA : (rS p).Disjoint (rA p)
  fO : (rF p).Disjoint (rO p)
  fU : (rF p).Disjoint (rU p)
  fE : (rF p).Disjoint (rE p)
  fP : (rF p).Disjoint (rP p)
  fR : (rF p).Disjoint (rR p used)
  fS : (rF p).Disjoint (rS p)
  fA : (rF p).Disjoint (rA p)
  no : p.op.toNat + p.len ≤ 2 ^ 32
  nu : p.up.toNat + 8 ≤ 2 ^ 32
  ne : p.ep.toNat + p.elen ≤ 2 ^ 32
  np : p.pp.toNat + p.plen ≤ 2 ^ 32
  nr : (p.rp + BitVec.ofNat 32 used).toNat + (p.randLen - used) ≤ 2 ^ 32
  ns : p.B.toNat + p.words * 8 ≤ 2 ^ 32

namespace SearchInput

variable {p : SearchPublic} {o : State}

theorem regions (h : SearchInput p o) :
    inOut o = rO p ∧ inUsed o = rU p ∧ inE o = rE p ∧ inP o = rP p ∧
      inRand o = ⟨State.addr p.rp, p.randLen⟩ ∧ inScr o = rS p ∧ inState o = ⟨State.addr p.stp, 32⟩ := by
  obtain ⟨-, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The tape from `used` is in the tape. -/
theorem tail_sub (h : SearchInput p o) {used : Nat} (hu : used ≤ p.randLen) :
    Region.Sub (rR p used) (inRand o) := by
  have hf := h.facts.nR
  rw [h.regions.2.2.2.2.1]
  change Region.Sub ⟨State.addr (p.rp + BitVec.ofNat 32 used), p.randLen - used⟩ _
  by_cases hl : used < p.randLen
  · have e : State.addr (p.rp + BitVec.ofNat 32 used) = State.addr p.rp + BitVec.ofNat 64 used :=
      VG.Arm.addr_add (by omega)
    rw [e]
    exact Offset.sub_base _ (by omega)
  · intro x hx
    simp only [Region.Contains] at hx
    omega

/-- The candidate's frame and stack are in the search's stack. -/
theorem A_sub (h : SearchInput p o) : Region.Sub (rA p) (inStack o) := by
  have room := h.facts.room
  change Region.Sub ⟨State.addr (p.sp - BitVec.ofNat 32 72), 28⟩ _
  rw [FrameStack.addr_sub' (by omega), h.sp_eq]
  exact h.stack_sub (by decide) (by decide)

theorem F_sub (h : SearchInput p o) : Region.Sub (rF p) (inStack o) := by
  have room := h.facts.room
  change Region.Sub ⟨State.addr (p.sp - BitVec.ofNat 32 72) - 112#64, 112⟩ _
  rw [FrameStack.addr_sub' (by omega), h.sp_eq, BitVec.sub_sub]
  exact h.stack_sub (by decide) (by decide)

theorem disj_sub {a b c : Region} (hd : c.Disjoint b) (hs : Region.Sub a c) : a.Disjoint b :=
  fun x ha hb => hd x (hs x ha) hb

theorem callFacts (h : SearchInput p o) {used : Nat} (hu : used ≤ p.randLen) : CallFacts p used := by
  obtain ⟨eO, eU, eE, eP, eR, eS, -⟩ := h.regions
  have f := h.facts
  have room := f.room
  have pw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at pw
  obtain ⟨⟨dOU, dOS, -⟩, ⟨dUS, -⟩, -⟩ := pw
  simp only [eO, eU, eS] at dOU dOS dUS
  have wr {w r : Region} (hw : w ∈ inWrites o) (hr : r ∈ inReads o) : w.Disjoint r := h.write_disjoint hw hr
  have st {r : Region} (hr : r ∈ inWrites o ++ inReads o) : (inStack o).Disjoint r := h.stack_disjoint hr
  have hR := h.tail_sub hu
  have hA := h.A_sub
  have hF := h.F_sub
  have S2n : p.S2.toNat = p.sp.toNat - 72 := FrameStack.sub_toNat' (by omega)
  have mO : inOut o ∈ inWrites o := by simp [inWrites]
  have mU : inUsed o ∈ inWrites o := by simp [inWrites]
  have mS : inScr o ∈ inWrites o := by simp [inWrites]
  have mE : inE o ∈ inReads o := by simp [inReads]
  have mP : inP o ∈ inReads o := by simp [inReads]
  have mR : inRand o ∈ inReads o := by simp [inReads]
  have wE {w : Region} (hw : w ∈ inWrites o) : w.Disjoint (rE p) := by rw [← eE]; exact wr hw mE
  have wP {w : Region} (hw : w ∈ inWrites o) : w.Disjoint (rP p) := by rw [← eP]; exact wr hw mP
  have wR {w : Region} (hw : w ∈ inWrites o) : w.Disjoint (rR p used) :=
    ((disj_sub (wr hw mR).symm hR)).symm
  have wA {w : Region} (hw : w ∈ inWrites o) : w.Disjoint (rA p) :=
    (disj_sub (st (List.mem_append_left _ hw)) hA).symm
  have fW {w : Region} (hw : w ∈ inWrites o ++ inReads o) : (rF p).Disjoint w := disj_sub (st hw) hF
  have fR : (rF p).Disjoint (rR p used) :=
    (disj_sub (fW (List.mem_append_right _ mR)).symm hR).symm
  have fA : (rF p).Disjoint (rA p) := by
    exact (Offset.base_disjoint_below (State.addr p.S2) (n := 112) (k := 28) (by decide)).symm
  refine ⟨by omega, by have := f.top; omega, dOU, ?_, ?_, ?_, dOS, ?_, ?_, ?_, ?_, dUS, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, fR, ?_, fA, f.nO, f.nU, f.nE, f.nP, ?_, f.nS⟩
  · rw [← eO]; exact wE mO
  · rw [← eO]; exact wP mO
  · rw [← eO]; exact wR mO
  · rw [← eO]; exact wA mO
  · rw [← eU]; exact wE mU
  · rw [← eU]; exact wP mU
  · rw [← eU]; exact wR mU
  · rw [← eU]; exact wA mU
  · rw [← eS]; exact (wE mS).symm
  · rw [← eS]; exact (wP mS).symm
  · rw [← eS]; exact (wR mS).symm
  · rw [← eS]; exact wA mS
  · rw [← eO]; exact fW (List.mem_append_left _ mO)
  · rw [← eU]; exact fW (List.mem_append_left _ mU)
  · rw [← eE]; exact fW (List.mem_append_right _ mE)
  · rw [← eP]; exact fW (List.mem_append_right _ mP)
  · rw [← eS]; exact fW (List.mem_append_left _ mS)
  · have := f.nR
    have := (p.rp + BitVec.ofNat 32 used).isLt
    by_cases hl : used < p.randLen
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    · omega

end SearchInput

end VG.Proof.RsaKeyGen.Arm.Search

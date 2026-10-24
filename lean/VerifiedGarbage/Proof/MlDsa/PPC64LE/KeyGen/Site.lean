module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Base
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE: the buffers of the top-level functions

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Site.lean`). The top-level
functions work on five buffers (a `Lay`, as ML-KEM's): `scratch` (buffer 0),
the `STK` bytes of stack below the stack pointer (buffer 1), and their
arguments (buffers 2, 3 and 4, whose pointers they keep in `r30`, `r29` and
`r28`; `r31` holds `scratch`): `ix` maps each register to the buffer it
points into. A state where they run their parts is a `Site`.

A pointer `q` (a register and an offset) is the address `lpa L q`, and the
region of `l` bytes there the triple `tri q l`, so that what a part writes
and what the proofs keep track of are lists of triples (`Kept`, `sepB`, as
in ML-KEM). A pointer, in a register of the layout, into a buffer but the
stack is `PtrIn`. The sponge (`hash`) is ML-KEM's (`hash_ok`, `hash_ct`),
which use the 48 bytes below the stack pointer as buffer 1: `hashLay` is the
layout with buffer 1 so narrowed (`Site.ctx`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.Sha3 (bytesAt)

/-- The buffer each register points into. -/
def ix : Reg → Nat
  | .r31 => 0
  | .r30 => 2
  | .r29 => 3
  | .r28 => 4
  | _ => 5

/-- The `l` bytes at the pointer `q`. -/
abbrev tri (q : Ptr) (l : Nat) : Nat × Nat × Nat := (ix q.1, q.2, l)

/-- The address of the pointer `q`. -/
abbrev lpa (L : Lay) (q : Ptr) : Addr := L.A (ix q.1) q.2

/-- The buffers fit in the address space, and a buffer of `Wb` (written, or
the stack) is apart from every other: buffers only read may overlap each
other. -/
structure OkW (L : Lay) (Wb : List Nat) : Prop where
  fit : ∀ i < L.sizes.length, (L.ptr i).toNat + L.size i ≤ 2 ^ 64
  disj : ∀ i < L.sizes.length, ∀ j < L.sizes.length, i ≠ j → (i ∈ Wb ∨ j ∈ Wb) → (L.buf i).Disjoint (L.buf j)

theorem OkW.ok {L : Lay} {Wb : List Nat} (h : OkW L Wb) (hall : ∀ i < L.sizes.length, i ∈ Wb) : L.Ok :=
  ⟨h.fit, fun i hi j hj hij => h.disj i hi j hj hij (.inl (hall i hi))⟩

/-- Two regions apart, one of them in a buffer of `Wb`, or both in the same. -/
theorem disjW' {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb ∨ i = j) :
    (L.R i o l).Disjoint (L.R j o' l') := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hla⟩, hlb⟩, hs⟩ := h
  by_cases e : i = j
  · subst e
    have hf : (L.ptr i).toNat + L.sizes.getD i 0 ≤ 2 ^ 64 := hL.fit i ha
    have hs' : o + l ≤ o' ∨ o' + l' ≤ o := by
      rcases hs with (hs | hs) | hs
      · exact absurd rfl hs
      · exact .inl hs
      · exact .inr hs
    have := (L.ptr i).isLt
    exact Offset.disjoint _ hs' (by omega) (by omega)
  · have hw' : i ∈ Wb ∨ j ∈ Wb := by rcases hw with h | h | h; exacts [.inl h, .inr h, absurd h e]
    exact ((hL.disj _ ha _ hb e hw').sub_left (Lay.R_sub hla)).sub_right (Lay.R_sub hlb)

/-- Two regions apart, one of them in a buffer of `Wb`. -/
theorem disjW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {i o l j o' l' : Nat}
    (h : sepB L.sizes (i, o, l) (j, o', l') = true) (hw : i ∈ Wb ∨ j ∈ Wb) :
    (L.R i o l).Disjoint (L.R j o' l') :=
  disjW' hL h (hw.elim .inl fun h => .inr (.inl h))

/-- A state where the parts of a top-level function run, with `STK` bytes of
stack, and the buffers `Wb` written (and the stack). -/
structure Site (L : Lay) (Wb : List Nat) (STK : Nat) (s : State) : Prop where
  ok : OkW L Wb
  len : L.sizes.length = 5
  w0 : 0 ∈ Wb
  w1 : 1 ∈ Wb
  sz0 : 32768 ≤ L.size 0
  sz1 : L.size 1 = STK
  p1 : L.ptr 1 = s.sp - BitVec.ofNat 64 STK
  s48 : 48 ≤ STK
  spk : STK ≤ s.sp.toNat
  r31 : s.gpr .r31 = L.ptr 0
  r30 : s.gpr .r30 = L.ptr 2
  r29 : s.gpr .r29 = L.ptr 3
  r28 : s.gpr .r28 = L.ptr 4
  cw : ∀ i ∈ Wb, i ≠ 1 → L.buf i ∈ s.wr
  cr : ∀ i < 5, i ≠ 1 → L.buf i ∈ s.rd ++ s.wr

theorem Site.kept {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) {rs : List Region}
    (hk : Kept rs s s') : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hk.sp]; exact h.p1, h.s48, by rw [hk.sp]; exact h.spk,
    by rw [hk.cs .r31 (by decide), h.r31], by rw [hk.cs .r30 (by decide), h.r30],
    by rw [hk.cs .r29 (by decide), h.r29], by rw [hk.cs .r28 (by decide), h.r28],
    by rw [hk.wr]; exact h.cw, by rw [hk.wr, hk.rd]; exact h.cr⟩

/-- A register of the layout. -/
def baseReg (r : Reg) : Bool := r == .r28 || r == .r29 || r == .r30 || r == .r31

/-- A register of the layout holds the pointer to its buffer. -/
theorem Site.base {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {r : Reg}
    (hr : baseReg r = true) : s.gpr r = L.ptr (ix r) := by
  simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((rfl | rfl) | rfl) | rfl
  exacts [h.r28, h.r29, h.r30, h.r31]

theorem baseReg_of {q : Ptr} (h : argOk (.ptr q) = true) : baseReg q.1 = true := by
  simp only [argOk, Bool.and_eq_true] at h; exact h.1

/-- A register of the layout is callee-saved. -/
theorem base_pres {r : Reg} (h : baseReg r = true) : r ∈ preserved := by
  simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

theorem ix_ne1 (r : Reg) : ix r ≠ 1 := by cases r <;> decide

theorem ix_lt {r : Reg} (h : baseReg r = true) : ix r < 5 := by
  simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

/-- A buffer, but the stack, with `l` bytes at offset `o`. -/
def inB (sz : List Nat) (w : Nat × Nat × Nat) : Bool :=
  w.1 != 1 && w.1 < sz.length && w.2.1 + w.2.2 ≤ sz.getD w.1 0

theorem inB_bounds {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) :
    w.1 ≠ 1 ∧ w.1 < sz.length ∧ w.2.1 + w.2.2 ≤ sz.getD w.1 0 := by
  simp only [inB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem inB_sep {sz : List Nat} {w : Nat × Nat × Nat} (h : inB sz w = true) {o l : Nat}
    (hs : o + l ≤ sz.getD 1 0) (h1 : 1 < sz.length) : sepB sz w (1, o, l) = true := by
  obtain ⟨h1', h2, h3⟩ := inB_bounds h
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨h2, h1⟩, h3⟩, hs⟩, .inl (.inl h1')⟩

/-- A pointer, in a register of the layout, to `l` bytes of a buffer (but the stack). -/
def PtrIn (L : Lay) (q : Ptr) (l : Nat) : Prop := argOk (.ptr q) = true ∧ inB L.sizes (tri q l) = true

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s)
include h

/-- The value of a pointer argument. -/
theorem Site.val {q : Ptr} (hq : argOk (.ptr q) = true) : argVal s (.ptr q) = lpa L q := by
  simp only [argVal, h.base (baseReg_of hq)]

/-- A pointer into a buffer fits in the address space. -/
theorem Site.fitE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (hl : 0 < l) : (lpa L q).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨-, h2, h3⟩ := inB_bounds pq.2
  dsimp only [tri] at h2 h3
  have hf := h.ok.fit _ h2
  have hq : q.2 < 2 ^ 31 := by
    have := pq.1; simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
  simp only [Lay.size] at hf
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.2) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A pointer argument's register after the moves. -/
theorem Site.gE {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {q : Ptr}
    (hm : (d, .ptr q) ∈ as) (hq : argOk (.ptr q) = true) : (glueSt s as).gpr d = lpa L q := by
  rw [glueSt_arg s hg hn hm, h.val hq]

/-- The stack below the stack pointer, as buffer 1. -/
theorem Site.belowSub {n : Nat} (hn : n ≤ STK) : Region.Sub (below s.sp n) (L.R 1 0 STK) := by
  simp only [below, Lay.R, h.p1, BitVec.add_zero]
  exact Offset.sub_below _ hn (by omega)

/-- A region of a buffer, but the stack, is apart from the stack. -/
theorem Site.stkD {w : Nat × Nat × Nat} (hb : inB L.sizes w = true) {n : Nat} (hn : n ≤ STK) :
    (L.R w.1 w.2.1 w.2.2).Disjoint (below s.sp n) := by
  have hsep := inB_sep hb (o := 0) (l := STK) (by rw [← h.sz1]; simp [Lay.size]) (by rw [h.len]; decide)
  exact (disjW h.ok hsep (.inr h.w1)).sub_right (h.belowSub hn)

/-- A buffer the state may write. -/
theorem Site.cwE {q : Ptr} {l : Nat} (pq : PtrIn L q l) (wq : ix q.1 ∈ Wb) : Covers [L.R (ix q.1) q.2 l] s.wr :=
  Lay.covers (h.cw _ wq (inB_bounds pq.2).1) (inB_bounds pq.2).2.2

/-- A buffer the state may read. -/
theorem Site.crE {q : Ptr} {l : Nat} (pq : PtrIn L q l) : Covers [L.R (ix q.1) q.2 l] (s.rd ++ s.wr) :=
  Lay.covers (h.cr _ (by have := (inB_bounds pq.2).2.1; rw [h.len] at this; exact this) (inB_bounds pq.2).1)
    (inB_bounds pq.2).2.2

/-- Two regions apart, one of them written. -/
theorem Site.dE {q q' : Ptr} {l l' : Nat} (hd : sepB L.sizes (tri q l) (tri q' l') = true)
    (hw : ix q.1 ∈ Wb ∨ ix q'.1 ∈ Wb) : (L.R (ix q.1) q.2 l).Disjoint (L.R (ix q'.1) q'.2 l') := disjW h.ok hd hw

/-- The stack below the stack pointer is apart from a buffer. -/
theorem Site.kE {q : Ptr} {l : Nat} (pq : PtrIn L q l) {n : Nat} (hn : n ≤ STK) {x : State} (hx : x.sp = s.sp) :
    (below x.sp n).Disjoint (L.R (ix q.1) q.2 l) := by
  rw [hx]; exact (h.stkD pq.2 hn).symm

end

/-! ## Changes of the stack -/

/-- What a call changes below the stack pointer is in buffer 1. -/
theorem Site.kept_stk {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    {W : List (Nat × Nat × Nat)} {rs : List Region}
    (hrs : ∀ r ∈ rs, ∃ w ∈ W, Region.Sub r (L.R w.1 w.2.1 w.2.2)) {n : Nat} (hn : n ≤ STK)
    (hk : Kept (rs ++ [below s.sp n]) s s') : Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  ⟨hk.cs, hk.sp, hk.rd, hk.wr, hk.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, hs⟩ := hrs r hr
      exact ⟨_, List.mem_map.mpr ⟨w, List.mem_append_left _ hw, rfl⟩, hs⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_map.mpr ⟨(1, 0, STK), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩,
        h.belowSub hn⟩⟩

/-- Kept, with the regions written those of the triples `W`. -/
theorem Site.keptW {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (hs : Site L Wb STK s)
    (W : List (Nat × Nat × Nat)) {n : Nat} (hn : n ≤ STK) (hk : Kept (L.RL W ++ [below s.sp n]) s s') :
    Kept (L.RL (W ++ [(1, 0, STK)])) s s' :=
  hs.kept_stk (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact ⟨w, hw, fun _ h => h⟩) hn hk

/-- The registers of the layout, the stack pointer, and the pointers of both
runs are the same. -/
theorem Site.gpr_eq {L : Lay} {Wb : List Nat} {STK : Nat} {x y : State} (hx : Site L Wb STK x)
    (hy : Site L Wb STK y) {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup)
    {d : Reg} {a : Arg} (hm : (d, a) ∈ as) : (glueSt x as).gpr d = (glueSt y as).gpr d := by
  rw [glueSt_arg x hg hn hm, glueSt_arg y hg hn hm]
  cases a with
  | imm v => rfl
  | ptr q =>
    have ha : argOk (.ptr q) = true := by
      have := List.all_eq_true.mp hg _ hm; simp only [Bool.and_eq_true] at this; exact this.2
    rw [hx.val ha, hy.val ha]

theorem view_glue_sp (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).sp = s.sp := glueSt_sp s as

theorem view_glue_mem (s : State) (as : List (Reg × Arg)) (rd wr : List Region) :
    (view (glueSt s as) rd wr).mem = s.mem := glueSt_mem s as

theorem view_gpr (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem imm_toNat {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem imm_toNat32 {v : Nat} (h : v < 2 ^ 32) : ((BitVec.ofNat 64 v).setWidth 32).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-! ## The sponge -/

/-- The layout with buffer 1 the 48 bytes below the stack pointer, as ML-KEM's
sponge routine (`hash_ok`) takes it, and of the arguments only those `K`
says (the others empty, so that the buffers are pairwise disjoint). -/
def hashLay (L : Lay) (s : State) (K : Nat → Bool) : Lay :=
  ⟨fun i => if i = 1 then s.sp - BitVec.ofNat 64 48 else L.ptr i,
    [L.size 0, 48, if K 2 then L.size 2 else 0, if K 3 then L.size 3 else 0, if K 4 then L.size 4 else 0]⟩

theorem hashLay_ptr (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) :
    (hashLay L s K).ptr i = L.ptr i := by
  simp only [hashLay, hi, ite_false]

theorem hashLay_R (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (o l : Nat) :
    (hashLay L s K).R i o l = L.R i o l := by
  simp only [Lay.R, hashLay_ptr L s K hi]

theorem hashLay_size_le (L : Lay) (s : State) (K : Nat → Bool) {i : Nat} (hi : i ≠ 1) (hi5 : i < 5) :
    (hashLay L s K).size i ≤ L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact Nat.le_refl _
  all_goals (show (if _ then _ else 0) ≤ _; split <;> omega)

theorem hashLay_size (L : Lay) (s : State) {K : Nat → Bool} {i : Nat} (hi : i ≠ 1) (hK : i = 0 ∨ K i = true)
    (hi5 : i < 5) : (hashLay L s K).size i = L.size i := by
  rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    rcases hK with h | h
    · omega
    · show (if _ then _ else 0) = _; rw [ite_eq_left h]

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {K : Nat → Bool}
  (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
include h hK

theorem hashLay_ok : (hashLay L s K).Ok := by
  have hL := h.ok
  have hsub : Region.Sub ⟨s.sp - BitVec.ofNat 64 48, 48⟩ (L.buf 1) := by
    rw [Lay.buf, show (⟨L.ptr 1, L.size 1⟩ : Region) = L.R 1 0 STK by
      rw [h.sz1]; simp only [Lay.R, BitVec.add_zero]]
    exact h.belowSub h.s48
  have hl5 := h.len
  have bi : ∀ k, k < 5 → k ≠ 1 → Region.Sub ⟨(hashLay L s K).ptr k, (hashLay L s K).size k⟩ (L.buf k) :=
    fun k hk hk1 => by
      rw [hashLay_ptr L s K hk1]
      intro x hx
      have := hashLay_size_le L s K hk1 hk
      simp only [Region.Contains] at hx ⊢
      omega
  have b1 : (⟨(hashLay L s K).ptr 1, (hashLay L s K).size 1⟩ : Region) = ⟨s.sp - BitVec.ofNat 64 48, 48⟩ := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · simp only [hashLay, List.length_cons, List.length_nil] at hi
    by_cases e : i = 1
    · subst e
      show (s.sp - BitVec.ofNat 64 48).toNat + 48 ≤ 2 ^ 64
      have := h.s48; have := h.spk; have := s.sp.isLt; bv_omega
    · have := hashLay_size_le L s K e (by omega)
      simp only [hashLay_ptr L s K e]
      exact Nat.le_trans (Nat.add_le_add_left this _) (hL.fit i (by omega))
  · simp only [hashLay, List.length_cons, List.length_nil] at hi hj
    -- an empty buffer is apart from every other
    by_cases z : (hashLay L s K).size i = 0 ∨ (hashLay L s K).size j = 0
    · intro x hx hy
      rcases z with z | z
      · simp only [Region.Contains, z] at hx; omega
      · simp only [Region.Contains, z] at hy; omega
    have hKi : i ≤ 1 ∨ K i = true := by
      rcases (by omega : i ≤ 1 ∨ 2 ≤ i) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl <;>
          exact z (.inl (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hKj : j ≤ 1 ∨ K j = true := by
      rcases (by omega : j ≤ 1 ∨ 2 ≤ j) with h' | h'
      · exact .inl h'
      · refine .inr ?_
        by_contra hc
        rw [Bool.not_eq_true] at hc
        rcases (by omega : j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl <;>
          exact z (.inr (by show (if _ then _ else 0) = 0; rw [ite_eq_right (by simp [hc])]))
    have hw : i ∈ Wb ∨ j ∈ Wb := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h'
      · exact .inl h.w0
      · exact .inl h.w1
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h''
      · exact .inr h.w0
      · exact .inr h.w1
      exact hK i hi j hj hij h' h'' (hKi.resolve_left (by omega)) (hKj.resolve_left (by omega))
    by_cases ei : i = 1
    · subst ei
      rw [b1]
      exact (hL.disj 1 (by omega) j (by omega) hij hw).sub_left hsub |>.sub_right (bi j hj (Ne.symm hij))
    · by_cases ej : j = 1
      · subst ej
        rw [b1]
        exact ((hL.disj i (by omega) 1 (by omega) hij hw).sub_right hsub).sub_left (bi i hi ei)
      · exact ((hL.disj i (by omega) j (by omega) hij hw).sub_left (bi i hi ei)).sub_right (bi j hj ej)

theorem Site.ctx : Ctx (hashLay L s K) s :=
  ⟨hashLay_ok h hK, by rw [hashLay_size L s (by decide) (.inl rfl) (by decide)]; exact h.sz0, rfl,
    by simp [hashLay], by rw [h.r31]; rfl, Nat.le_trans h.s48 h.spk, by simp [hashLay],
    by rw [show (⟨(hashLay L s K).ptr 0, (hashLay L s K).size 0⟩ : Region) = L.buf 0 from rfl]
       exact h.cw 0 h.w0 (by decide)⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen

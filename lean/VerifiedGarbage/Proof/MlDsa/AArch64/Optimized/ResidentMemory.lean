module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.RoundLoop
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.AArch64.Optimized.ResidentBlock`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResidentRate`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Neon.RoundLoop`, which only this module used -/

section

/-!
# The rounds in a loop, on both lanes

`roundsLoop_ok`: given the vector operations of a round before iota, which
take both lanes' states to their values before iota (`Core2`), and the table
of the round constants at `p` (`RcTable`), `roundsLoop core p` computes
Keccak-f[1600] on both lanes, and changes only `x16` and vector registers.
`rcStore_ok` stores the table.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Proof.MlKem.AArch64 (VChg VUpd wp_vop wp_ldrq)

/-- The constants' table at `T`, readable: word `i` is constant `i / 2`. -/
structure RcTable (s : State) (T : Addr) : Prop where
  rd : ∀ r < 24, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * r)) 16
  word : ∀ i < 48, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = Spec.Sha3.RC (i / 2)

/-- The table survives writes outside it. -/
theorem RcTable.frame {s t : State} {T : Addr} (h : RcTable s T) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, (Region.mk T 384).Disjoint r) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : RcTable t T :=
  ⟨fun k hk => by rw [hrd, hwr]; exact h.rd k hk, fun k hk => by
    rw [hf.readW (r := ⟨T, 384⟩) (Offset.contains_base T (by omega_arith) (by omega_arith)) hd (by decide)]
    exact h.word k hk⟩

/-- Entry `r` of the table, as the value `ldrq` loads. -/
theorem RcTable.entry {s : State} {T : Addr} (h : RcTable s T) {r : Nat} (hr : r < 24) :
    s.mem.read (T + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) := by
  rw [read16_dwords, Offset.add_add, show 16 * r = 8 * (2 * r) by omega_arith, h.word _ (by omega_arith),
    show 8 * (2 * r) + 8 = 8 * (2 * r + 1) by omega_arith, h.word _ (by omega_arith)]
  congr 2 <;> omega_arith

/-- The vector operations of a round before iota. -/
def Core2 (core : List Instr) : Prop :=
  ∀ {t : State} {A B : Spec.Sha3.State}, Pairs t A B →
    WP isa (.block core) t fun u => Keep t u ∧ CPairs u A B

theorem core_ok : Core2 core := fun hp => core2_ok hp

/-- `str x16, [p, off]`. -/
theorem str_ok {s : State} {p : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr p + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8) :
    WP isa (.block [.str .x .x16 p off]) s fun t => t.v = s.v ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.mem = s.mem.writeW a (s.gpr .x16) := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr .x16) }) ?_ (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

/-- `add d, n, imm`, as a write of `d`. -/
theorem addImm_ok {s : State} {p n : Reg} {imm : Nat} (h : imm < 4096) :
    WP isa (.block [.addImm .x p n imm]) s fun t => t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr p = s.gpr n + BitVec.ofNat 64 imm ∧ ∀ g, g ≠ p → t.gpr g = s.gpr g := by
  refine WP.cons (s' := s.write .x p (s.gpr n + BitVec.ofNat 64 imm)) ?_ (WP.block_nil ?_)
  · simp [exec, h, State.read]
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun g hg => ?_⟩
    · simp [State.write]
    · simp [State.write, hg]

/-- `sub p, p, imm`, as a write of `p`. -/
theorem subImm_ok {s : State} {p : Reg} {imm : Nat} (h : imm < 4096) :
    WP isa (.block [.subImm .x p p imm]) s fun t => t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr p = s.gpr p - BitVec.ofNat 64 imm ∧ ∀ g, g ≠ p → t.gpr g = s.gpr g := by
  refine WP.cons (s' := s.write .x p (s.gpr p - BitVec.ofNat 64 imm)) ?_ (WP.block_nil ?_)
  · simp [exec, h, State.read]
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun g hg => ?_⟩
    · simp [State.write]
    · simp [State.write, hg]

/-- After `k` of the table's entries. -/
structure StInv (s : State) (T : Addr) (k : Nat) (t : State) : Prop where
  gpr : ∀ g, g ≠ .x16 → t.gpr g = s.gpr g
  v : t.v = s.v
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨T, 384⟩] s.mem t.mem
  word : ∀ i < 2 * k, t.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = Spec.Sha3.RC (i / 2)

/-- A word of the table after a store of another, or of itself. -/
theorem word_store {m : Mem} {T : Addr} {j i : Nat} (hj : j < 48) (hi : i < 48) (v : BitVec 64) :
    (m.writeW (T + BitVec.ofNat 64 (8 * j)) v).readW (T + BitVec.ofNat 64 (8 * i)) 64 =
      if i = j then v else m.readW (T + BitVec.ofNat 64 (8 * i)) 64 := by
  by_cases h : i = j
  · subst h; simp only [↓reduceIte]; exact Mem.readW_writeW_self _ _ 8 _ (by decide)
  · simp only [h, ↓reduceIte]
    rw [Mem.readW_writeW_sep (Offset.sep T (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]

/-- The table's stores, to `T` at `p`, writable. -/
theorem rcStore_ok {s : State} {p : Reg} (hp16 : p ≠ .x16) {T : Addr} (hT : s.gpr p = T)
    (hw : ∀ i < 48, InRegions s.wr (T + BitVec.ofNat 64 (8 * i)) 8)
    (hw16 : ∀ r < 24, InRegions s.wr (T + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rcStore p 0)) s fun t => (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ t.v = s.v ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Frame [⟨T, 384⟩] s.mem t.mem ∧ RcTable t T := by
  unfold rcStore
  refine WP.mono (wp_range_flatMap (M := isa) (StInv s T) (fun k t hk h => ?_) 24 (Nat.le_refl _) s
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega_arith)⟩)
    fun t h => ⟨h.gpr, h.v, h.rd, h.wr, h.sp, h.frame,
      ⟨fun r hr => by
        obtain ⟨R, hR, hc⟩ := hw16 r hr
        rw [h.rd, h.wr]; exact ⟨R, List.mem_append_right _ hR, hc⟩, h.word⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha3.AArch64.Sha3.Vector.constant_ok (Spec.Sha3.RC k) t)
    fun t₁ ⟨k₁, v₁, x₁⟩ => ?_
  have hx : t₁.gpr .x16 = Spec.Sha3.RC k := by
    rw [x₁, VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow_RC k hk]
  have ha : t₁.gpr p + BitVec.ofNat 64 (0 + 16 * k) = T + BitVec.ofNat 64 (8 * (2 * k)) := by
    rw [k₁.gpr p hp16, h.gpr p hp16, hT]; congr 2; omega_arith
  have hb : t₁.gpr p + BitVec.ofNat 64 (0 + 16 * k + 8) = T + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [k₁.gpr p hp16, h.gpr p hp16, hT]; congr 2; omega_arith
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (str_ok (by omega_arith) ha (by rw [k₁.wr, h.wr]; exact hw _ (by omega_arith)))
    fun t₂ ⟨v₂, g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
  have hb₂ : t₂.gpr p + BitVec.ofNat 64 (0 + 16 * k + 8) = T + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [g₂]; exact hb
  refine WP.mono (str_ok (a := T + BitVec.ofNat 64 (8 * (2 * k + 1))) (by omega_arith) hb₂
    (by rw [wr₂, k₁.wr, h.wr]; exact hw _ (by omega_arith)))
    fun t₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_
  have hm : t₃.mem = (t.mem.writeW (T + BitVec.ofNat 64 (8 * (2 * k))) (Spec.Sha3.RC k)).writeW
      (T + BitVec.ofNat 64 (8 * (2 * k + 1))) (Spec.Sha3.RC k) := by
    rw [m₃, m₂, g₂, k₁.mem, hx]
  refine ⟨fun g hg => by rw [g₃, g₂, k₁.gpr g hg, h.gpr g hg], by rw [v₃, v₂, v₁, h.v],
    by rw [rd₃, rd₂, k₁.rd, h.rd], by rw [wr₃, wr₂, k₁.wr, h.wr], by rw [sp₃, sp₂, k₁.sp, h.sp], ?_,
    fun i hi => ?_⟩
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base T (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base T (by omega_arith) (by omega_arith))
  · rw [hm, word_store (by omega_arith) (by omega_arith), word_store (by omega_arith) (by omega_arith)]
    by_cases h1 : i = 2 * k + 1
    · simp only [h1, ↓reduceIte]; congr 1; omega_arith
    · simp only [h1, ↓reduceIte]
      by_cases h0 : i = 2 * k
      · simp only [h0, ↓reduceIte]; congr 1; omega_arith
      · simp only [h0, ↓reduceIte]; exact h.word i (by omega_arith)

/-- The iota step: the constant from the table, XORed into lane 0. -/
theorem iotaQ_ok {s : State} {A B : Spec.Sha3.State} (hp : CPairs s A B) {p : Reg} {rc : BitVec 64}
    (hin : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 0) 16)
    (hv : s.mem.read (s.gpr p + BitVec.ofNat 64 0) 16 = ofVDwords rc rc) :
    WP isa (.block [.ldrq .v26 p 0, .vop (.logic .eor .v0 .v0 .v26)]) s fun t => VChg allV s t ∧
      Pairs t (Proof.Sha3.outState A rc) (Proof.Sha3.outState B rc) := by
  refine wp_ldrq (by decide) rfl hin fun s1 h1 => wp_vop (d := .v0) rfl fun t h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  rw [out_word A rc hi,out_word B rc hi]
  by_cases h0 : i = 0
  · subst i
    change t.v .v0 = ofVDwords (chiWord A 0 ^^^ rc) (chiWord B 0 ^^^ rc)
    rw [h2.v,h1.get .v0,h1.v,hv]
    change s.v .v0 ^^^ ofVDwords rc rc = _
    have hp0 : s.v .v0 = ofVDwords (chiWord A 0) (chiWord B 0) := hp 0 (by decide)
    rw [hp0,pair_xor]
  · rw [ite_eq_right h0,ite_eq_right h0,h2.get (vreg i) (by
      change ¬ vreg i = vreg 0
      rw [vreg_inj i (by omega_arith) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem ofNat_ne_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases hk : k = 0
  · subst hk; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega_arith
    rw [show (BitVec.ofNat 64 k != 0) = true from bne_iff_ne.mpr this]
    simp [hk]

/-- At round `r` of the loop, from `s`. -/
structure LInv (s : State) (p : Reg) (T : Addr) (A B : Spec.Sha3.State) (r : Nat) (t : State) : Prop where
  lt : r < 24
  gpr : ∀ g, g ≠ .x16 → g ≠ p → t.gpr g = s.gpr g
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  ptr : t.gpr p = T + BitVec.ofNat 64 (16 * r)
  cnt : t.gpr .x16 = BitVec.ofNat 64 (24 - r)
  pairs : Pairs t ((List.range r).foldl Spec.Sha3.rnd A) ((List.range r).foldl Spec.Sha3.rnd B)

theorem roundsLoop_ok {core : List Instr} (hc : Core2 core) {p : Reg} (hp16 : p ≠ .x16)
    {s : State} {A B : Spec.Sha3.State} (hpr : Pairs s A B) (ht : RcTable s (s.gpr p)) :
    WP isa (roundsLoop core p) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold roundsLoop
  have hmov : isa.exec (.movz .x .x16 24 0) s = some (s.write .x .x16 (BitVec.ofNat 64 24)) := by
    simp only [isa, exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 by decide, ite_true,
      BitVec.shiftLeft_zero]
    rfl
  refine WP.seq (WP.cons hmov (WP.block_nil ?_))
  refine WP.seq (WP.mono (WP.loop (M := isa) (fun n t => ∃ r, n = 24 - r ∧ LInv s p (s.gpr p) A B r t)
    (Q := fun t => (∀ g, g ≠ .x16 → g ≠ p → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr p = s.gpr p + BitVec.ofNat 64 384 ∧
      Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B))
    (fun n t ⟨r, hn, h⟩ => ?_) 24 _ ⟨0, rfl, ?_⟩) fun t ht => ?_)
  · -- one iteration
    subst hn
    rw [WP.block_append_iff]
    refine WP.mono (hc h.pairs) fun u ⟨ku, pu⟩ => ?_
    have hpu : u.gpr p = s.gpr p + BitVec.ofNat 64 (16 * r) := by rw [ku.gpr, h.ptr]
    have hin : InRegions (u.rd ++ u.wr) (u.gpr p + BitVec.ofNat 64 0) 16 := by
      rw [ku.rd, ku.wr, h.rd, h.wr, hpu, BitVec.add_zero]; exact ht.rd r h.lt
    have hv : u.mem.read (u.gpr p + BitVec.ofNat 64 0) 16 =
        ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) := by
      rw [ku.mem, h.mem, hpu, BitVec.add_zero]; exact ht.entry h.lt
    rw [show ([.ldrq .v26 p 0, .vop (.logic .eor .v0 .v0 .v26), .addImm .x p p 16,
        .subImm .x .x16 .x16 1] : List Instr) = [.ldrq .v26 p 0, .vop (.logic .eor .v0 .v0 .v26)] ++
        ([.addImm .x p p 16] ++ [.subImm .x .x16 .x16 1]) from rfl, WP.block_append_iff]
    refine WP.mono (iotaQ_ok pu hin hv) fun u₂ ⟨c₂, p₂⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (addImm_ok (by decide)) fun u₃ ⟨v₃, m₃, rd₃, wr₃, sp₃, ptr₃, g₃⟩ =>
      WP.mono (subImm_ok (by decide)) fun t' ⟨v₄, m₄, rd₄, wr₄, sp₄, x₄, g₄⟩ => ?_
    have hcnt : t'.gpr .x16 = BitVec.ofNat 64 (24 - (r + 1)) := by
      rw [x₄, g₃ _ hp16.symm, c₂.gpr, ku.gpr, h.cnt]
      have := h.lt
      rw [show 24 - r = (24 - (r + 1)) + 1 by omega_arith, BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have hpairs : Pairs t' ((List.range (r + 1)).foldl Spec.Sha3.rnd A)
        ((List.range (r + 1)).foldl Spec.Sha3.rnd B) := by
      intro i hi
      rw [v₄, v₃]
      have := p₂ i hi
      simp only [Proof.Sha3.outState_eq] at this
      simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] using this
    have hgpr : ∀ g, g ≠ .x16 → g ≠ p → t'.gpr g = s.gpr g := fun g h1 h2 => by
      rw [g₄ g h1, g₃ g h2, c₂.gpr, ku.gpr, h.gpr g h1 h2]
    have hptr : t'.gpr p = s.gpr p + BitVec.ofNat 64 (16 * (r + 1)) := by
      rw [g₄ p hp16, ptr₃, c₂.gpr, hpu, Offset.add_add, Nat.mul_succ]
    have hmem : t'.mem = s.mem := by rw [m₄, m₃, c₂.mem, ku.mem, h.mem]
    have hrd : t'.rd = s.rd := by rw [rd₄, rd₃, c₂.rd, ku.rd, h.rd]
    have hwr : t'.wr = s.wr := by rw [wr₄, wr₃, c₂.wr, ku.wr, h.wr]
    have hsp : t'.sp = s.sp := by rw [sp₄, sp₃, c₂.sp, ku.sp, h.sp]
    show (some (t'.read .x .x16 != 0) = some false ∧ _) ∨ (some (t'.read .x .x16 != 0) = some true ∧ _)
    have hrd16 : t'.read .x .x16 = t'.gpr .x16 := rfl
    rw [hrd16, hcnt, ofNat_ne_zero (by omega_arith)]
    by_cases hl : r + 1 = 24
    · left
      refine ⟨by simp [hl], hgpr, hmem, hrd, hwr, hsp, by rw [hptr, hl], ?_⟩
      rw [hl] at hpairs
      exact hpairs
    · right
      refine ⟨by have := h.lt; simp; omega_arith, 24 - (r + 1), by have := h.lt; omega_arith, r + 1, rfl,
        ⟨by have := h.lt; omega_arith, hgpr, hmem, hrd, hwr, hsp, hptr, hcnt, hpairs⟩⟩
  · -- the invariant at the start
    refine ⟨by decide, fun g h1 _ => by simp [State.write, h1], rfl, rfl, rfl, rfl,
      by simp [State.write, hp16], by simp [State.write], fun i hi => hpr i hi⟩
  · -- restore `p`
    obtain ⟨g, m, rd, wr, sp, hptr, hpairs⟩ := ht
    refine WP.mono (subImm_ok (by decide)) fun u ⟨v₄, m₄, rd₄, wr₄, sp₄, p₄, g₄⟩ =>
      ⟨⟨fun r hr => ?_, by rw [m₄, m], by rw [rd₄, rd], by rw [wr₄, wr], by rw [sp₄, sp]⟩, ?_⟩
    · by_cases hrp : r = p
      · subst hrp; rw [p₄, hptr, BitVec.add_sub_cancel]
      · rw [g₄ r hrp, g r hr hrp]
    · intro i hi; rw [v₄]; exact hpairs i hi

end VG.Proof.Sha3.AArch64.Neon.Hw

end

end


/-! ## From `Resident.lean` -/

@[expose] public section

section

/-! The resident core uses the established two-lane Keccak proof. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- An inline paired permutation, with no custom ABI or external symbol. -/
structure Core where
  code : Prog isa
  correct : ∀ {s : State} {A B : Spec.Sha3.State}, Pairs s A B →
    VG.Proof.Sha3.AArch64.Neon.Hw.RcTable s (s.gpr .x15) →
    WP isa code s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B)

/-- Neither stream constrains the other: every input bit in both lanes is
covered, and the inline permutation leaves memory untouched. -/
theorem permute_ok {s : State} {A B : Spec.Sha3.State} (h : Pairs s A B)
    (ht : VG.Proof.Sha3.AArch64.Neon.Hw.RcTable s (s.gpr .x15)) :
    WP isa Impl.MlDsa.AArch64.Optimized.Resident.permute s fun t =>
      CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) :=
  VG.Proof.Sha3.AArch64.Neon.Hw.roundsLoop_ok VG.Proof.Sha3.AArch64.Neon.Hw.core_ok (by decide) h ht

def originalCore : Core := ⟨Impl.MlDsa.AArch64.Optimized.Resident.permute, permute_ok⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentSqueeze.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)

/-- Squeezing leaves the resident state intact; only two temporary vectors
and the scalar temporaries for an odd final word can change. -/
structure SqueezeKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r
  vec : ∀ r, r ≠ .v26 → r ≠ .v27 → t.v r = s.v r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem SqueezeKeep.refl (s : State) : SqueezeKeep s s :=
  ⟨fun _ _ _ => rfl,fun _ _ _ => rfl,rfl,rfl,rfl⟩

theorem SqueezeKeep.trans {s t u : State} (h : SqueezeKeep s t)
    (k : SqueezeKeep t u) : SqueezeKeep s u :=
  ⟨fun r h6 h7 => (k.gpr r h6 h7).trans (h.gpr r h6 h7),
   fun r h26 h27 => (k.vec r h26 h27).trans (h.vec r h26 h27),
   k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

theorem stateReg_ne : ∀ i < 25, vreg i ≠ .v26 ∧ vreg i ≠ .v27 := by decide +kernel

theorem SqueezeKeep.pairs {s t : State} {A B : Spec.Sha3.State}
    (h : SqueezeKeep s t) (hp : VG.Proof.Sha3.AArch64.Neon.Pairs s A B) :
    VG.Proof.Sha3.AArch64.Neon.Pairs t A B := by
  intro i hi
  rw [h.vec _ (stateReg_ne i hi).1 (stateReg_ne i hi).2]
  exact hp i hi

private theorem narrow64 (w : BitVec 64) : (w.setWidth 128).setWidth 64 = w := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

private theorem pair_congr {a b c d : BitVec 64} (h : a = c) (k : b = d) :
    ofVDwords a b = ofVDwords c d := by
  subst h k
  rfl

theorem trn1_dwords (x y : BitVec 128) :
    VPermOp.eval .trn1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  exact pair_congr (narrow64 _) (narrow64 _)

theorem trn2_dwords (x y : BitVec 128) :
    VPermOp.eval .trn2 .d2 x y = ofVDwords (vdword x 1) (vdword y 1) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  exact pair_congr (narrow64 _) (narrow64 _)

/-- Four instructions emit four rate words without disturbing either state. -/
theorem squeezePair_ok {s : State} {a b : Addr} {ra rb : Reg} {i : Nat}
    (hi : 2*i+1 < 25) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (hwa : InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeezePair ra rb i)) s fun t =>
      SqueezeKeep s t ∧ t.mem =
        (s.mem.write (a+BitVec.ofNat 64 (16*i)) 16
          (ofVDwords (vdword (s.v (vreg (2*i))) 0) (vdword (s.v (vreg (2*i+1))) 0))).write
        (b+BitVec.ofNat 64 (16*i)) 16
          (ofVDwords (vdword (s.v (vreg (2*i))) 1) (vdword (s.v (vreg (2*i+1))) 1)) := by
  unfold Impl.MlDsa.AArch64.Optimized.Resident.squeezePair
  refine wp_vop (d := .v26) rfl fun s1 h1 => ?_
  refine wp_vop (d := .v27) rfl fun s2 h2 => ?_
  refine wp_strq (t := .v26) (a := a+BitVec.ofNat 64 (16*i)) ⟨by omega_using [],by omega_using [hi]⟩
    (by rw [h2.gpr,h1.gpr,ha]) (by rw [h2.wr,h1.wr]; exact hwa) fun s3 h3 => ?_
  refine wp_strq (t := .v27) (a := b+BitVec.ofNat 64 (16*i)) ⟨by omega_using [],by omega_using [hi]⟩
    (by rw [h3.gpr,h2.gpr,h1.gpr,hb]) (by rw [h3.wr,h2.wr,h1.wr]; exact hwb)
    fun t h4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r _ _ => ?_,fun r h26 h27 => ?_,?_,?_,?_⟩
    · rw [h4.gpr,h3.gpr,h2.gpr,h1.gpr]
    · rw [h4.v,h3.v,h2.other r h27,h1.other r h26]
    · exact h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd))
    · exact h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr))
    · exact h4.sp.trans (h3.sp.trans (h2.sp.trans h1.sp))
  · rw [h4.mem,h3.mem,h3.v,h2.v,h2.other .v26 (by decide),h1.v,
      h2.mem,h1.mem,trn1_dwords,trn2_dwords,
      h1.other _ (stateReg_ne _ (by omega_using [hi])).1,
      h1.other _ (stateReg_ne _ hi).1]
/-- The odd final word reuses the established scalar pair-squeeze theorem. -/
theorem squeezeLast_ok {s : State} {a b : Addr} {ra rb : Reg} {i : Nat}
    (hi : i < 21) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hwa : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr a i) 8)
    (hwb : InRegions s.wr (VG.Proof.Sha3.AArch64.Neon.outAddr b i) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeezeLast ra rb i)) s fun t =>
      SqueezeKeep s t ∧ t.mem =
        (s.mem.writeW (VG.Proof.Sha3.AArch64.Neon.outAddr a i) (vdword (s.v (vreg i)) 0)).writeW
        (VG.Proof.Sha3.AArch64.Neon.outAddr b i) (vdword (s.v (vreg i)) 1) := by
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.squeeze_step hi ha hb ha6 ha7 hb6 hb7 hwa hwb) ?_
  intro t h
  exact ⟨⟨h.1.gpr,fun _ _ _ => congrFun h.1.vec _,h.1.rd,h.1.wr,h.1.sp⟩,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentRate.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- Complete 128-bit groups of one serialized SHAKE rate. -/
def RatePairs (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < n, m.read (a+BitVec.ofNat 64 (16*i)) 16 = ofVDwords A[2*i]! A[2*i+1]!

theorem squeezePairs_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 12) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n)).Disjoint ⟨b,16*n⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range n).flatMap
      (Impl.MlDsa.AArch64.Optimized.Resident.squeezePair ra rb))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RatePairs t.mem a n A ∧ RatePairs t.mem b n B ∧
        Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega_using [hi]) (by omega_using [hn, hi])
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem a k A ∧ RatePairs t.mem b k B ∧
      Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,fun _ h => by omega,Frame.refl _ _⟩)
    (fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2.1,h.2.2.2⟩)
  have hpt := ht.1.pairs hp
  refine WP.mono (squeezePair_ok (by omega_using [hn, hk])
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    (by rw [ht.1.wr]; exact hwa k hk) (by rw [ht.1.wr]; exact hwb k hk)) ?_
  intro u hu
  have hm : u.mem = (t.mem.write (a+BitVec.ofNat 64 (16*k)) 16 (ofVDwords A[2*k]! A[2*k+1]!)).write
      (b+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega_using [hn, hk]),hpt _ (by omega_using [hn, hk]),vdword_ofVDwords_0,vdword_ofVDwords_0,
      vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_,?_⟩
  · intro i hi
    rw [hm,Mem.read_write_sep (hd.sep (ac i (by omega_using [hk, hi])) (bc k hk)) (by decide)]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega_using [he]) (by omega_using [hn, hk, hi]) (by omega_using [hn, hk])) (by decide)]
      exact ht.2.1 i (by omega_using [hi, he])
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega_using [he]) (by omega_using [hn, hk, hi]) (by omega_using [hn, hk])) (by decide),
        Mem.read_write_sep (hd.symm.sep (bc i (by omega_using [hk, hi])) (ac k hk)) (by decide)]
      exact ht.2.2.1 i (by omega_using [hi, he])
  · rw [hm]
    exact (ht.2.2.2.write (by simp) _ (ac k hk)).write (by simp) _ (bc k hk)
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- An odd-word rate: complete vector groups and its final scalar word. -/
def RateBlock (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  RatePairs m a n A ∧ m.readW (a+BitVec.ofNat 64 (16*n)) 64 = A[2*n]!

/-- Vector serialization of either SHAKE rate, including the odd final word. -/
theorem squeeze_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb)) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RateBlock t.mem a n A ∧ RateBlock t.mem b n B ∧
        Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega_using [hi]) (by omega_using [hn, hi])
  have al : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base a (by omega_using []) (by omega_using [hn])
  have bl : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base b (by omega_using []) (by omega_using [hn])
  have haSub : (Region.mk a (16*n)).Sub ⟨a,16*n+8⟩ := by
    simpa using Offset.sub_base a (d := 0) (n := 16*n) (k := 16*n+8) (by omega_using [])
  have hbSub : (Region.mk b (16*n)).Sub ⟨b,16*n+8⟩ := by
    simpa using Offset.sub_base b (d := 0) (n := 16*n) (k := 16*n+8) (by omega_using [])
  unfold Impl.MlDsa.AArch64.Optimized.Resident.squeeze
  rw [show (2*n+1)/2=n by omega_using [],show (2*n+1)%2=1 by omega_using [],ite_eq_left rfl,
    show 2*n+1-1=2*n by omega_using [],WP.block_append_iff]
  refine WP.mono (squeezePairs_ok (by omega_using [hn]) hp ha hb ha6 ha7 hb6 hb7
    ((hd.sub_left haSub).sub_right hbSub) hwa hwb) ?_
  intro t ht
  refine WP.mono (squeezeLast_ok (i := 2*n) (by omega_using [hn])
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    ha6 ha7 hb6 hb7
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []] using hwal)
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []] using hwbl)) ?_
  intro u hu
  have hm : u.mem = (t.mem.writeW (a+BitVec.ofNat 64 (16*n)) A[2*n]!).writeW
      (b+BitVec.ofNat 64 (16*n)) B[2*n]! := by
    rw [hu.2,ht.2.1 _ (by omega_using [hn]),vdword_ofVDwords_0,vdword_ofVDwords_1]
    simp only [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega_using []]
  refine ⟨ht.1.trans hu.1,hu.1.pairs ht.2.1,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (hd.sep (ac i hi) bl) (by decide),
      Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega_using [hi]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
    exact ht.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_sep (hd.sep al bl) (by decide),Mem.readW_writeW_self64]
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega_using [hi]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide),
      Mem.read_write_sep (hd.symm.sep (bc i hi) al) (by decide)]
    exact ht.2.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_self64]
  · rw [hm]
    have hf : Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem :=
      ht.2.2.2.2.sub (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_,by simp,haSub⟩
        · exact ⟨_,by simp,hbSub⟩)
    exact (hf.writeW (by simp) _ al).writeW (by simp) _ bl
end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

end

/-! ## From `ResidentStep.lean` -/

@[expose] public section

/-! ## From `ResidentCounter.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- The three public loop updates leave all resident lanes and memory intact. -/
theorem advance_ok {s : State} {ra rb : Reg} {rate : Nat}
    (hrate : rate < 4096) (hab : ra ≠ rb)
    (ha28 : ra ≠ .x28) (hb28 : rb ≠ .x28) :
    WP isa (.block ([.addImm .x ra ra rate,.addImm .x rb rb rate,
      .subImm .x .x28 .x28 1] : List Instr)) s fun t =>
      t.gpr ra = s.gpr ra + BitVec.ofNat 64 rate ∧
      t.gpr rb = s.gpr rb + BitVec.ofNat 64 rate ∧
      t.gpr .x28 = s.gpr .x28 - 1 ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s1 := s.write .x ra (s.gpr ra + BitVec.ofNat 64 rate)
  let s2 := s1.write .x rb (s1.gpr rb + BitVec.ofNat 64 rate)
  let s3 := s2.write .x .x28 (s2.gpr .x28 - 1)
  refine WP.block_cons_iff.mpr ⟨s1,by simp [isa,exec,hrate,State.read,s1],?_⟩
  refine WP.block_cons_iff.mpr ⟨s2,by simp [isa,exec,hrate,State.read,s2],?_⟩
  refine WP.block_cons_iff.mpr ⟨s3,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [s3,s2,s1]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [ha28,hb28,hab,Ne.symm hab,Ne.symm ha28,Ne.symm hb28,ite_false,ite_true,true_and]
  constructor
  · intro r hra hrb hr28
    simp only [hra,hrb,hr28,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64

/-- Later output blocks cannot change an already serialized rate block. -/
theorem RateBlock.keep {m m' : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    {rs : List Region} (h : RateBlock m a n A) (hn : n ≤ 10)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk a (16*n+8)).Disjoint r) :
    RateBlock m' a n A := by
  constructor
  · intro i hi
    rw [hf.read (Offset.contains_base a (by omega_using [hi]) (by omega_using [hn, hi])) hd (by decide)]
    exact h.1 i hi
  · rw [hf.readW (Offset.contains_base a (by omega_using []) (by omega_using [hn])) hd (by decide)]
    exact h.2

def permuted (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | j+1 => Spec.Sha3.keccakF (permuted A j)

/-- Output of the first `j` paired permutations. -/
def StreamOutput (m : Mem) (a : Addr) (n j : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < j, RateBlock m (a+BitVec.ofNat 64 ((16*n+8)*i)) n
    (permuted A (i+1))

/-- Adjacent bounded output blocks have disjoint addresses even if the base
address itself wraps. -/
theorem block_disjoint {a : Addr} {n i j : Nat} (hn : n ≤ 10)
    (hij : i < j) (hj : j < 65536) :
    (Region.mk (a+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Disjoint
      ⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩ := by
  have hij' := Nat.mul_le_mul_left (16*n+8) hij
  have hiBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega_using [hn]) (show i+1 ≤ 65536 by omega_using [hij, hj])
  have hjBound := Nat.mul_le_mul (show 16*n+8 ≤ 168 by omega_using [hn]) (show j+1 ≤ 65536 by omega_using [hj])
  simp only [Nat.mul_add,Nat.mul_one] at hij' hiBound hjBound
  exact Offset.disjoint a (Or.inl (by omega)) (by omega_using [hiBound]) (by omega_using [hjBound])

/-- Appending a block preserves every earlier block in both streams. -/
theorem StreamOutput.append {m m' : Mem} {a b : Addr} {n j blocks : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hj : j < blocks) (hblocks : blocks ≤ 65536)
    (hd : (Region.mk a ((16*n+8)*blocks)).Disjoint ⟨b,(16*n+8)*blocks⟩)
    (ha : StreamOutput m a n j A) (hb : StreamOutput m b n j B)
    (hnewa : RateBlock m' (a+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted A (j+1)))
    (hnewb : RateBlock m' (b+BitVec.ofNat 64 ((16*n+8)*j)) n (permuted B (j+1)))
    (hf : Frame [⟨a+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩,
      ⟨b+BitVec.ofNat 64 ((16*n+8)*j),16*n+8⟩] m m') :
    StreamOutput m' a n (j+1) A ∧ StreamOutput m' b n (j+1) B := by
  have sub (p : Addr) (i : Nat) (hi : i < blocks) :
      (Region.mk (p+BitVec.ofNat 64 ((16*n+8)*i)) (16*n+8)).Sub
        ⟨p,(16*n+8)*blocks⟩ := by
    apply Offset.sub_base
    have h := Nat.mul_le_mul_left (16*n+8) hi
    simpa only [Nat.mul_succ] using h
  constructor
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewa
    · refine (ha i (by omega_using [hi, he])).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact block_disjoint hn (by omega_using [hi, he]) (by omega_using [hj, hblocks])
      · exact (hd.sub_left (sub a i (by omega_using [hj, hi]))).sub_right (sub b j hj)
  · intro i hi
    by_cases he : i = j
    · simpa only [he] using hnewb
    · refine (hb i (by omega_using [hi, he])).keep hn hf ?_
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact (hd.symm.sub_left (sub b i (by omega_using [hj, hi]))).sub_right (sub a j hj)
      · exact block_disjoint hn (by omega_using [hi, he]) (by omega_using [hj, hblocks])

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

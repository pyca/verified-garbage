module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.RoundLoop
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

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
    rw [hf.readW (r := ⟨T, 384⟩) (Offset.contains_base T (by omega) (by omega)) hd (by decide)]
    exact h.word k hk⟩

/-- Entry `r` of the table, as the value `ldrq` loads. -/
theorem RcTable.entry {s : State} {T : Addr} (h : RcTable s T) {r : Nat} (hr : r < 24) :
    s.mem.read (T + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) := by
  rw [read16_dwords, Offset.add_add, show 16 * r = 8 * (2 * r) by omega, h.word _ (by omega),
    show 8 * (2 * r) + 8 = 8 * (2 * r + 1) by omega, h.word _ (by omega)]
  congr 2 <;> omega

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
    rw [Mem.readW_writeW_sep (Offset.sep T (by omega) (by omega) (by omega)) (by decide)]

/-- The table's stores, to `T` at `p`, writable. -/
theorem rcStore_ok {s : State} {p : Reg} (hp16 : p ≠ .x16) {T : Addr} (hT : s.gpr p = T)
    (hw : ∀ i < 48, InRegions s.wr (T + BitVec.ofNat 64 (8 * i)) 8)
    (hw16 : ∀ r < 24, InRegions s.wr (T + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rcStore p 0)) s fun t => (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ t.v = s.v ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Frame [⟨T, 384⟩] s.mem t.mem ∧ RcTable t T := by
  unfold rcStore
  refine WP.mono (wp_range_flatMap (M := isa) (StInv s T) (fun k t hk h => ?_) 24 (Nat.le_refl _) s
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩)
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
    rw [k₁.gpr p hp16, h.gpr p hp16, hT]; congr 2; omega
  have hb : t₁.gpr p + BitVec.ofNat 64 (0 + 16 * k + 8) = T + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [k₁.gpr p hp16, h.gpr p hp16, hT]; congr 2; omega
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (str_ok (by omega) ha (by rw [k₁.wr, h.wr]; exact hw _ (by omega)))
    fun t₂ ⟨v₂, g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
  have hb₂ : t₂.gpr p + BitVec.ofNat 64 (0 + 16 * k + 8) = T + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [g₂]; exact hb
  refine WP.mono (str_ok (a := T + BitVec.ofNat 64 (8 * (2 * k + 1))) (by omega) hb₂
    (by rw [wr₂, k₁.wr, h.wr]; exact hw _ (by omega)))
    fun t₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_
  have hm : t₃.mem = (t.mem.writeW (T + BitVec.ofNat 64 (8 * (2 * k))) (Spec.Sha3.RC k)).writeW
      (T + BitVec.ofNat 64 (8 * (2 * k + 1))) (Spec.Sha3.RC k) := by
    rw [m₃, m₂, g₂, k₁.mem, hx]
  refine ⟨fun g hg => by rw [g₃, g₂, k₁.gpr g hg, h.gpr g hg], by rw [v₃, v₂, v₁, h.v],
    by rw [rd₃, rd₂, k₁.rd, h.rd], by rw [wr₃, wr₂, k₁.wr, h.wr], by rw [sp₃, sp₂, k₁.sp, h.sp], ?_,
    fun i hi => ?_⟩
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base T (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base T (by omega) (by omega))
  · rw [hm, word_store (by omega) (by omega), word_store (by omega) (by omega)]
    by_cases h1 : i = 2 * k + 1
    · simp only [h1, ↓reduceIte]; congr 1; omega
    · simp only [h1, ↓reduceIte]
      by_cases h0 : i = 2 * k
      · simp only [h0, ↓reduceIte]; congr 1; omega
      · simp only [h0, ↓reduceIte]; exact h.word i (by omega)

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
      rw [vreg_inj i (by omega) 0 (by decide)]; exact h0),h1.get (vreg i)
      ((show ∀ i < 25,vreg i ≠ .v26 by decide) i hi)]
    exact hp i hi

theorem ofNat_ne_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases hk : k = 0
  · subst hk; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
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
      rw [show 24 - r = (24 - (r + 1)) + 1 by omega, BitVec.ofNat_add]
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
    rw [hrd16, hcnt, ofNat_ne_zero (by omega)]
    by_cases hl : r + 1 = 24
    · left
      refine ⟨by simp [hl], hgpr, hmem, hrd, hwr, hsp, by rw [hptr, hl], ?_⟩
      rw [hl] at hpairs
      exact hpairs
    · right
      refine ⟨by have := h.lt; simp; omega, 24 - (r + 1), by have := h.lt; omega, r + 1, rfl,
        ⟨by have := h.lt; omega, hgpr, hmem, hrd, hwr, hsp, hptr, hcnt, hpairs⟩⟩
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

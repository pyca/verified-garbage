module

import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Sample.Ball
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
meta import VerifiedGarbage.Proof.MlDsa.Sample.Ball
meta import VerifiedGarbage.Proof.MlDsa.Sample.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
meta import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.X86_64.Sample.Ball`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Sample.BallLoop`, which only this module used -/

section

/-!
# ML-DSA on x86-64: the loops of `vg_mldsa_sample_in_ball`

The polynomial `c` is kept in memory as the words that represent its
coefficients modulo `q` (`CStored`); the first loop zeroes it (`bZero_ok`),
and an iteration of the second does what `bStep` does to it and to `i` (in
`rdi`), with the sign bits not yet used in `r9` (`bBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt IPoly n)
open VG.Proof.MlDsa (coeffAt)
open VG.Impl.MlKem.X86_64 (at_)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (s₀ : State) (aP : Addr) (k : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (4 * k)
  rax : s.gpr .rax = 0
  keep : Keep [.rax, .rdi, .rcx] s₀ s
  frame : Frame [pR aP] s₀.mem s.mem
  zero : ∀ j < k, coeffAt s.mem aP j = 0

theorem zStep_ok (s : State) {a : Addr} (ha : s.gpr .rdi = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr .rax).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 4 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]
  rfl

/-- The zeroing loop: the 256 coefficients at `rbp` set to 0. -/
theorem bZero_ok (s₀ : State) {aP : Addr} (hbp : s₀.gpr .rbp = aP) (hw : pR aP ∈ s₀.wr) :
    WP isa bZero s₀ fun s => Keep [.rax, .rdi, .rcx] s₀ s ∧ Frame [pR aP] s₀.mem s.mem ∧
      CStored s.mem aP (Vector.replicate n 0) := by
  refine WP.seq (WP.mono (WP.keep [.rax, .rdi] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rax = 0 ∧
      s.gpr .rdi = aP) (by xrun [hbp]) (by decide)) fun s1 ⟨⟨hm1, hax, hdi⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s1.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  refine wp_countdown (N := 256) (by decide) (by decide) (ZAt s₀ aP) (fun k hk s hI _ => ?_)
    (fun s h => ⟨h.keep, h.frame, fun j hj => ?_⟩)
    ⟨by rw [k2.gpr (by decide), hdi]; simp, by rw [k2.gpr (by decide), hax], (k1.trans k2).mono (by simp),
      by rw [hm2, hm1]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ hcx
  · have ha : s.gpr .rdi = coeffAddr aP k := by rw [hI.rdi]
    refine WP.mono (zStep_ok s ha (by rw [hI.keep.2.2]; exact ⟨_, hw, coeff_contains _ hk⟩))
      fun s' ⟨⟨hm, hdi', hcx', hz⟩, k'⟩ => ⟨⟨?_, by rw [k'.gpr (by decide), hI.rax], hI.keep.trans k' |>.mono (by simp),
        ?_, fun j hj => ?_⟩, hcx', hz⟩
    · rw [hdi', hI.rdi, offAdd, Nat.mul_succ]
    · rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)
    · rw [hm, coeffAt_writeW _ _ (by omega_arith) hk, hI.rax]
      by_cases e : k = j
      · rw [ifT e]; rfl
      · rw [ifF e]; exact hI.zero j (by omega_arith)
  · rw [h.zero j hj, getElem!_pos _ j (by simp only [n]; omega_arith), Vector.getElem_replicate]
    rfl

/-! ## Setting a coefficient -/

theorem and1_beq (x : BitVec 64) : ((x &&& 1) == 0) = !x.getLsbD 0 := by
  have h1 : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
    by_cases h : x.toNat % 2 = 1 <;> simp [h]
  rw [h2]
  by_cases h : x.toNat % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega_arith
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h1]; simp; omega_arith

theorem ea_cJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    s.ea cJ = coeffAddr aP j := by
  simp only [State.ea, cJ, hbp, hax]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega_arith

theorem bSet1_ok (s : State) {a b : Addr} (hb : s.ea cJ = b) (ha : s.ea aJ = a)
    (hr : InRegions (s.rd ++ s.wr) b 4) (hw : InRegions s.wr a 4) :
    WP isa (.block [.mov32 .rdx (.mem cJ), .store32 aJ .rdx, .alu .test .r9 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a (s.mem.readW b 32) ∧ s'.zf = some ((s.gpr .r9 &&& 1) == 0) ∧
        s'.gpr .r9 = s.gpr .r9) ∧ Keep [.rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have ha' : (s.setReg .rdx (BitVec.setWidth 64 (s.mem.readW b 32))).ea aJ = a := by
    rw [← ha]; rfl
  xrun [hb, hr, hw, ha', sw32_64]

theorem bSet3_ok (s : State) {b : Addr} (hb : s.ea cJ = b) (hw : InRegions s.wr b 4) :
    WP isa (.block [.store32 cJ .rdx, .shift .shr .r9 1, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW b ((s.gpr .rdx).setWidth 32) ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧
        s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.r9, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hb, hw]

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) : (if b then (qImm - 1 : BitVec 32) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

theorem movRdx_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' => (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = v) ∧
      Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sw32_64]

/-- The word of the sign `b`. -/
theorem bSign_ok (s : State) (b : Bool) (hz : s.zf = some (!b)) :
    WP isa (.ite .e (.block [.mov32 .rdx (.imm 1)]) (.block [.mov32 .rdx (.imm (qImm - 1))])) s fun s' =>
      (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = (if b then qImm - 1 else 1)) ∧ Keep [.rdx] s s' := by
  cases b
  · exact WP.ite true hz (fun _ => movRdx_ok s 1) (fun h => absurd h (by decide))
  · exact WP.ite false hz (fun h => absurd h (by decide)) (fun _ => movRdx_ok s (qImm - 1))

/-- `c[i] ← c[j]`, `c[j] ← ±1` (with the sign bit 0 of `r9`), `i` incremented. -/
theorem bSet_ok (s : State) {aP : Addr} {c : IPoly} {i j : Nat} (hij : j ≤ i) (hi : i < 256)
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (hw : pR aP ∈ s.wr) (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) :
    WP isa bSet s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (i + 1) ∧
      CStored s'.mem aP ((c.set! i c[j]!).set! j (if (s.gpr .r9).getLsbD 0 then -1 else 1)) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧ Keep [.rdx, .r9, .rdi] s s' := by
  refine WP.seq (WP.mono (bSet1_ok s (ea_cJ s hbp hax) (ea_aJ s hbp hdi) ⟨_, hrd, coeff_contains _ (by omega_arith)⟩
    ⟨_, hw, coeff_contains _ hi⟩) fun s1 ⟨⟨hm1, hz1, h91⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (bSign_ok s1 ((s.gpr .r9).getLsbD 0) (by rw [hz1, and1_beq]))
    fun s2 ⟨⟨hm2, hdx2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (bSet3_ok s2 (b := coeffAddr aP j) (ea_cJ s2 (by rw [k12.gpr (by decide), hbp])
    (by rw [k12.gpr (by decide), hax])) (by rw [k12.2.2]; exact ⟨_, hw, coeff_contains _ (by omega_arith)⟩))
    fun s3 ⟨⟨hm3, h93, hdi3⟩, k3⟩ => ⟨?_, fun k hk => ?_, ?_, ?_, (k12.trans k3).mono (by simp)⟩
  · rw [hdi3, k12.gpr (by decide), hdi]; exact ofNat64_succ (by omega_arith)
  · rw [hm3, hm2, hm1, hdx2, coeffAt_writeW _ _ hk (by omega_arith), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega_arith), ipoly_set!_get _ _ (by simp only [n]; omega_arith)]
    by_cases ejk : j = k
    · subst ejk; rw [ifT rfl, ifT rfl, sgn_word]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : i = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, hst j (by omega_arith)]
      · rw [ifF eik, ifF eik]; exact hst k hk
  · rw [hm3, hm2, hm1]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by omega_arith))
  · rw [h93, k2.gpr (by decide), h91]

/-! ## An iteration -/

theorem bLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) s fun s' =>
      (s'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < (s.mem (s.gpr .rsi)).toNat)) ∧ s'.mem = s.mem ∧
        s'.gpr .rdi = s.gpr .rdi) ∧ Keep [.rax, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have e : BitVec.setWidth 64 (s.mem (s.gpr .rsi)) = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth64_8, BitVec.toNat_ofNat]; have := (s.mem (s.gpr .rsi)).isLt; omega_arith
  xrun [h0, e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .rsi)).isLt; omega_arith)]

/-- The try of the byte at `rsi`, if `i < 256`. -/
theorem bMid_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false)
    (hcf : s.cf = some (decide (i < 256))) :
    WP isa (.ite .b bTry (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      Keep [.rax, .rdx, .r9, .rdi] s s' := by
  refine WP.ite (decide (i < 256)) hcf (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have hl : (s.gpr .rdi).toNat = i := by rw [hdi, ofNat64_toNat (by omega_arith)]
    refine WP.seq (WP.mono (bLoad_ok s h0) fun s1 ⟨⟨hax, hcf1, hm1, hdi1⟩, k1⟩ => ?_)
    rw [hl] at hcf1
    refine WP.ite (decide (i < (s.mem (s.gpr .rsi)).toNat)) hcf1 (fun hj => ?_) (fun hj => ?_)
    · simp only [decide_eq_true_eq] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifT hj]
      rw [e]
      exact WP.block_nil ⟨by rw [hdi1, hdi], by rw [hm1]; exact hst, by rw [hm1]; exact Frame.refl _ _,
        by rw [ifT rfl, k1.gpr (by decide)], k1.mono (by simp)⟩
    · simp only [decide_eq_false_iff_not] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) =
          ((c.set! i c[(s.mem (s.gpr .rsi)).toNat]!).set! (s.mem (s.gpr .rsi)).toNat
            (if h.getD (i + τ - 256) false then -1 else 1), i + 1) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifF hj]
      rw [e, ← hsg hb]
      have h91 : s1.gpr .r9 = s.gpr .r9 := k1.gpr (by decide)
      refine WP.mono (bSet_ok s1 (aP := aP) (c := c) (by omega_arith) hb (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hax
        (by rw [k1.2.2]; exact hw) (by rw [k1.2.1, k1.2.2]; exact hrd) (by rw [hm1]; exact hst))
        fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ⟨hdi2, by rw [h91] at hst2; exact hst2,
          by rw [← hm1]; exact hf2, by rw [ifF (by omega_arith), h92, h91], (k1.trans k2).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
      unfold bStep; rw [ifF (show ¬ (c, i).2 < n from hb)]
    rw [e]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, by rw [ifT rfl], Keep.refl _ _⟩

/-- An iteration: what `bStep` does to the polynomial and `i`. -/
theorem bBody_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false) :
    WP isa bBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r9, .rdi, .rsi, .rcx] s s' := by
  refine WP.seq (WP.mono (cmpRdi_ok s) fun s1 ⟨hcf1, hm1, hg1, hrd1, hwr1⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg1], hrd1, hwr1⟩
  refine WP.seq (WP.mono (bMid_ok s1 (aP := aP) (τ := τ) (h := h) (c := c) (by rw [hg1, hbp]) (by rw [hg1, hdi]) hi
    (by rw [hwr1]; exact hw) (by rw [hrd1, hwr1]; exact hrd) (by rw [hm1]; exact hst)
    (by rw [hrd1, hwr1, hg1]; exact h0) (by rw [hg1]; exact hsg)
    (by rw [hcf1, hdi, ofNat64_toNat (by omega_arith)])) fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ?_)
  rw [hm1, hg1] at hdi2 hst2 h92
  rw [hm1] at hf2
  refine WP.mono (step_ok s2 1) fun s3 ⟨⟨hsi3, hcx3, hz3, hm3⟩, k3⟩ => ?_
  have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hg1]
  have hcx2 : s2.gpr .rcx = s.gpr .rcx := by rw [k2.gpr (by decide), hg1]
  exact ⟨by rw [k3.gpr (by decide), hdi2], by rw [hm3]; exact hst2, by rw [hm3]; exact hf2,
    by rw [k3.gpr (by decide), h92], by rw [hsi3, hsi2, sx1'], by rw [hcx3, hcx2], by rw [hz3, hcx2],
    ((k1.trans k2).trans k3).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample

end

end


/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(c̃, 272)` (`J6`), the zeroing of `c`, and the loop over the 264 bytes after
the sign bits, iteration `t` of which starts from `BAt σ t`: with the
polynomial and `i` that `bFold` computes from the first `t` of them, and the
sign bits not yet used in `r9` (`W σ`, the first 8 bytes as a `u64`, shifted
right once per coefficient set).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n toRq)
open VG.Proof.MlDsa (PolyIs ballParams)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `edx`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .rdx).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = rdi, len = rsi, tau = edx, c = rcx, scratch = r8) -> eax`,
with 16 bytes of stack below `rsp`. -/
def sbK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .rcx), ⟨s.gpr .r8, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .rcx)) ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .r8, 2048⟩ ∧
    (pR (s.gpr .rcx)).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint ⟨s.gpr .r8, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rcx)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r8, 2048⟩ ∧ (s.gpr .r8).toNat + 2048 ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat, tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .rcx) (toRq (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat = bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat

theorem readW64_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 64) :
    (m.readW a 64).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (j := k / 8) (by omega_arith), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega_arith, decide_true, Bool.true_and, hk]
  congr 1; omega_arith

/-- The `u64` at `p`, from the bytes there. -/
theorem readW_leNat (m : Mem) (p : Addr) (L : List Byte) (h : ∀ k < 8, m (p + BitVec.ofNat 64 k) = L.getD k 0) :
    m.readW p 64 = BitVec.ofNat 64 (leNat (L.take 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [readW64_getLsbD m p hk, h _ (by omega_arith), BitVec.getLsbD_ofNat, testBit_leNat, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega_arith)]
  simp [hk]

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega_arith

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .rdi, (σ.gpr .rsi).toNat, σ.gpr .r8, σ.gpr .rcx, BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32)⟩

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - tauOf σ

/-- The sign bits, as a `u64`. -/
abbrev W (σ : State) : BitVec 64 := BitVec.ofNat 64 (leNat ((X σ).take 8))

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (tauOf σ) (signs (X σ)) (Vector.replicate n 0, i0 σ) (((X σ).drop 8).take t)

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .rsi).toNat ≤ 64 ∧ 39 ≤ tauOf σ ∧ tauOf σ ≤ 60 :=
  ballParams_le hp.2.2.2.2.2.2.2.2.2.2.2.2

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.1,
    by show (σ.gpr .rsi).toNat < 2 ^ 64; have := (params hp).1; omega_arith⟩

theorem pro_ok : WP isa (.block (pro .r8 .rcx (.reg .rdx) (.reg .rsi))) σ (J0 (spOf σ) σ) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spOf σ).at' 2024) (σ.gpr .rbx)).writeW ((spOf σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spOf σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rcx ∧
        s.gpr .r12 = BitVec.setWidth 64 ((σ.gpr .rdx).setWidth 32) ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = σ.gpr .rsi)
    (by unfold pro; xrun [inScrσ (spOk hp) (a := 2024) (n := 8) (by omega_arith),
      inScrσ (spOk hp) (a := 2032) (n := 8) (by omega_arith), inScrσ (spOk hp) (a := 2040) (n := 8) (by omega_arith)])
    (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, hcx, h8⟩, k⟩ =>
      pro_J0 hm hbx hbp h12 hcx (by rw [h8]; simp) k

omit hp in
theorem X_length : (X σ).length = 272 := H_length _ _

/-! ## The zeroing, and the setup of the loop -/

/-- After the zeroing. -/
structure ZDone (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (σ.gpr .rcx) (Vector.replicate n 0)

theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa bZero s (ZDone σ) := by
  have hp' := spOk hp
  refine WP.mono (bZero_ok s h.env.rbp (by rw [h.env.wr, hp.2.1]; simp)) fun s' ⟨k, hf, hst⟩ => ?_
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  have k' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := k.mono (by simp)
  refine ⟨⟨k'.2.1.trans h.env.rd, k'.2.2.trans h.env.wr, by rw [k'.gpr (by decide), h.env.rbx],
    by rw [k'.gpr (by decide), h.env.rbp], by rw [k'.gpr (by decide), h.env.r12],
    by rw [k'.gpr (by decide), h.env.rsp], fun r hr => by rw [k'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega_arith) (by omega_arith), hsv 2032 (by omega_arith) (by omega_arith), hsv 2040 (by omega_arith) (by omega_arith)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩, ?_, hst⟩
  rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 272) (by omega_arith)).symm) (by omega_arith), h.out]
  exact (H_eq _ _).symm

/-- At the start of iteration `t`. -/
structure BAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  rsi : s.gpr .rsi = (spOf σ).at' 848 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (St σ t).2
  r9 : s.gpr .r9 = W σ >>> ((St σ t).2 - i0 σ)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (264 - t)
  st : CStored s.mem (σ.gpr .rcx) (St σ t).1

omit hp in
theorem out_getD {s : State} (hout : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ) {j : Nat} (hj : j < 272) :
    s.mem ((spOf σ).at' 840 + BitVec.ofNat 64 j) = (X σ).getD j 0 := by
  have := congrArg (fun L => L.getD j 0) hout
  rw [MlKem.bytesAt_getD _ _ hj] at this
  exact this

theorem setup_ok {s : State} (h : ZDone σ s) :
    WP isa (.block bSetup) s fun s1 => WP isa (.block [.mov32 .rcx (.imm 264)]) s1 (BAt σ 0) := by
  have hp' := spOk hp
  have ht := (params hp).2
  refine (WP.mono (WP.keep [.r9, .rdi, .rsi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .r9 = s.mem.readW ((spOf σ).at' 840) 64 ∧ s'.gpr .rdi = BitVec.ofNat 64 (i0 σ) ∧
      s'.gpr .rsi = (spOf σ).at' 848) (by
        unfold bSetup
        xrun [h.env.rbx, h.env.r12, inScrRd hp' h.env (a := 840) (n := 8) (by omega_arith), sx840, sw32_64,
          show BitVec.signExtend 64 (848 : BitVec 32) = BitVec.ofNat 64 848 by decide]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, show (256 : BitVec 32).toNat = 256 from rfl]
        have := ((σ.gpr .rdx).setWidth 32).isLt
        simp only [i0, tauOf] at ht ⊢
        omega_arith) (by decide)) fun s1 ⟨⟨hm1, h91, hdi1, hsi1⟩, k1⟩ => ?_)
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 264)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  have he1 := h.env.keep hm1 (k1.mono (by decide))
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨he1.keep hm2 (k2.mono (by decide)), by rw [hm2, hm1]; exact h.out,
    by rw [k2.gpr (by decide), hsi1]; simp, by rw [k2.gpr (by decide), hdi1, hSt], ?_, hcx,
    by rw [hm2, hm1, hSt]; exact h.st⟩
  rw [k2.gpr (by decide), h91, hSt, Nat.sub_self, BitVec.ushiftRight_zero]
  exact readW_leNat _ _ _ fun k hk => out_getD h.out (by omega_arith)

/-! ## The loop -/

omit hp in
theorem St_le (t : Nat) : (St σ t).2 ≤ 256 := bFold_le (by simp) _

omit hp in
theorem St_ge (t : Nat) : i0 σ ≤ (St σ t).2 :=
  bFold_ge (τ := tauOf σ) (h := signs (X σ)) (Vector.replicate n 0, i0 σ) _

omit hp in
theorem take_succ'' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The sign bit of `i`. -/
theorem sign_bit {i : Nat} (hi0 : i0 σ ≤ i) (hi : i < 256) :
    (W σ >>> (i - i0 σ)).getLsbD 0 = (signs (X σ)).getD (i + tauOf σ - 256) false := by
  have ht := (params hp).2
  simp only [i0] at hi0
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, signs_getD, BitVec.getLsbD_ofNat,
    show i - (256 - tauOf σ) = i + tauOf σ - 256 by omega_arith,
    decide_eq_true (show i + tauOf σ - 256 < 64 by omega_arith), Bool.true_and]

/-- An iteration, from `BAt`. -/
theorem bat_step {t : Nat} {s : State} (ht : t < 264) (h : BAt σ t s) :
    WP isa bBody s fun s' => BAt σ (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (264 - t) - 1 == 0) := by
  have hp' := spOk hp
  have hw : pR (σ.gpr .rcx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hle := St_le (σ := σ) t
  have hge := St_ge (σ := σ) t
  refine WP.mono (bBody_ok s (τ := tauOf σ) (h := signs (X σ)) (c := (St σ t).1) (aP := σ.gpr .rcx) h.env.rbp h.rdi
    hle hw (List.mem_append_right _ hw) h.st
    (by rw [h.rsi, at_add]; exact inScrRd hp' h.env (by omega_arith))
    (fun hi => by rw [h.r9]; exact sign_bit hp hge hi)) fun s' ⟨hdi, hst, hf, h9, hsi, hcx, hz, hk⟩ => ?_
  have hb : s.mem (s.gpr .rsi) = ((X σ).drop 8).getD t 0 := by
    rw [h.rsi, at_add, show 848 + t = 840 + (8 + t) by omega_arith, ← at_add, out_getD h.out (by omega_arith),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ht1 : St σ (t + 1) = bStep (tauOf σ) (signs (X σ)) (St σ t) (((X σ).drop 8).getD t 0) := by
    simp only [St]
    rw [take_succ'' _ (by rw [List.length_drop, X_length]; omega_arith), bFold_snoc]
  rw [hb, ← ht1] at hdi hst h9
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ).at' k) 64 = s.mem.readW ((spOf σ).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp], fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega_arith) (by omega_arith), hsv 2032 (by omega_arith) (by omega_arith), hsv 2040 (by omega_arith) (by omega_arith)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 272) (by omega_arith)).symm)
      (by omega_arith)]; exact h.out, by rw [hsi, h.rsi, offAdd], hdi, ?_,
    by rw [hcx, h.rcx, ofNat64_pred (by omega_arith) (by omega_arith)]; rfl, hst⟩, by rw [hz, h.rcx]⟩
  rw [h9, h.r9]
  have hs : (St σ (t + 1)).2 = (St σ t).2 ∨ (St σ (t + 1)).2 = (St σ t).2 + 1 := by
    rw [ht1]; unfold bStep; split
    · split
      · exact .inl rfl
      · exact .inr rfl
    · exact .inl rfl
  rcases hs with e | e
  · rw [ifT e, e]
  · rw [ifF (by omega_arith), e, ← BitVec.shiftRight_add, show (St σ t).2 + 1 - i0 σ = (St σ t).2 - i0 σ + 1 by omega_arith]

theorem loop_ok {s : State} (h : ZDone σ s) : WP isa bLoop s (BAt σ 264) :=
  WP.seq (WP.mono (setup_ok hp h) fun _ h1 => WP.seq (WP.mono h1 fun _ h2 =>
    wp_countdown (N := 264) (by decide) (by decide) (BAt σ) (fun t ht s hI _ => WP.mono (bat_step hp ht hI)
      fun s' ⟨hI', hz⟩ => ⟨hI', by rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega_arith) (by omega_arith)]; rfl,
        by rw [hz, hI.rcx]⟩) (fun _ h => h) h2 h2.rcx))

/-- The end: the postcondition and the calling convention. -/
theorem end_ok {s : State} (h : BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => sbK.post σ s' ∧ gprPreserved σ s' := by
  have hL : St σ 264 = ballFold (tauOf σ) (X σ) := by
    simp only [St, ballFold, i0]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (St_le 264)) fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun hf => ?_⟩, hg⟩
  · rw [hax, hL]
  · rw [hm]
    have hst := h.st
    rw [hL] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

end Ball

theorem sampleInBall_correct (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Sample.sampleInBall σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' := by
  open Ball in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 272) (.inl rfl) (by decide) h1) fun s2 h2 =>
      WP.seq (WP.mono (zero_ok hp h2) fun s3 h3 => WP.seq (WP.mono (loop_ok hp h3) fun s4 h4 => end_ok hp h4))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Sample

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_sample_in_ball`, constant time but for `c̃`

Two runs whose `c̃` (the declared leak), `len`, `τ` and pointers agree leak
the same: the prologue and the blocks around the loop by the taint analysis,
the sponge by `sponge_ct`, and the loop, whose branches and addresses depend
on the SHAKE256 output, by relating the two runs iteration by iteration
(`body_ct`): both are at the same iteration with the same `i`, sign bits and
byte to read, so each branch goes the same way and each access goes to the
same address.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.X86_64 (at_)

/-- Code that writes only the registers `rs` keeps the others, in both runs. -/
theorem RelCT.keeps {c : Prog isa} (rs : List Reg) (hc : writesOnly rs c = true) {P Q : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True)
    (hQ : ∀ x y x' y', P x y → (∀ r, r ∉ rs → x'.gpr r = x.gpr r) → (∀ r, r ∉ rs → y'.gpr r = y.gpr r) →
      Q x' y') : RelCT isa P c Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  refine ⟨(h _ _ _ _ _ _ hp e₁ e₂).1, hQ x y x' y' hp (fun r hr => Exec.gpr (fun i hi => ?_) e₁)
    (fun r hr => Exec.gpr (fun i hi => ?_) e₂)⟩ <;>
  · unfold writesOnly at hc
    rw [Code.allInstrs_eq, List.all_eq_true] at hc
    cases hcl : Taint.clobbers i r
    · rfl
    · exact absurd (List.contains_iff_mem.mp (writesIn_sound (hc i hi) hcl)) hr

namespace BallCT

/-- Registers that agree in two runs. -/
def Same (rs : List Reg) (s₁ s₂ : State) : Prop := ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

/-- Two runs at the start of an iteration: the same registers of the loop,
and the same byte to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  Same [.rbp, .rdi, .rsi, .rcx, .r9] s₁ s₂ ∧ s₁.mem (s₁.gpr .rsi) = s₂.mem (s₂.gpr .rsi) ∧
    InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsi) 1

/-- After the comparison of `i` with 256. -/
def R1 (s₁ s₂ : State) : Prop := BRel s₁ s₂ ∧ s₁.cf = s₂.cf

/-- After the load of the byte. -/
def R2 (s₁ s₂ : State) : Prop := Same [.rbp, .rdi, .rax, .r9, .rsi, .rcx] s₁ s₂ ∧ s₁.cf = s₂.cf

/-- The end of a try. -/
def RQ (s₁ s₂ : State) : Prop := Same [.rsi, .rcx] s₁ s₂

theorem same_of {rs : List Reg} {s₁ s₂ : State} (h : Same rs s₁ s₂) {r : Reg} (hr : r ∈ rs) :
    s₁.gpr r = s₂.gpr r := h r hr

theorem cmp_ct : RelCT isa BRel (.block [.alu .cmp .rdi (.imm 256)]) R1 :=
  RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧
      x'.gpr = x.gpr ∧ x'.rd = x.rd ∧ x'.wr = x.wr)
    (taintRel [] nil_regs (by taint_decide)) (fun x y _ => ⟨cmpRdi_ok x, cmpRdi_ok y⟩)
    fun x y x' y' ⟨hs, hb, i₁, i₂⟩ ⟨c₁, m₁, g₁, r₁, w₁⟩ ⟨c₂, m₂, g₂, r₂, w₂⟩ =>
      ⟨⟨fun r hr => by rw [g₁, g₂]; exact hs r hr, by rw [m₁, m₂, g₁, g₂]; exact hb,
        by rw [r₁, w₁, g₁]; exact i₁, by rw [r₂, w₂, g₂]; exact i₂⟩,
        by rw [c₁, c₂, same_of hs (by decide : Reg.rdi ∈ _)]⟩

theorem load_ct : RelCT isa (fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some true)
    (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) R2 :=
  RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .rax = BitVec.ofNat 64 (x.mem (x.gpr .rsi)).toNat ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < (x.mem (x.gpr .rsi)).toNat)) ∧ x'.mem = x.mem ∧
        x'.gpr .rdi = x.gpr .rdi) ∧ Keep [.rax, .rdi] x x')
    (taintRel [.rsi] (fun x y ⟨⟨⟨hs, _⟩, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact same_of hs (by decide)) (by taint_decide))
    (fun x y ⟨⟨⟨_, _, i₁, i₂⟩, _⟩, _⟩ => ⟨bLoad_ok x i₁, bLoad_ok y i₂⟩)
    fun x y x' y' ⟨⟨⟨hs, hb, _⟩, _⟩, _⟩ ⟨⟨a₁, c₁, _, d₁⟩, k₁⟩ ⟨⟨a₂, c₂, _, d₂⟩, k₂⟩ => by
      refine ⟨fun r hr => ?_, by rw [c₁, c₂, hb, same_of hs (by decide : Reg.rdi ∈ _)]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [k₁.gpr (by decide), k₂.gpr (by decide)]; exact same_of hs (by decide)
      · rw [d₁, d₂]; exact same_of hs (by decide)
      · rw [a₁, a₂, hb]
      all_goals rw [k₁.gpr (by decide), k₂.gpr (by decide)]; exact same_of hs (by decide)

theorem nil_ct {P : State → State → Prop} (hP : ∀ x y, P x y → RQ x y) : RelCT isa P (.block []) RQ :=
  RelCT.postDep (F := fun (x x' : State) => x' = x) (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun x y x' y' h f₁ f₂ => by rw [f₁, f₂]; exact hP x y h

theorem set_ct : RelCT isa (fun s₁ s₂ => R2 s₁ s₂ ∧ isa.eval .b s₁ = some false) bSet RQ :=
  RelCT.keeps [.rdx, .r9, .rdi] (by rfl)
    (taintRel [.rbp, .rdi, .rax, .r9] (fun x y ⟨⟨hs, _⟩, _⟩ r hr => hs r (List.mem_append_left (bs := [Reg.rsi, Reg.rcx]) hr))
      (by taint_decide))
    fun x y x' y' ⟨⟨hs, _⟩, _⟩ k₁ k₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [k₁ _ (by decide), k₂ _ (by decide)] <;> exact same_of hs (by decide)

theorem try_ct : RelCT isa (fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some true) bTry RQ :=
  RelCT.seq load_ct (RelCT.ite (fun x y h => h.2)
    (nil_ct (P := fun s₁ s₂ => R2 s₁ s₂ ∧ isa.eval .b s₁ = some true) fun x y ⟨⟨hs, _⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact same_of hs (by decide))
    set_ct)

theorem step_ct : RelCT isa RQ (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)])
    fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (taintRel [] nil_regs (by taint_decide))
    (fun x y _ => ⟨WP.mono (step_ok x 1) fun _ h => h.1.2.2.1, WP.mono (step_ok y 1) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, same_of e (by decide : Reg.rcx ∈ _)]

theorem body_ct : RelCT isa BRel bBody fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq cmp_ct (RelCT.seq (RelCT.ite (fun x y h => h.2) try_ct
    (nil_ct (P := fun s₁ s₂ => R1 s₁ s₂ ∧ isa.eval .b s₁ = some false) fun x y ⟨⟨⟨hs, _⟩, _⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact same_of hs (by decide))) step_ct)

end BallCT

/-! ## The whole function -/

namespace Ball

open BallCT

section
variable {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂)
include hq

theorem pub_X : X σ₁ = X σ₂ := by simp only [X, B, hq.2.2.2.2.2.2]
theorem pub_tau : tauOf σ₁ = tauOf σ₂ := by simp only [tauOf, hq.2.2.1]
theorem pub_sp : spOf σ₁ = spOf σ₂ := by simp only [spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]
theorem pub_St (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, pub_X hq, pub_tau hq]

theorem spPub : SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  ⟨hq.1, by simp only [hq.2.1], hq.2.2.2.2.1, hq.2.2.2.1, by simp only [hq.2.2.1], hq.2.2.2.2.2.1⟩

end

/-- Two runs at iteration `t`, `n = 264 - t` iterations from the end. -/
def LI (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, sbK.pre σ₁ ∧ sbK.pre σ₂ ∧ sbK.pub σ₁ σ₂ ∧ n = 264 - t ∧ t < 264 ∧ BAt σ₁ t s₁ ∧ BAt σ₂ t s₂

theorem li_brel {n : Nat} {s₁ s₂ : State} (h : LI n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  have rs : ∀ {σ s}, sbK.pre σ → BAt σ t s → InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1 := fun hp h => by
    rw [h.rsi, at_add]; exact inScrRd (spOk hp) h.env (by omega_using [ht])
  have bt : ∀ {σ s}, BAt σ t s → s.mem (s.gpr .rsi) = (X σ).getD (8 + t) 0 := fun h => by
    rw [h.rsi, at_add, show 848 + t = 840 + (8 + t) by omega_using [], ← at_add, out_getD h.out (by omega_using [ht])]
  refine ⟨fun r hr => ?_, by rw [bt l₁, bt l₂, pub_X hq], rs p₁ l₁, rs p₂ l₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [l₁.env.rbp, l₂.env.rbp, pub_sp hq]
  · rw [l₁.rdi, l₂.rdi, pub_St hq]
  · rw [l₁.rsi, l₂.rsi, pub_sp hq]
  · rw [l₁.rcx, l₂.rcx]
  · rw [l₁.r9, l₂.r9, pub_St hq]; simp only [W, i0, pub_X hq, pub_tau hq]

theorem loop_ct (n : Nat) :
    RelCT isa (LI n) (.loop bBody .ne) (Rel2 sbK.pre sbK.pub fun σ s => BAt σ 264 s) := by
  refine RelCT.loop (M := isa) LI (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sbK.pre p.1 ∧ p.2 < 264 ∧ BAt p.1 p.2 x →
      BAt p.1 (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (264 - p.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y h => li_brel h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all' (fun p hp' => bat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => bat_step hp'.1 hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (264 - t) - 1 == 0) = decide (t + 1 = 264) := by
      rw [ofNat64_pred (by omega_using [ht]) (by omega_using []), ofNat64_beq_zero (by omega_using [])]
      exact decide_eq_decide.mpr (by omega_using [ht])
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 264 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ 264 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨264 - (t + 1), by omega_using [hn, ht], σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega_using [ht, this], l₁', l₂'⟩

theorem hok : ∀ σ, sbK.pre σ → SpOk (spOf σ) σ := fun _ hp => spOk hp

theorem hpub : ∀ σ₁ σ₂, sbK.pre σ₁ → sbK.pre σ₂ → sbK.pub σ₁ σ₂ → SpPub (spOf σ₁) (spOf σ₂) σ₁ σ₂ :=
  fun _ _ _ _ hq => spPub hq

/-- The zeroing, the loop and the end. -/
theorem tail_ct : RelCT isa (Rel2 sbK.pre sbK.pub fun σ => J6 136 272 (spOf σ) σ)
    (.seq bZero (.seq bLoop (.block (retJ ++ epi)))) fun _ _ => True := by
  refine RelCT.seq (relInv (I' := ZDone) (fun σ s hp h => zero_ok hp h)
    (taintSp hpub (J := J6 136 272) (fun _ _ h => h.env) [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (RelCT.seq (relInv (I' := fun σ s => WP isa (.block [.mov32 .rcx (.imm 264)]) s (BAt σ 0))
      (fun σ s hp h => setup_ok hp h)
      (taintSp hpub (J := fun P σ s => ZDone σ s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)))
    (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => BAt σ 0 s) (fun σ s _ h => h) (RelCT.mono
        (taintRel [] nil_regs (by taint_decide)) (fun _ _ _ => trivial) fun _ _ _ => trivial))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by omega_using [], l₁, l₂⟩)
      (loop_ct 264))) ?_
  exact taintSp hpub (J := fun P σ s => BAt σ 264 s) (fun _ _ h => h.env) [] nil_regs (by taint_decide)

end Ball

open Ball in
theorem sampleInBall_ct : ConstantTime isa sbK.pre sbK.pub Impl.MlDsa.X86_64.Sample.sampleInBall := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (relInv (I' := fun σ => J0 (spOf σ) σ)
    (fun σ s hp h => by subst h; exact pro_ok hp)
    (taintRel [.rdi, .rsi, .rcx, .r8, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1]) (by taint_decide))) ?_)
  exact RelCT.seq (sponge_ct hok hpub (.inl rfl) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))
    tail_ct

end VG.Proof.MlDsa.X86_64.Sample

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def sbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 39 | .rcx => 0x2000 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sampleInBall_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Sample.sampleInBall (Proof.MlDsa.sampleInBallContract X86_64.abi 16) :=
  Verified.of_correct sampleInBall_correct sampleInBall_ct
    { pre := by sig_implies_pre [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ 221 _) = none
              rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, X86_64.abi,
          X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, leakBytes_inj hb⟩
      sat := by sig_implies_sat [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, sbK, X86_64.abi,
        X86_64.argRegs] [sbSat] using sbSat }

end VG.Proof.MlDsa.X86_64.Sample

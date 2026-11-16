module

public import VerifiedGarbage.Impl.Gcm.AArch64.Neon
public import VerifiedGarbage.Proof.Gcm.AArch64.Neon.Mul
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

/-!
# GHASH with the 8-bit PMULL on AArch64: `vg_ghash_neon`

Untrusted: everything here is checked by Lean. What each group of
instructions of `Impl.Gcm.AArch64.Neon` does to the state, each proved by one
symbolic execution, and from them that a block's instructions compute `mulV`
of `Proof/Gcm/Clmul/Ops.lean`, which `vg_ghash_aes` computes with the 64-bit
`pmull` (`Mul.lean`): the rest is as its proof (`Pmull/Ghash.lean`).
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.Gcm.AArch64.Neon

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul
open VG.Proof.Gcm.AArch64.Pmull (VOnly v_setV gpr_setV mem_setV rd_setV wr_setV sp_setV exec_eor exec_ext8
  exec_movi0 exec_rev64b)
open VG.Impl.Gcm.AArch64.Neon

/-! ## The instructions -/

theorem by8_vdword (v : BitVec 128) (l e : Nat) (he : e < 8) :
    by8 (vdword v l) e = VectorCrypto.vbyte v (8 * l + e) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [by8, VG.Proof.Gcm.Clmul.vdword, VectorCrypto.vbyte, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and, decide_eq_true (show 8 * e + i < 64 by omega_using [he, hi])]
  exact congrArg _ (by omega_using [])

theorem exec_pmull8_lo (d n m : VReg) (s : State) :
    exec (.vop (.pmull8 false d n m)) s =
      some (s.setV d (pmB (vdword (s.v n) 0) (vdword (s.v m) 0))) := by
  have h : exec (.vop (.pmull8 false d n m)) s = some (s.setV d
      (ofVHalves fun e => polyMul8 (VectorCrypto.vbyte (s.v n) (0 + e)) (VectorCrypto.vbyte (s.v m) (0 + e)))) := rfl
  rw [h]
  simp only [pmB, ofVHalves, by8_vdword _ _ _ (show 0 < 8 by decide), by8_vdword _ _ _ (show 1 < 8 by decide),
    by8_vdword _ _ _ (show 2 < 8 by decide), by8_vdword _ _ _ (show 3 < 8 by decide),
    by8_vdword _ _ _ (show 4 < 8 by decide), by8_vdword _ _ _ (show 5 < 8 by decide),
    by8_vdword _ _ _ (show 6 < 8 by decide), by8_vdword _ _ _ (show 7 < 8 by decide), Nat.mul_zero]

theorem exec_pmull8_hi (d n m : VReg) (s : State) :
    exec (.vop (.pmull8 true d n m)) s =
      some (s.setV d (pmB (vdword (s.v n) 1) (vdword (s.v m) 1))) := by
  have h : exec (.vop (.pmull8 true d n m)) s = some (s.setV d
      (ofVHalves fun e => polyMul8 (VectorCrypto.vbyte (s.v n) (8 + e)) (VectorCrypto.vbyte (s.v m) (8 + e)))) := rfl
  rw [h]
  simp only [pmB, ofVHalves, by8_vdword _ _ _ (show 0 < 8 by decide), by8_vdword _ _ _ (show 1 < 8 by decide),
    by8_vdword _ _ _ (show 2 < 8 by decide), by8_vdword _ _ _ (show 3 < 8 by decide),
    by8_vdword _ _ _ (show 4 < 8 by decide), by8_vdword _ _ _ (show 5 < 8 by decide),
    by8_vdword _ _ _ (show 6 < 8 by decide), by8_vdword _ _ _ (show 7 < 8 by decide), Nat.mul_one]

/-- The doubleword `pmull` (`pmull2` if `hi`) reads. -/
def half (hi : Bool) (v : BitVec 128) : BitVec 64 := vdword v (if hi then 1 else 0)

theorem exec_pmull8 (hi : Bool) (d n m : VReg) (s : State) :
    exec (.vop (.pmull8 hi d n m)) s = some (s.setV d (pmB (half hi (s.v n)) (half hi (s.v m)))) := by
  cases hi
  · exact exec_pmull8_lo d n m s
  · exact exec_pmull8_hi d n m s

theorem exec_shl (d n : VReg) (s : State) {k : Nat} (hk : k < 64) :
    exec (.vop (.shift .shl .d2 d n k)) s = some (s.setV d (sl k (s.v n))) := by
  have hc : VShiftOp.ok .shl (VArr.esize .d2) k = true := decide_eq_true hk
  simp only [exec, reduceVOpEval, hc, ite_true, Option.map_some]
  rfl

theorem exec_ushr (d n : VReg) (s : State) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64) :
    exec (.vop (.shift .ushr .d2 d n k)) s = some (s.setV d (sr k (s.v n))) := by
  have hc : VShiftOp.ok .ushr (VArr.esize .d2) k = true := by
    simp only [VShiftOp.ok, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hk1, hk⟩
  simp only [exec, reduceVOpEval, hc, ite_true, Option.map_some]
  rfl

/-- `ext d, n, m, #15`: the top byte of `n`, then the low fifteen of `m`. -/
def ext15 (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> (15 * 8)).extractLsb' 0 128

theorem exec_ext15 (d n m : VReg) (s : State) :
    exec (.vop (.ext d n m 15)) s = some (s.setV d (ext15 (s.v n) (s.v m))) := rfl

/-- A vector rotated up by a byte is shifted, if its top byte is clear. -/
theorem ext15_self (v : BitVec 128) (h : ∀ i < 8, v.getMsbD i = false) : ext15 v v = v <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ext15, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h8 : i < 8
  · have e := h (7 - i) (by omega_using [])
    simp only [BitVec.getMsbD, show 7 - i < 128 by omega_using [], decide_true, Bool.true_and,
      show 128 - 1 - (7 - i) = 15 * 8 + i by omega_using [h8]] at e
    simp only [show 15 * 8 + i < 128 by omega_using [h8], ite_true, e, h8, decide_true, Bool.not_true, Bool.false_and]
  · simp only [show ¬ 15 * 8 + i < 128 by omega_using [h8], ite_false, h8, decide_false, Bool.not_false, Bool.true_and]
    exact congrArg _ (by omega_using [h8])

/-! ## Forms -/

/-- A doubleword shifted down by `e - 3` bytes (up, if that is negative). -/
def fmW (e : Nat) (q : BitVec 64) : BitVec 64 :=
  match e with
  | 0 => q <<< 24 | 1 => q <<< 16 | 2 => q <<< 8 | 4 => q >>> 8 | 5 => q >>> 16 | 6 => q >>> 24
  | 7 => q >>> 32 | _ => q

/-- Each doubleword shifted down by `e - 3` bytes. -/
def fmV (e : Nat) (v : BitVec 128) : BitVec 128 := ofVDwords (fmW e (vdword v 0)) (fmW e (vdword v 1))

theorem fmV_3 (v : BitVec 128) : fmV 3 v = v := (vdwords v).symm

theorem half_fmV (hi : Bool) (e : Nat) (v : BitVec 128) : half hi (fmV e v) = fmW e (half hi v) := by
  cases hi
  · exact vdword_append_0 _ _
  · exact vdword_append_1 _ _

theorem form_ok (d n : VReg) (e : Nat) (s : State) (he : e < 8) (h3 : e ≠ 3) :
    WP isa (.block (form d n e)) s fun s' => s'.v d = fmV e (s.v n) ∧ VOnly [d] s s' := by
  have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by omega_using [he, h3]
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply WP.of_runBlock
    simp (disch := decide) only [form, runBlock_cons, runStep_some, runBlock_nil, exec_shl, exec_ushr,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
      by simp only [wr_setV], by simp only [sp_setV]⟩⟩
    · simp only [v_setV, ite_true]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [v_setV, hr, ite_false]

/-- The registers `k` hold the forms of `sv`. -/
def Keys (k : Nat → VReg) (s : State) (sv : BitVec 128) : Prop := ∀ e < 8, s.v (k e) = fmV e sv

/-! ## Sums of products -/

theorem add2_ok (hi : Bool) (p q f k0 k1 : VReg) (s : State) (hpU : p ≠ U := by decide)
    (hqU : q ≠ U := by decide) (hqp : q ≠ p := by decide) (hfU : f ≠ U := by decide)
    (hfp : f ≠ p := by decide) (hk1 : k1 ≠ U := by decide) (hk1p : k1 ≠ p := by decide) :
    WP isa (.block (add2 hi p q f k0 k1)) s fun s' =>
      s'.v p = s.v p ^^^ pmB (half hi (s.v f)) (half hi (s.v k0)) ∧
      s'.v q = s.v q ^^^ pmB (half hi (s.v f)) (half hi (s.v k1)) ∧ VOnly [U, p, q] s s' := by
  have hUp := hpU.symm
  have hpq := hqp.symm
  apply WP.of_runBlock
  simp only [add2, runBlock_cons, runStep_some, runBlock_nil, exec_pmull8, exec_eor, Option.some.injEq,
    exists_eq_left', v_setV, ite_true, ite_false, hpU, hqU, hqp, hfU, hfp, hk1, hk1p, hUp, hpq, true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

theorem add1_ok (hi : Bool) (q f k1 : VReg) (s : State) (hqU : q ≠ U := by decide) :
    WP isa (.block (add1 hi q f k1)) s fun s' =>
      s'.v q = s.v q ^^^ pmB (half hi (s.v f)) (half hi (s.v k1)) ∧ VOnly [U, q] s s' := by
  apply WP.of_runBlock
  simp only [add1, runBlock_cons, runStep_some, runBlock_nil, exec_pmull8, exec_eor, Option.some.injEq,
    exists_eq_left', v_setV, ite_true, ite_false, hqU, true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2, ite_false]

theorem fin_ok (p q : VReg) (s : State) (hpq : p ≠ q := by decide) :
    WP isa (.block (fin p q)) s fun s' =>
      s'.v p = s.v p ^^^ ext15 (s.v q) (s.v q) ∧ VOnly [q, p] s s' := by
  apply WP.of_runBlock
  simp only [fin, runBlock_cons, runStep_some, runBlock_nil, exec_ext15, exec_eor, Option.some.injEq,
    exists_eq_left', v_setV, ite_true, ite_false, hpq, true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2, ite_false]

/-! ## The products -/

theorem kReg_nmem (c : Nat) : kReg c ∉ [Y, A, F, U, P0, P1, Q0, Q1] := by
  unfold kReg; split <;> decide

theorem mReg_nmem (c : Nat) : mReg c ∉ [Y, A, F, U, P0, P1, Q0, Q1] := by
  unfold mReg; split <;> decide

theorem kReg_nmem' {rs : List VReg} (c : Nat)
    (hs : ∀ r ∈ rs, r ∈ [Y, A, F, U, P0, P1, Q0, Q1] := by decide) : kReg c ∉ rs :=
  fun h => kReg_nmem c (hs _ h)

theorem mReg_nmem' {rs : List VReg} (c : Nat)
    (hs : ∀ r ∈ rs, r ∈ [Y, A, F, U, P0, P1, Q0, Q1] := by decide) : mReg c ∉ rs :=
  fun h => mReg_nmem c (hs _ h)

theorem kReg_ne (c : Nat) {r : VReg} (h : r ∈ [Y, A, F, U, P0, P1, Q0, Q1] := by decide) : kReg c ≠ r :=
  fun e => kReg_nmem c (e ▸ h)

theorem mReg_ne (c : Nat) {r : VReg} (h : r ∈ [Y, A, F, U, P0, P1, Q0, Q1] := by decide) : mReg c ≠ r :=
  fun e => mReg_nmem c (e ▸ h)

theorem half_false (v : BitVec 128) : half false v = vdword v 0 := rfl
theorem half_true (v : BitVec 128) : half true v = vdword v 1 := rfl

/-- The products of the form `e` of the block (in `A` at `s₀`) by the forms
`c0` and `c1` of the key, of the low doublewords and of the high ones, added
to the sums. -/
theorem stepLH_ok (e c0 c1 : Nat) (he : e < 8) (h3 : e ≠ 3) (hc0 : c0 < 8) (hc1 : c1 < 8) {s₀ s : State}
    {sv : BitVec 128} (hK : Keys kReg s₀ sv) (o : VOnly [F, U, P0, P1, Q0, Q1] s₀ s) (rest : List Instr)
    (Q : State → Prop)
    (h : ∀ s', s'.v P0 = s.v P0 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c0 (vdword sv 0)) →
      s'.v Q0 = s.v Q0 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c1 (vdword sv 0)) →
      s'.v P1 = s.v P1 ^^^ pmB (fmW e (vdword (s₀.v A) 1)) (fmW c0 (vdword sv 1)) →
      s'.v Q1 = s.v Q1 ^^^ pmB (fmW e (vdword (s₀.v A) 1)) (fmW c1 (vdword sv 1)) →
      VOnly [F, U, P0, P1, Q0, Q1] s₀ s' → WP isa (.block rest) s' Q) :
    WP isa (.block (form F A e ++ (add2 false P0 Q0 F (kReg c0) (kReg c1) ++
      (add2 true P1 Q1 F (kReg c0) (kReg c1) ++ rest)))) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (form_ok F A e s he h3) fun s₁ ⟨f₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add2_ok false P0 Q0 F (kReg c0) (kReg c1) s₁ (hk1 := kReg_ne c1) (hk1p := kReg_ne c1))
    fun s₂ ⟨p₂, q₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add2_ok true P1 Q1 F (kReg c0) (kReg c1) s₂ (hk1 := kReg_ne c1) (hk1p := kReg_ne c1))
    fun s₃ ⟨p₃, q₃, o₃⟩ => ?_
  have hF : s₁.v F = fmV e (s₀.v A) := by rw [f₁, o.v A (by decide)]
  have kv : ∀ c, c < 8 → s₁.v (kReg c) = fmV c sv := fun c hc => by
    rw [o₁.v _ (kReg_nmem' c), o.v _ (kReg_nmem' c), hK c hc]
  refine h s₃ ?_ ?_ ?_ ?_ ((o.trans (o₁.trans (o₂.trans o₃))).weaken)
  · rw [o₃.v P0 (by decide), p₂, o₁.v P0 (by decide), hF, kv c0 hc0, half_fmV, half_fmV]; rfl
  · rw [o₃.v Q0 (by decide), q₂, o₁.v Q0 (by decide), hF, kv c1 hc1, half_fmV, half_fmV]; rfl
  · rw [p₃, o₂.v P1 (by decide), o₁.v P1 (by decide), o₂.v F (by decide), o₂.v _ (kReg_nmem' c0), hF,
      kv c0 hc0, half_fmV, half_fmV]; rfl
  · rw [q₃, o₂.v Q1 (by decide), o₁.v Q1 (by decide), o₂.v F (by decide), o₂.v _ (kReg_nmem' c1), hF,
      kv c1 hc1, half_fmV, half_fmV]; rfl

/-- The products of the form `e` by the form `c1` alone, added to `Q0` and `Q1`. -/
theorem stepLH1_ok (e c1 : Nat) (he : e < 8) (h3 : e ≠ 3) (hc1 : c1 < 8) {s₀ s : State}
    {sv : BitVec 128} (hK : Keys kReg s₀ sv) (o : VOnly [F, U, P0, P1, Q0, Q1] s₀ s) (rest : List Instr)
    (Q : State → Prop)
    (h : ∀ s', s'.v P0 = s.v P0 →
      s'.v Q0 = s.v Q0 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c1 (vdword sv 0)) →
      s'.v P1 = s.v P1 →
      s'.v Q1 = s.v Q1 ^^^ pmB (fmW e (vdword (s₀.v A) 1)) (fmW c1 (vdword sv 1)) →
      VOnly [F, U, P0, P1, Q0, Q1] s₀ s' → WP isa (.block rest) s' Q) :
    WP isa (.block (form F A e ++ (add1 false Q0 F (kReg c1) ++ (add1 true Q1 F (kReg c1) ++ rest)))) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (form_ok F A e s he h3) fun s₁ ⟨f₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add1_ok false Q0 F (kReg c1) s₁) fun s₂ ⟨q₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add1_ok true Q1 F (kReg c1) s₂) fun s₃ ⟨q₃, o₃⟩ => ?_
  have hF : s₁.v F = fmV e (s₀.v A) := by rw [f₁, o.v A (by decide)]
  have kv : ∀ c, c < 8 → s₁.v (kReg c) = fmV c sv := fun c hc => by
    rw [o₁.v _ (kReg_nmem' c), o.v _ (kReg_nmem' c), hK c hc]
  refine h s₃ ?_ ?_ ?_ ?_ ((o.trans (o₁.trans (o₂.trans o₃))).weaken)
  · rw [o₃.v P0 (by decide), o₂.v P0 (by decide), o₁.v P0 (by decide)]
  · rw [o₃.v Q0 (by decide), q₂, o₁.v Q0 (by decide), hF, kv c1 hc1, half_fmV, half_fmV]; rfl
  · rw [o₃.v P1 (by decide), o₂.v P1 (by decide), o₁.v P1 (by decide)]
  · rw [q₃, o₂.v Q1 (by decide), o₁.v Q1 (by decide), o₂.v F (by decide), o₂.v _ (kReg_nmem' c1), hF,
      kv c1 hc1, half_fmV, half_fmV]; rfl

/-- The products of the block and the key, unshifted. -/
theorem firstLH_ok {s : State} {sv : BitVec 128} (hK : Keys kReg s sv) :
    WP isa (.block [.vop (.pmull8 false P0 A (kReg 3)), .vop (.pmull8 true P1 A (kReg 3)),
      .vop (.pmull8 false Q0 A (kReg 4)), .vop (.pmull8 true Q1 A (kReg 4))]) s fun s' =>
      s'.v P0 = pmB (vdword (s.v A) 0) (vdword sv 0) ∧
      s'.v Q0 = pmB (vdword (s.v A) 0) (fmW 4 (vdword sv 0)) ∧
      s'.v P1 = pmB (vdword (s.v A) 1) (vdword sv 1) ∧
      s'.v Q1 = pmB (vdword (s.v A) 1) (fmW 4 (vdword sv 1)) ∧ VOnly [F, U, P0, P1, Q0, Q1] s s' := by
  have k3 : s.v .v19 = sv := by have := hK 3 (by decide); rwa [fmV_3] at this
  have k4 : s.v .v20 = fmV 4 sv := hK 4 (by decide)
  apply WP.of_runBlock
  simp only [kReg, runBlock_cons, runStep_some, runBlock_nil, exec_pmull8, Option.some.injEq, exists_eq_left',
    v_setV, ite_true, ite_false, reduceCtorEq, k3, k4, half_fmV, half_false, half_true, true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- `mulLH`: the products of the low and of the high doublewords. -/
theorem mulLH_ok {s : State} {sv : BitVec 128} (hK : Keys kReg s sv) :
    WP isa (.block mulLH) s fun s' =>
      s'.v P0 = polyMul (vdword (s.v A) 0) (vdword sv 0) ∧
      s'.v P1 = polyMul (vdword (s.v A) 1) (vdword sv 1) ∧ VOnly [F, U, P0, P1, Q0, Q1] s s' := by
  simp only [mulLH, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (firstLH_ok hK) fun s₁ ⟨a₁, b₁, c₁, d₁, o₁⟩ => ?_
  refine stepLH_ok 4 2 3 (by decide) (by decide) (by decide) (by decide) hK o₁ _ _ fun s₂ a₂ b₂ c₂ d₂ o₂ => ?_
  refine stepLH_ok 5 1 2 (by decide) (by decide) (by decide) (by decide) hK o₂ _ _ fun s₃ a₃ b₃ c₃ d₃ o₃ => ?_
  refine stepLH_ok 6 0 1 (by decide) (by decide) (by decide) (by decide) hK o₃ _ _ fun s₄ a₄ b₄ c₄ d₄ o₄ => ?_
  refine stepLH1_ok 7 0 (by decide) (by decide) (by decide) hK o₄ _ _ fun s₅ a₅ b₅ c₅ d₅ o₅ => ?_
  refine stepLH_ok 2 4 5 (by decide) (by decide) (by decide) (by decide) hK o₅ _ _ fun s₆ a₆ b₆ c₆ d₆ o₆ => ?_
  refine stepLH_ok 1 5 6 (by decide) (by decide) (by decide) (by decide) hK o₆ _ _ fun s₇ a₇ b₇ c₇ d₇ o₇ => ?_
  refine stepLH_ok 0 6 7 (by decide) (by decide) (by decide) (by decide) hK o₇ _ _ fun s₈ a₈ b₈ c₈ d₈ o₈ => ?_
  have hP0 : s₈.v P0 = cl0 (vdword (s.v A) 0) (vdword sv 0) := by
    rw [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁]; rfl
  have hQ0 : s₈.v Q0 = cl1 (vdword (s.v A) 0) (vdword sv 0) := by
    rw [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁]; rfl
  have hP1 : s₈.v P1 = cl0 (vdword (s.v A) 1) (vdword sv 1) := by
    rw [c₈, c₇, c₆, c₅, c₄, c₃, c₂, c₁]; rfl
  have hQ1 : s₈.v Q1 = cl1 (vdword (s.v A) 1) (vdword sv 1) := by
    rw [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (fin_ok P0 Q0 s₈) fun s₉ ⟨f₉, o₉⟩ => ?_
  refine WP.mono (fin_ok P1 Q1 s₉) fun s' ⟨f', o'⟩ => ⟨?_, ?_, (o₈.trans (o₉.trans o')).weaken⟩
  · rw [o'.v P0 (by decide), f₉, hP0, hQ0, ext15_self _ fun i hi => msb_cl1 _ _ hi, cl_polyMul]
  · rw [f', o₉.v P1 (by decide), o₉.v Q1 (by decide), hP1, hQ1, ext15_self _ fun i hi => msb_cl1 _ _ hi,
      cl_polyMul]

/-- The products of the form `e` of the sum of the block's halves (in `A`
at `s₀`) by the forms `c0` and `c1` of the sum of the key's, added to the sums. -/
theorem stepM_ok (e c0 c1 : Nat) (he : e < 8) (h3 : e ≠ 3) (hc0 : c0 < 8) (hc1 : c1 < 8) {s₀ s : State}
    {sm : BitVec 128} (hK : Keys mReg s₀ sm) (o : VOnly [F, U, Q0, Q1] s₀ s) (rest : List Instr)
    (Q : State → Prop)
    (h : ∀ s', s'.v Q0 = s.v Q0 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c0 (vdword sm 0)) →
      s'.v Q1 = s.v Q1 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c1 (vdword sm 0)) →
      VOnly [F, U, Q0, Q1] s₀ s' → WP isa (.block rest) s' Q) :
    WP isa (.block (form F A e ++ (add2 false Q0 Q1 F (mReg c0) (mReg c1) ++ rest))) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (form_ok F A e s he h3) fun s₁ ⟨f₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add2_ok false Q0 Q1 F (mReg c0) (mReg c1) s₁ (hk1 := mReg_ne c1) (hk1p := mReg_ne c1))
    fun s₂ ⟨p₂, q₂, o₂⟩ => ?_
  have hF : s₁.v F = fmV e (s₀.v A) := by rw [f₁, o.v A (by decide)]
  have kv : ∀ c, c < 8 → s₁.v (mReg c) = fmV c sm := fun c hc => by
    rw [o₁.v _ (mReg_nmem' c), o.v _ (mReg_nmem' c), hK c hc]
  refine h s₂ ?_ ?_ ((o.trans (o₁.trans o₂)).weaken)
  · rw [p₂, o₁.v Q0 (by decide), hF, kv c0 hc0, half_fmV, half_fmV]; rfl
  · rw [q₂, o₁.v Q1 (by decide), hF, kv c1 hc1, half_fmV, half_fmV]; rfl

theorem stepM1_ok (e c1 : Nat) (he : e < 8) (h3 : e ≠ 3) (hc1 : c1 < 8) {s₀ s : State}
    {sm : BitVec 128} (hK : Keys mReg s₀ sm) (o : VOnly [F, U, Q0, Q1] s₀ s) (rest : List Instr)
    (Q : State → Prop)
    (h : ∀ s', s'.v Q0 = s.v Q0 →
      s'.v Q1 = s.v Q1 ^^^ pmB (fmW e (vdword (s₀.v A) 0)) (fmW c1 (vdword sm 0)) →
      VOnly [F, U, Q0, Q1] s₀ s' → WP isa (.block rest) s' Q) :
    WP isa (.block (form F A e ++ (add1 false Q1 F (mReg c1) ++ rest))) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (form_ok F A e s he h3) fun s₁ ⟨f₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add1_ok false Q1 F (mReg c1) s₁) fun s₂ ⟨q₂, o₂⟩ => ?_
  have hF : s₁.v F = fmV e (s₀.v A) := by rw [f₁, o.v A (by decide)]
  have kv : ∀ c, c < 8 → s₁.v (mReg c) = fmV c sm := fun c hc => by
    rw [o₁.v _ (mReg_nmem' c), o.v _ (mReg_nmem' c), hK c hc]
  refine h s₂ ?_ ?_ ((o.trans (o₁.trans o₂)).weaken)
  · rw [o₂.v Q0 (by decide), o₁.v Q0 (by decide)]
  · rw [q₂, o₁.v Q1 (by decide), hF, kv c1 hc1, half_fmV, half_fmV]; rfl

/-- The sum of the block's halves, and its products by the key's, unshifted. -/
theorem firstM_ok {s : State} {sm : BitVec 128} (hK : Keys mReg s sm) :
    WP isa (.block [.vop (.ext F A A 8), .vop (.logic .eor A A F),
      .vop (.pmull8 false Q0 A (mReg 3)), .vop (.pmull8 false Q1 A (mReg 4))]) s fun s' =>
      s'.v A = s.v A ^^^ ext8 (s.v A) (s.v A) ∧
      s'.v Q0 = pmB (vdword (s.v A ^^^ ext8 (s.v A) (s.v A)) 0) (vdword sm 0) ∧
      s'.v Q1 = pmB (vdword (s.v A ^^^ ext8 (s.v A) (s.v A)) 0) (fmW 4 (vdword sm 0)) ∧
      VOnly [A, F, U, Q0, Q1] s s' := by
  have k3 : s.v .v27 = sm := by have := hK 3 (by decide); rwa [fmV_3] at this
  have k4 : s.v .v28 = fmV 4 sm := hK 4 (by decide)
  apply WP.of_runBlock
  simp only [mReg, runBlock_cons, runStep_some, runBlock_nil, exec_pmull8, exec_ext8, exec_eor,
    Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq, k3, k4, half_fmV, half_false,
    true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `mulM`: the product of the sums of the halves. -/
theorem mulM_ok {s : State} {sm : BitVec 128} (hK : Keys mReg s sm) :
    WP isa (.block mulM) s fun s' =>
      s'.v Q0 = polyMul (vdword (s.v A) 0 ^^^ vdword (s.v A) 1) (vdword sm 0) ∧
      VOnly [A, F, U, Q0, Q1] s s' := by
  simp only [mulM, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (firstM_ok hK) fun s₁ ⟨m₁, a₁, b₁, o₁⟩ => ?_
  have hK₁ : Keys mReg s₁ sm := fun c hc => by rw [o₁.v _ (mReg_nmem' c), hK c hc]
  have o₀ := VOnly.refl [F, U, Q0, Q1] s₁
  refine stepM_ok 4 2 3 (by decide) (by decide) (by decide) (by decide) hK₁ o₀ _ _ fun s₂ a₂ b₂ o₂ => ?_
  refine stepM_ok 5 1 2 (by decide) (by decide) (by decide) (by decide) hK₁ o₂ _ _ fun s₃ a₃ b₃ o₃ => ?_
  refine stepM_ok 6 0 1 (by decide) (by decide) (by decide) (by decide) hK₁ o₃ _ _ fun s₄ a₄ b₄ o₄ => ?_
  refine stepM1_ok 7 0 (by decide) (by decide) (by decide) hK₁ o₄ _ _ fun s₅ a₅ b₅ o₅ => ?_
  refine stepM_ok 2 4 5 (by decide) (by decide) (by decide) (by decide) hK₁ o₅ _ _ fun s₆ a₆ b₆ o₆ => ?_
  refine stepM_ok 1 5 6 (by decide) (by decide) (by decide) (by decide) hK₁ o₆ _ _ fun s₇ a₇ b₇ o₇ => ?_
  refine stepM_ok 0 6 7 (by decide) (by decide) (by decide) (by decide) hK₁ o₇ _ _ fun s₈ a₈ b₈ o₈ => ?_
  have hm : vdword (s₁.v A) 0 = vdword (s.v A) 0 ^^^ vdword (s.v A) 1 := by
    rw [m₁, vdword_xor, vdword_ext8_0]
  have hQ0 : s₈.v Q0 = cl0 (vdword (s.v A) 0 ^^^ vdword (s.v A) 1) (vdword sm 0) := by
    rw [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, hm, ← m₁, hm]; rfl
  have hQ1 : s₈.v Q1 = cl1 (vdword (s.v A) 0 ^^^ vdword (s.v A) 1) (vdword sm 0) := by
    rw [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, hm, ← m₁, hm]; rfl
  refine WP.mono (fin_ok Q0 Q1 s₈) fun s' ⟨f', o'⟩ => ⟨?_, (o₁.trans (o₈.trans o')).weaken⟩
  rw [f', hQ0, hQ1, ext15_self _ fun i hi => msb_cl1 _ _ hi, cl_polyMul]

theorem middle_ok (s : State) :
    WP isa (.block middle) s fun s' =>
      s'.v F = 0#128 ∧ s'.v P1 = s.v P1 ^^^ ext8 0#128 (s.v Q0 ^^^ s.v P0 ^^^ s.v P1) ∧
      s'.v P0 = s.v P0 ^^^ ext8 (s.v Q0 ^^^ s.v P0 ^^^ s.v P1) 0#128 ∧ VOnly [F, U, P0, P1, Q0] s s' := by
  apply WP.of_runBlock
  simp only [middle, runBlock_cons, runStep_some, runBlock_nil, exec_eor, exec_movi0, exec_ext8,
    Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq]
  refine ⟨rfl, rfl, rfl, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem carry_ok (s : State) (hF : s.v F = 0#128) :
    WP isa (.block carry) s fun s' =>
      s'.v P1 = s.v P1 ^^^ ext8 0#128 (sl 63 (s.v P1) ^^^ sl 62 (s.v P1) ^^^ sl 57 (s.v P1)) ∧
      s'.v P0 = s.v P0 ^^^ ext8 (sl 63 (s.v P1) ^^^ sl 62 (s.v P1) ^^^ sl 57 (s.v P1)) 0#128 ∧
      VOnly [A, U, P0, P1] s s' := by
  apply WP.of_runBlock
  simp (disch := decide) only [carry, runBlock_cons, runStep_some, runBlock_nil, exec_eor, exec_ext8,
    exec_shl, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq, hF]
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem stay_ok (s : State) :
    WP isa (.block stay) s fun s' =>
      s'.v Y = ext8 (s.v P0 ^^^ s.v P1 ^^^ sr 1 (s.v P1) ^^^ sr 2 (s.v P1) ^^^ sr 7 (s.v P1))
        (s.v P0 ^^^ s.v P1 ^^^ sr 1 (s.v P1) ^^^ sr 2 (s.v P1) ^^^ sr 7 (s.v P1)) ∧
      VOnly [U, P0, Y] s s' := by
  apply WP.of_runBlock
  simp (disch := decide) only [stay, runBlock_cons, runStep_some, runBlock_nil, exec_eor, exec_ext8,
    exec_ushr, Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq]
  refine ⟨trivial, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
    by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [v_setV, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `reduce`: `mid`, and the product reduced. -/
theorem reduce_ok (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Neon.reduce) s fun s' =>
      s'.v Y = reduceN ⟨s.v P1, s.v Q0 ^^^ s.v P0 ^^^ s.v P1, s.v P0⟩ ∧
      VOnly [Y, A, F, U, P0, P1, Q0] s s' := by
  rw [Impl.Gcm.AArch64.Neon.reduce, List.append_assoc, WP.block_append_iff]
  refine WP.mono (middle_ok s) fun s₁ ⟨f₁, l₁, h₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carry_ok s₁ f₁) fun s₂ ⟨l₂, h₂, o₂⟩ => ?_
  refine WP.mono (stay_ok s₂) fun s' ⟨y', o'⟩ => ⟨?_, (o₁.trans (o₂.trans o')).weaken⟩
  rw [y', h₂, l₂, h₁, l₁]
  rfl

/-- The block in `A` multiplied by the key: `mulV` of the 64-bit `pmull`. -/
theorem mul_ok {s : State} {sv : BitVec 128} (hK : Keys kReg s sv)
    (hM : Keys mReg s (sv ^^^ ext8 sv sv)) :
    WP isa (.block (mulLH ++ (mulM ++ Impl.Gcm.AArch64.Neon.reduce))) s fun s' =>
      s'.v Y = mulV (s.v A) (ext8 sv sv) ∧ VOnly [Y, A, F, U, P0, P1, Q0, Q1] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mulLH_ok hK) fun s₁ ⟨p0, p1, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulM_ok (s := s₁) (sm := sv ^^^ ext8 sv sv) fun c hc => by
    rw [o₁.v _ (mReg_nmem' c), hM c hc]) fun s₂ ⟨q0, o₂⟩ => ?_
  refine WP.mono (reduce_ok s₂) fun s' ⟨y', o'⟩ => ⟨?_, (o₁.trans (o₂.trans o')).weaken⟩
  rw [y', q0, o₂.v P0 (by decide), o₂.v P1 (by decide), p0, p1, o₁.v A (by decide), vdword_xor,
    vdword_ext8_0, ← mulN_eq, ext8_ext8]
  rfl

end VG.Proof.Gcm.AArch64.Neon

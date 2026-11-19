module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.Variants.Sm4Gcm.AArch64
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Sm4Gcm.Scratch
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.AesGcm.AArch64
public import VerifiedGarbage.Proof.Gcm.AArch64.Holes
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
import VerifiedGarbage.Proof.Gcm.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Impl.Gcm.AArch64.Neon
public import VerifiedGarbage.Impl.Gcm.AArch64
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.Gcm.AArch64.Neon
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
meta import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `Gcm.AArch64.Neon.Ghash`, which only this module used -/

section

/-!
# GHASH with the 8-bit PMULL on AArch64: `vg_ghash_neon`

Untrusted: everything here is checked by Lean. What each group of
instructions of `Impl.Gcm.AArch64.Neon` does to the state, each proved by one
symbolic execution, as bits, and from them that a block's instructions
compute `mulV` of `Proof/Gcm/Clmul/Ops.lean`, which `vg_ghash_aes` computes
with the 64-bit `pmull`, so that the function is `vg_ghash`'s contract's. The
arithmetic that takes is a hypothesis here (`Arith`), proven with the algebra
of `Proof/Gcm/Poly.lean` in `Proof/AesGcm/AArch64/GhashImpls.lean`, as that
of `vg_ghash_aes`'s key (`MulKey`): this module needs no algebra.
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.Gcm.AArch64.Neon

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Clmul
open VG.Proof.Gcm.AArch64 (hA yp dp nb H₀ Y₀ blkAddr hR yR dR Pre pre_of contains_offset toNat_ofNat_lt)
open VG.Proof.Gcm.AArch64.Pmull (VOnly v_setV gpr_setV mem_setV rd_setV wr_setV sp_setV exec_eor exec_ext8
  exec_movi0 exec_rev64b exec_movz_x exec_ins_d2 exec_addImm exec_subImm exec_strq gpr_write_x v_write mem_write
  rd_write wr_write loadRev_ok eor_ok rev64b_read blockAt_store keyV MulKey)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Impl.Gcm.Clmul (poly)
open VG.Impl.Gcm.AArch64.Neon

/-! ## The values

What the instructions compute, as bits. -/

/-- Byte `i` of a doubleword. -/
def by8 (q : BitVec 64) (i : Nat) : BitVec 8 := q.extractLsb' (8 * i) 8

/-- What `pmull .8h` computes from the doublewords it reads. -/
def pmB (a b : BitVec 64) : BitVec 128 := ofVHalves fun e => polyMul8 (by8 a e) (by8 b e)

/-! ### The product of two doublewords

Byte `i` of `a` and byte `j` of `b` meet in lane `l` of a `pmull` of `a`
shifted down by `d` bytes and `b` shifted up by as many, where `i = l + d` and
`j = l - d`: their product then lies at byte `2 l = i + j`, where it belongs
(`cl0`: the pairs with `i + j` even). Those with `i + j` odd meet in the
`pmull`s of `a` shifted down by `d` and `b` shifted up by `d - 1`, a byte
below where they belong (`cl1`). -/

def cl0 (a b : BitVec 64) : BitVec 128 :=
  pmB a b ^^^ pmB (a >>> 8) (b <<< 8) ^^^ pmB (a >>> 16) (b <<< 16) ^^^ pmB (a >>> 24) (b <<< 24) ^^^
    pmB (a <<< 8) (b >>> 8) ^^^ pmB (a <<< 16) (b >>> 16) ^^^ pmB (a <<< 24) (b >>> 24)

def cl1 (a b : BitVec 64) : BitVec 128 :=
  pmB a (b >>> 8) ^^^ pmB (a >>> 8) b ^^^ pmB (a >>> 16) (b <<< 8) ^^^ pmB (a >>> 24) (b <<< 16) ^^^
    pmB (a >>> 32) (b <<< 24) ^^^ pmB (a <<< 8) (b >>> 16) ^^^ pmB (a <<< 16) (b >>> 24) ^^^
    pmB (a <<< 24) (b >>> 32)

/-- Each doubleword shifted up by `k` bits. -/
def sl (k : Nat) (v : BitVec 128) : BitVec 128 := ofVDwords (vdword v 0 <<< k) (vdword v 1 <<< k)

/-- Each doubleword shifted down by `k` bits. -/
def sr (k : Nat) (v : BitVec 128) : BitVec 128 := ofVDwords (vdword v 0 >>> k) (vdword v 1 >>> k)

/-- The fold of `lo` into `hi`, with its halves swapped. -/
def fold (lo hi : BitVec 128) : BitVec 128 :=
  let c := sl 63 lo ^^^ sl 62 lo ^^^ sl 57 lo
  let lo := lo ^^^ ext8 0#128 c
  let hi := hi ^^^ ext8 c 0#128
  let hi := hi ^^^ lo ^^^ sr 1 lo ^^^ sr 2 lo ^^^ sr 7 lo
  ext8 hi hi

/-- The block, with its halves swapped, of a product. -/
def reduceN (p : Prod) : BitVec 128 := fold (p.lo ^^^ ext8 0#128 p.mid) (p.hi ^^^ ext8 p.mid 0#128)

/-- The product of the block `a` as loaded and the key whose halves swapped
are `s`, reduced: its three products of doublewords are those of the halves
and of their sums. -/
def mulN (a s : BitVec 128) : BitVec 128 :=
  reduceN ⟨polyMul (vdword a 1) (vdword s 1),
    polyMul (vdword a 0 ^^^ vdword a 1) (vdword s 0 ^^^ vdword s 1) ^^^ polyMul (vdword a 0) (vdword s 0) ^^^
      polyMul (vdword a 1) (vdword s 1),
    polyMul (vdword a 0) (vdword s 0)⟩

/-- What `twist` computes from the hash subkey as loaded. -/
def twistV (a : BitVec 128) : BitVec 128 :=
  (sl 1 a ^^^ ext8 (sr 63 a) (sr 63 a)) ^^^
    (ofVDwords ((vdword a 0).sshiftRight 63) ((vdword a 1).sshiftRight 63) &&& ofVDwords poly 0#64)

/-- The arithmetic the code rests on, stated without the algebra that proves
it (`arith`, `Proof/AesGcm/AArch64/GhashImpls.lean`): fifteen `pmull`s of
bytes make the product of two doublewords, and the sum of those below where
they belong has a clear top byte; the three products and the reduction by
shifts make `mulV`; `twist` computes the key of `vg_ghash_aes`, by which
`mulV` multiplies by the hash subkey. -/
structure Arith : Prop where
  cl : ∀ a b : BitVec 64, cl0 a b ^^^ (cl1 a b <<< 8) = polyMul a b
  msb : ∀ (a b : BitVec 64) (i : Nat), i < 8 → (cl1 a b).getMsbD i = false
  mul : ∀ a t : BitVec 128, mulN a (ext8 t t) = mulV a t
  key : ∀ H : Block, ext8 (twistV (ext8 H H)) (twistV (ext8 H H)) = keyV H
  mulKey : MulKey

theorem ext8_xor (a b : BitVec 128) : ext8 (a ^^^ b) (a ^^^ b) = ext8 a a ^^^ ext8 b b := by
  have h := vdwords (ext8 a a ^^^ ext8 b b)
  rw [vdword_xor, vdword_xor, vdword_ext8_0, vdword_ext8_1, vdword_ext8_0, vdword_ext8_1] at h
  rw [h, ext8_eq, vdword_xor, vdword_xor]

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
theorem mulLH_ok (ar : Arith) {s : State} {sv : BitVec 128} (hK : Keys kReg s sv) :
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
  · rw [o'.v P0 (by decide), f₉, hP0, hQ0, ext15_self _ fun i hi => ar.msb _ _ i hi, ar.cl]
  · rw [f', o₉.v P1 (by decide), o₉.v Q1 (by decide), hP1, hQ1, ext15_self _ fun i hi => ar.msb _ _ i hi,
      ar.cl]

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
theorem mulM_ok (ar : Arith) {s : State} {sm : BitVec 128} (hK : Keys mReg s sm) :
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
  rw [f', hQ0, hQ1, ext15_self _ fun i hi => ar.msb _ _ i hi, ar.cl]

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
  simp only [carry, runBlock_cons, runStep_some, runBlock_nil, exec_eor, exec_ext8,
    exec_shl _ _ _ (show 63 < 64 by decide), exec_shl _ _ _ (show 62 < 64 by decide),
    exec_shl _ _ _ (show 57 < 64 by decide), Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false,
    reduceCtorEq, hF]
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
theorem mul_ok (ar : Arith) {s : State} {sv : BitVec 128} (hK : Keys kReg s sv)
    (hM : Keys mReg s (sv ^^^ ext8 sv sv)) :
    WP isa (.block Impl.Gcm.AArch64.Neon.mul) s fun s' =>
      s'.v Y = mulV (s.v A) (ext8 sv sv) ∧ VOnly [Y, A, F, U, P0, P1, Q0, Q1] s s' := by
  rw [Impl.Gcm.AArch64.Neon.mul, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulLH_ok ar hK) fun s₁ ⟨p0, p1, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulM_ok ar (s := s₁) (sm := sv ^^^ ext8 sv sv) fun c hc => by
    rw [o₁.v _ (mReg_nmem' c), hM c hc]) fun s₂ ⟨q0, o₂⟩ => ?_
  refine WP.mono (reduce_ok s₂) fun s' ⟨y', o'⟩ => ⟨?_, (o₁.trans (o₂.trans o')).weaken⟩
  rw [y', q0, o₂.v P0 (by decide), o₂.v P1 (by decide), p0, p1, o₁.v A (by decide), vdword_xor,
    vdword_ext8_0, ← ar.mul, ext8_ext8]
  rfl

/-! ## The key -/

theorem exec_sshr63 (d n : VReg) (s : State) :
    exec (.vop (.shift .sshr .d2 d n 63)) s =
      some (s.setV d (ofVDwords ((vdword (s.v n) 0).sshiftRight 63) ((vdword (s.v n) 1).sshiftRight 63))) := rfl

theorem exec_and (d n m : VReg) (s : State) :
    exec (.vop (.logic .and d n m)) s = some (s.setV d (s.v n &&& s.v m)) := rfl

/-- `twist`: `H' = H · x⁻¹`, from `H` as loaded in `A`. -/
theorem twist_ok (s : State) :
    WP isa (.block twist) s fun s' =>
      s'.v (kReg 3) = twistV (s.v A) ∧
      (∀ r, r ∉ [F, U, P0, P1, Q0, kReg 3] → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (disch := decide) only [twist, kReg, runBlock_cons, runStep_some, runBlock_nil, exec_ushr, exec_shl,
    exec_sshr63, exec_ext8, exec_eor, exec_and, exec_movi0, exec_movz_x (show 16 * 3 < 64 by decide),
    exec_ins_d2 (show 0 < 2 by decide), Option.some.injEq, exists_eq_left']
  simp only [v_setV, gpr_setV, v_write,
    gpr_write_x, mem_setV, rd_setV, wr_setV, mem_write, rd_write, wr_write, ite_true, ite_false, reduceCtorEq,
    and_true]
  refine ⟨?_, fun r hr => ?_, fun r h5 => ?_⟩
  · rw [show setLane (0 : BitVec 128) 64 0 ((0xc200 : BitVec 16).setWidth 64 <<< (16 * 3)) =
      ofVDwords poly 0#64 by decide +kernel]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  · simp only [h5, ite_false]

theorem sumKey_ok (s : State) :
    WP isa (.block sumKey) s fun s' =>
      s'.v (mReg 3) = s.v (kReg 3) ^^^ ext8 (s.v (kReg 3)) (s.v (kReg 3)) ∧ VOnly [mReg 3] s s' := by
  apply WP.of_runBlock
  simp only [sumKey, kReg, mReg, runBlock_cons, runStep_some, runBlock_nil, exec_ext8, exec_eor,
    Option.some.injEq, exists_eq_left', v_setV, ite_true, ite_false, reduceCtorEq, true_and]
  refine ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV], by simp only [rd_setV],
    by simp only [wr_setV], by simp only [sp_setV]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [v_setV, hr, ite_false]

/-- The seven other forms of a key. -/
theorem forms_ok (k : Nat → VReg) (hk : k = kReg ∨ k = mReg) (s : State) :
    WP isa (.block (forms k)) s fun s' =>
      Keys k s' (s.v (k 3)) ∧ VOnly [k 0, k 1, k 2, k 4, k 5, k 6, k 7] s s' := by
  rcases hk with rfl | rfl
  all_goals
    apply WP.of_runBlock
    simp (disch := decide) only [forms, form, kReg, mReg, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec_shl, exec_ushr, Option.some.injEq, exists_eq_left', v_setV,
      ite_false, reduceCtorEq]
    refine ⟨fun e he => ?_, ⟨fun r hr => ?_, by simp only [gpr_setV], by simp only [mem_setV],
      by simp only [rd_setV], by simp only [wr_setV], by simp only [sp_setV]⟩⟩
    · have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by omega_using [he]
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [kReg, mReg, v_setV, ite_true, ite_false, reduceCtorEq]
      all_goals first | rfl | exact (fmV_3 _).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [v_setV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2,
        ite_false]

theorem kReg_nmem_m (c : Nat) : kReg c ∉ [mReg 0, mReg 1, mReg 2, mReg 4, mReg 5, mReg 6, mReg 7] := by
  unfold kReg; split <;> decide

/-! ## The invariant -/

/-- `Y` after `i` blocks. -/
abbrev Ys (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- Block `i` is in the data. -/
theorem in_blk16 {s₀ : State} (hp : Pre s₀) {i : Nat} (h : i < nb s₀) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * 0)) 16 := by
  have := hp.nb_lt
  refine ⟨dR s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add, ← Nat.mul_add]
  exact contains_offset (by omega_using [h]) (by omega_using [h, this])

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

theorem ofNat_bne {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  rw [bne, ofNat_beq hk]
  by_cases h : k = 0
  · rw [decide_eq_true h, decide_eq_false (by omega_using [h])]; rfl
  · rw [decide_eq_false h, decide_eq_true h]; rfl

/-- What holds after `i` blocks. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i ≤ nb s₀
  key : ∃ sv, ext8 sv sv = keyV (H₀ s₀) ∧ Keys kReg s sv ∧ Keys mReg s (sv ^^^ ext8 sv sv)
  y : s.v Y = ext8 (Ys s₀ i) (Ys s₀ i)
  x1 : s.gpr .x1 = yp s₀
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (16 * 1) ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → s'.gpr r = s.gpr r) ∧ s'.v = s.v ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec_addImm (show 16 < 4096 by decide),
    exec_subImm (show 1 < 4096 by decide), gpr_write_x, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, fun r h2 h3 => by simp only [h2, h3, ite_false], rfl, rfl, rfl, rfl⟩

theorem body_ok (ar : Arith) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i + 1 ≤ nb s₀) {s : State}
    (hI : Inv s₀ i s) : WP isa (.block body) s (Inv s₀ (i + 1)) := by
  obtain ⟨sv, hx, hK, hM⟩ := hI.key
  simp only [body, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x2 (16 * 0) s rfl (by decide)
    (by rw [hI.rd, hI.wr, hI.x2]; exact in_blk16 hp (by omega_using [hi]))) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  have o₁₂ := o₁.trans o₂
  refine WP.mono (mul_ok ar (s := s₂) (sv := sv) (fun c hc => by rw [o₁₂.v _ (kReg_nmem' c), hK c hc])
    (fun c hc => by rw [o₁₂.v _ (mReg_nmem' c), hM c hc])) fun s₃ ⟨y₃, o₃⟩ => ?_
  refine WP.mono (advance_ok s₃) fun s' ⟨f2, f3, fg, fv, fm, frd, fwr⟩ => ?_
  have O := o₁₂.trans o₃
  refine ⟨hi, ⟨sv, hx, fun c hc => by rw [fv, O.v _ (kReg_nmem' c), hK c hc],
    fun c hc => by rw [fv, O.v _ (mReg_nmem' c), hM c hc]⟩, ?_,
    by rw [fg .x1 (by decide) (by decide), O.gpr, hI.x1], ?_, ?_, by rw [fm, O.mem, hI.mem],
    by rw [frd, O.rd, hI.rd], by rw [fwr, O.wr, hI.wr]⟩
  · rw [fv, y₃, e₂, l₁, rev64b_read, o₁.v Y (by decide), hI.y, hI.mem, hI.x2, Nat.mul_zero, add_ofNat_zero,
      ← ext8_xor, hx, ar.mulKey,
      show Ys s₀ (i + 1) = _ from ghashFrom_blocksAt_succ _ _ _ _ _, BitVec.xor_comm]
  · rw [f2, O.gpr, hI.x2, blkAddr, blkAddr, Offset.add_add, ← Nat.mul_add]
  · rw [f3, O.gpr, hI.x3, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]

/-! ## The prologue and the epilogue -/

theorem prologue_ok (ar : Arith) {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (Inv s₀ 0) := by
  have h_in : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 0) 16 :=
    ⟨hR s₀, by simp [hp.rd], contains_offset (by decide) (by decide)⟩
  simp only [prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x0 0 s₀ rfl (by decide) h_in) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (twist_ok s₁) fun s₂ ⟨t₂, kv₂, kg₂, m₂, rd₂, wr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sumKey_ok s₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (forms_ok kReg (.inl rfl) s₃) fun s₄ ⟨k₄, o₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (forms_ok mReg (.inr rfl) s₄) fun s₅ ⟨k₅, o₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .x5 → s₅.gpr r = s₀.gpr r := fun r h5 => by
    rw [o₅.gpr, o₄.gpr, o₃.gpr, kg₂ r h5, o₁.gpr]
  have mem₅ : s₅.mem = s₀.mem := by rw [o₅.mem, o₄.mem, o₃.mem, m₂, o₁.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [o₅.rd, o₄.rd, o₃.rd, rd₂, o₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [o₅.wr, o₄.wr, o₃.wr, wr₂, o₁.wr]
  refine WP.mono (loadRev_ok Y .x1 0 s₅ rfl (by decide) (by
    rw [rd₅, wr₅, g₅ .x1 (by decide)]
    exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩))
    fun s' ⟨l', o'⟩ => ?_
  have hx : ext8 (s₂.v (kReg 3)) (s₂.v (kReg 3)) = keyV (H₀ s₀) := by
    rw [t₂, l₁, rev64b_read, add_ofNat_zero]; exact ar.key _
  have hK : Keys kReg s' (s₂.v (kReg 3)) := fun c hc => by
    rw [o'.v _ (kReg_nmem' c), o₅.v _ (kReg_nmem_m c), k₄ c hc, o₃.v _ (by decide)]
  have hM : Keys mReg s' (s₂.v (kReg 3) ^^^ ext8 (s₂.v (kReg 3)) (s₂.v (kReg 3))) := fun c hc => by
    rw [o'.v _ (mReg_nmem' c), k₅ c hc, o₄.v _ (by decide), m₃]
  refine ⟨Nat.zero_le _, ⟨_, hx, hK, hM⟩, ?_, by rw [o'.gpr, g₅ .x1 (by decide)],
    by rw [o'.gpr, g₅ .x2 (by decide)]; simp [blkAddr], by rw [o'.gpr, g₅ .x3 (by decide)]; simp [nb],
    by rw [o'.mem, mem₅], by rw [o'.rd, rd₅], by rw [o'.wr, wr₅]⟩
  rw [l', rev64b_read, mem₅, g₅ .x1 (by decide), add_ofNat_zero]
  rfl

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, by simp [hp.wr], contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hout,
    WP.block_nil ?_⟩
  show blockAt ((s.setV Y _).mem.write ((s.setV Y _).gpr .x1 + BitVec.ofNat 64 0) 16
    ((s.setV Y _).v Y)) (yp s₀) = Ys s₀ (nb s₀)
  simp only [mem_setV, gpr_setV, v_setV, ↓reduceIte, hI.x1, add_ofNat_zero, blockAt_store, hI.y, ext8_ext8]

/-! ## The whole function -/

theorem loops_ok (ar : Arith) {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x3) s₀ = some (decide (nb s₀ = 0)) := by
    have h3 : s₀.gpr .x3 = BitVec.ofNat 64 (nb s₀) := by simp [nb]
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
    rw [h3, ofNat_beq (show nb s₀ < 2 ^ 64 by omega_using [hn])]
  refine WP.ite _ hev (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.block_nil ?_
    show blockAt s₀.mem (yp s₀) = Ys s₀ (nb s₀)
    rw [h]; rfl
  · simp only [decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (prologue_ok ar hp) fun s₁ hI₁ => ?_)
    refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
    let Inv1 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, Inv1 m s → WP isa (.block body) s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ Inv s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv1 m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok ar hp (by omega_using [hi]) hI) fun s' hI' => ?_
      have hev : eval (.nonzero .x .x3) s' = some (decide (nb s₀ - (i + 1) ≠ 0)) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x3,
          ofNat_bne (show nb s₀ - (i + 1) < 2 ^ 64 by omega_using [hn])]
      by_cases hlast : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega_using [hi, hlast]
        exact .inl ⟨by rw [hev, decide_eq_false (fun hne => hne hlast)], this ▸ hI'⟩
      · exact .inr ⟨by rw [hev, decide_eq_true hlast], nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl,
          by omega_using [hlast], hI'⟩
    exact WP.loop (M := isa) Inv1 hstep (nb s₀) s₁ ⟨0, rfl, by omega_using [h], hI₁⟩

/-- Whether a register is not one of `preserved`, as one `match` (as in
`Pmull/Ghash.lean`). -/
private def notPres : Reg → Bool
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 | .x30 => false
  | _ => true

private theorem keeps_pres {c : Prog isa} (h : c.allInstrs (fun i => (dsts i).all notPres) = true) :
    c.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  rw [Code.allInstrs_eq] at h ⊢
  refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun r hr => ?_
  have hn : notPres r = false := by revert r; decide
  simp only [clobbers_eq_false_of_all (List.all_eq_true.mp h i hi) hn, Bool.not_false]

theorem correct (ar : Arith) {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loops_ok ar hp) (keeps_pres (by decide +kernel))
    (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghash_correct (ar : Arith) (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct ar (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Gcm.AArch64.Neon

end

end

/-!
# AES-GCM on AArch64: `vg_ghash`, `vg_ghash_neon`, `vg_ghash_aes`, `vg_ghash_prepared8_aes` and `vg_ghash_with_powers_aes`

Untrusted: everything here is checked by Lean. The `GhashImpl`s of
`vg_ghash`, `vg_ghash_neon` (with the arithmetic its proof takes as a
hypothesis, `Neon.arith`) and `vg_ghash_aes` and the `GhashPreparedImpl` of
`vg_ghash_prepared8_aes`, from their proofs, apart from `Callee.lean`: only
the variants need them, and their proofs import the algebra of
`Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then need not
import. So does `gh8Ok`, which
the interleaved loops' proofs (`Proof/Gcm/AArch64/Stitch/`) take as a
hypothesis: what `ghPart` computes (`gh8V`) is GHASH of its eight blocks, in
the ring `Q` of `Proof/Gcm/Poly.lean`. Karatsuba's products (`kadd`) add
`x · a · s` once `fix`ed (`val_fix_kadd`): `mid` has the two products
`vg_ghash_aes` adds to it, and the other two each twice. The power `H'ᵏ` with
its halves swapped is of the class of `x⁻¹ · Hᵏ` (`x_φ_pp`).
-/

@[expose] public section


local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

/-! ## `vg_ghash_neon`: the arithmetic

What `Proof/AesGcm/AArch64/GhashImpls.lean` takes as a hypothesis (`Arith`):
`pmull` of eight pairs of bytes (`pmB`) multiplies polynomials lane by lane,
and fifteen of them, of the two factors shifted by whole bytes in opposite
directions, add up to the product of two doublewords (`cl_polyMul`); the
reduction by shifts is of the class of the product (`ρ_reduceN`), so that a
block's instructions compute `mulV` (`mulN_eq`); and `twist` computes
`vg_ghash_aes`'s key (`twistV_key`). -/

namespace VG.Proof.Gcm.AArch64.Neon

open Polynomial
open VG.AArch64 (polyMul8 ofVHalves)
open VG.VectorCrypto VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul
open VG.Impl.Gcm.Clmul (poly)

/-! ## The product of two bytes -/

theorem gp_shl8 (b : BitVec 8) {j : Nat} (hj : j < 8) :
    gp ((b.setWidth 16) <<< j) = X ^ (8 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 8 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 16 - 8 ≤ d + j by omega_using [h]), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega_using [hj]))
  · simp only [h, ite_false, decide_eq_false (show ¬ 16 - 8 ≤ d + j by omega_using [h]), Bool.false_and]; rfl

/-- The first `k` steps of `polyMul8`. -/
def clSteps8 (a b : BitVec 8) (k : Nat) : BitVec 16 :=
  (List.range k).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 16 <<< i) else acc) 0

theorem gp_clSteps8 (a b : BitVec 8) {k : Nat} (hk : k ≤ 8) :
    gp (clSteps8 a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (7 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [clSteps8, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : clSteps8 a b (k + 1) =
        if a.getLsbD k then clSteps8 a b k ^^^ (b.setWidth 16 <<< k) else clSteps8 a b k := by
      simp only [clSteps8, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega_using [hk]), gp_shl8 b (by omega_using [hk]),
        show 8 - k = 7 - k + 1 by omega_using [hk], pow_succ]
      ring
    · rw [ih (by omega_using [hk])]; ring

theorem gp_lsb8 (a : BitVec 8) :
    (∑ i ∈ Finset.range 8, if a.getLsbD i then (X : P) ^ (7 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega_using [hi]), Bool.true_and,
    show 8 - 1 - i = 7 - i by omega_using [], show 7 - (8 - 1 - i) = i by omega_using [hi]]

/-- `pmull` of two bytes multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_polyMul8 (a b : BitVec 8) : gp (polyMul8 a b) = X * gp a * gp b := by
  rw [show polyMul8 a b = clSteps8 a b 8 from rfl, gp_clSteps8 a b (Nat.le_refl _), gp_lsb8]

/-! ## Bytes -/

theorem bytes64 (q : BitVec 64) :
    q = by8 q 7 ++ by8 q 6 ++ by8 q 5 ++ by8 q 4 ++ by8 q 3 ++ by8 q 2 ++ by8 q 1 ++ by8 q 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [by8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have h : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨
      (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_using []
  rcases h with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_using [h, hi]) only [↓ite_eq_left, ↓ite_eq_right, Bool.true_and, decide_eq_true] <;> exact congrArg _ (by omega_using [h, hi])

/-- A doubleword's polynomial, from its bytes'. -/
theorem gp_bytes (q : BitVec 64) :
    gp q = X ^ 56 * gp (by8 q 0) + X ^ 48 * gp (by8 q 1) + X ^ 40 * gp (by8 q 2) +
      X ^ 32 * gp (by8 q 3) + X ^ 24 * gp (by8 q 4) + X ^ 16 * gp (by8 q 5) + X ^ 8 * gp (by8 q 6) +
      gp (by8 q 7) := by
  conv_lhs => rw [bytes64 q]
  simp only [gp_append]
  ring

theorem by8_ushr (q : BitVec 64) (d i : Nat) :
    by8 (q >>> (8 * d)) i = if i + d < 8 then by8 q (i + d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and,
      BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge q _ (by omega_using [h])

theorem by8_shl (q : BitVec 64) (d i : Nat) :
    by8 (q <<< (8 * d)) i = if d ≤ i ∧ i < 8 then by8 q (i - d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and,
      decide_eq_true (show 8 * i + k < 64 by omega_using [h, hk]),
      decide_eq_false (show ¬ 8 * i + k < 8 * d by omega_using [h]), Bool.not_false]
    exact congrArg _ (by omega_using [h])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases h8 : i < 8
    · simp only [decide_eq_true (show 8 * i + k < 8 * d by omega_using [h, h8, hk]), Bool.not_true, Bool.false_and,
        Bool.and_false, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    · simp only [decide_eq_false (show ¬ 8 * i + k < 64 by omega_using [h8]), Bool.false_and, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]

/-! ## `pmull` of eight pairs of bytes -/

theorem gp_pmB (a b : BitVec 64) :
    gp (pmB a b) = X * (X ^ 112 * (gp (by8 a 0) * gp (by8 b 0)) + X ^ 96 * (gp (by8 a 1) * gp (by8 b 1)) +
      X ^ 80 * (gp (by8 a 2) * gp (by8 b 2)) + X ^ 64 * (gp (by8 a 3) * gp (by8 b 3)) +
      X ^ 48 * (gp (by8 a 4) * gp (by8 b 4)) + X ^ 32 * (gp (by8 a 5) * gp (by8 b 5)) +
      X ^ 16 * (gp (by8 a 6) * gp (by8 b 6)) + gp (by8 a 7) * gp (by8 b 7)) := by
  simp only [pmB, ofVHalves, gp_append, gp_polyMul8]
  ring

theorem polyMul8_zero_left (b : BitVec 8) : polyMul8 0 b = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, zero_mul, gp_zero])

theorem polyMul8_zero_right (a : BitVec 8) : polyMul8 a 0 = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, gp_zero])

/-- The top byte of `pmB` is of the product of the top bytes. -/
theorem msb_pmB (a b : BitVec 64) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = (polyMul8 (by8 a 7) (by8 b 7)).getMsbD i := by
  simp only [pmB, ofVHalves, BitVec.getMsbD_append]
  simp (disch := omega_using [hi]) only [↓ite_eq_right]

theorem msb_pmB_left (a b : BitVec 64) (h : by8 a 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_left]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

theorem msb_pmB_right (a b : BitVec 64) (h : by8 b 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_right]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

/-- A shift up by a byte divides by `X⁸`, if that byte is clear. -/
theorem gp_shl_byte (v : BitVec 128) (h : ∀ i < 8, v.getMsbD i = false) :
    X ^ 8 * gp (v <<< 8) = gp v := by
  ext d
  rw [coeff_X_pow_mul', coeff_gp, coeff_gp, BitVec.getMsbD_shiftLeft]
  by_cases h8 : 8 ≤ d
  · simp only [h8, ite_true, Nat.sub_add_cancel h8]
  · simp only [h8, ite_false, h d (by omega_using [h8])]; rfl

theorem by8_ushr8 (q : BitVec 64) (i : Nat) : by8 (q >>> 8) i = if i + 1 < 8 then by8 q (i + 1) else 0 :=
  by8_ushr q 1 i
theorem by8_ushr16 (q : BitVec 64) (i : Nat) : by8 (q >>> 16) i = if i + 2 < 8 then by8 q (i + 2) else 0 :=
  by8_ushr q 2 i
theorem by8_ushr24 (q : BitVec 64) (i : Nat) : by8 (q >>> 24) i = if i + 3 < 8 then by8 q (i + 3) else 0 :=
  by8_ushr q 3 i
theorem by8_ushr32 (q : BitVec 64) (i : Nat) : by8 (q >>> 32) i = if i + 4 < 8 then by8 q (i + 4) else 0 :=
  by8_ushr q 4 i
theorem by8_shl8 (q : BitVec 64) (i : Nat) : by8 (q <<< 8) i = if 1 ≤ i ∧ i < 8 then by8 q (i - 1) else 0 :=
  by8_shl q 1 i
theorem by8_shl16 (q : BitVec 64) (i : Nat) : by8 (q <<< 16) i = if 2 ≤ i ∧ i < 8 then by8 q (i - 2) else 0 :=
  by8_shl q 2 i
theorem by8_shl24 (q : BitVec 64) (i : Nat) : by8 (q <<< 24) i = if 3 ≤ i ∧ i < 8 then by8 q (i - 3) else 0 :=
  by8_shl q 3 i

theorem msb_cl1 (a b : BitVec 64) {i : Nat} (hi : i < 8) : (cl1 a b).getMsbD i = false := by
  simp only [cl1, BitVec.getMsbD_xor]
  rw [msb_pmB_right _ _ (by rw [by8_ushr8]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr8]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr16]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr24]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr32]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr16]; rfl) hi,
    msb_pmB_right _ _ (by rw [by8_ushr24]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr32]; rfl) hi]
  rfl

/-- Fifteen `pmull`s of bytes make the `pmull` of two doublewords. -/
theorem cl_polyMul (a b : BitVec 64) : cl0 a b ^^^ (cl1 a b <<< 8) = polyMul a b := by
  apply gp_ext
  apply mul_left_cancel₀ (pow_ne_zero 8 (X_ne_zero (R := ZMod 2)))
  rw [gp_xor, mul_add, gp_shl_byte _ fun i hi => msb_cl1 a b hi, gp_polyMul, gp_bytes a, gp_bytes b]
  simp only [cl0, cl1, gp_xor, gp_pmB, by8_ushr8, by8_ushr16, by8_ushr24, by8_ushr32, by8_shl8, by8_shl16,
    by8_shl24, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, and_true, and_self, ↓reduceIte, gp_zero, zero_mul, mul_zero, add_zero, zero_add]
  ring

/-! ## The reduction

The 256 bits of a product, `hi : mid : lo` with `hi` holding the low powers,
are four doublewords `I₃ : I₂ : I₁ : I₀`. `x¹²⁸ = 1 + x + x² + x⁷` folds
`I₀` into `I₂` and `I₁`, then `I₁` into `I₃` and `I₂`: the part of
`(1 + x + x² + x⁷) · I` that stays in its doubleword is `I ⊕ I ≫ 1 ⊕ I ≫ 2
⊕ I ≫ 7`, and what leaves it for the next is `I ≪ 63 ⊕ I ≪ 62 ⊕ I ≪ 57`. -/

/-- A shift of a doubleword down by `k` bits multiplies by `xᵏ`, but for
the bits that leave it. -/
theorem gp_split (v : BitVec 64) {k : Nat} (hk : k < 64) :
    X ^ k * gp v = gp (v >>> k) + X ^ 64 * gp (v <<< (64 - k)) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_X_pow_mul', coeff_gp, coeff_gp, coeff_gp,
    BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  rcases (by omega_using [hk] : d < k ∨ (k ≤ d ∧ d < 64) ∨ 64 ≤ d) with h | h | h
  · simp [show ¬ k ≤ d by omega_using [h], h, show ¬ 64 ≤ d by omega_using [h, hk], bit]
  · simp [h.1, h.2, show ¬ d < k by omega_using [h], show ¬ 64 ≤ d by omega_using [h]]
  · simp [show k ≤ d by omega_using [h, hk], show ¬ d < 64 by omega_using [h], h, bit,
      show d - 64 + (64 - k) = d - k by omega_using [h, hk]]

theorem ψ_split (v : BitVec 64) {k : Nat} (hk : k < 64) :
    x ^ k * ψ v = ψ (v >>> k) + x ^ 64 * ψ (v <<< (64 - k)) := by
  have h := congrArg (AdjoinRoot.mk g) (gp_split v hk)
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  exact h

/-- What leaves a doubleword leaves the next one too. -/
theorem carry_shl (q : BitVec 64) {s : Nat} (hs : 7 ≤ s) :
    (q <<< 63 ^^^ q <<< 62 ^^^ q <<< 57) <<< s = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [show i - s < 63 by omega_using [hi, hs], show i - s < 62 by omega_using [hi, hs],
    show i - s < 57 by omega_using [hi, hs]]

theorem ψ_zero : ψ 0#64 = 0 := by simp only [ψ, gp_zero', map_zero]

theorem vdword_zero (e : Nat) : vdword 0#128 e = 0#64 := by
  simp only [VG.Proof.Gcm.Clmul.vdword, BitVec.extractLsb'_zero]

theorem ρ_fold (lo hi : BitVec 128) : ρ (fold lo hi) = φ hi + x ^ 128 * φ lo := by
  simp only [fold]
  rw [ρ_ext8_self, φ_v, φ_v hi, φ_v lo]
  simp only [vdword_xor, vdword_ext8_0, vdword_ext8_1, vdword_zero, sl, sr, VG.Proof.Gcm.Clmul.ofVDwords,
    vdword_append_0,
    vdword_append_1, BitVec.xor_zero]
  generalize vdword lo 0 = a0
  generalize vdword lo 1 = a1
  generalize vdword hi 0 = h0
  generalize vdword hi 1 = h1
  have hw : ∀ s, 7 ≤ s → (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) <<< s = a1 <<< s := fun s hs => by
    rw [BitVec.shiftLeft_xor_distrib, carry_shl a0 hs, BitVec.xor_zero]
  have w1 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 1) (by decide)
  have w2 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 2) (by decide)
  have w7 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 7) (by decide)
  rw [hw _ (by decide)] at w1 w2 w7
  have b1 := ψ_split a0 (k := 1) (by decide)
  have b2 := ψ_split a0 (k := 2) (by decide)
  have b7 := ψ_split a0 (k := 7) (by decide)
  have hW : ψ (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) =
      ψ a1 + ψ (a0 <<< 63) + ψ (a0 <<< 62) + ψ (a0 <<< 57) := by
    simp only [ψ_xor]; ring
  simp only [ψ_xor]
  simp only [Nat.reduceSub] at w1 w2 w7 b1 b2 b7
  linear_combination (-1 : Q) * w1 + (-1 : Q) * w2 + (-1 : Q) * w7 + (-x ^ 64) * b1 + (-x ^ 64) * b2 +
    (-x ^ 64) * b7 + (x + x ^ 2 + x ^ 7) * hW +
    (-(ψ a1 + ψ (a0 <<< 63) + ψ (a0 <<< 62) + ψ (a0 <<< 57) + x ^ 64 * ψ a0)) * x128

theorem ρ_reduceN (p : Prod) : ρ (reduceN p) = p.val := by
  rw [reduceN, ρ_fold, φ_xor, φ_xor, φ_ext8, φ_ext8, Prod.val, φ_v p.mid, vdword_zero, vdword_zero, ψ_zero]
  ring

theorem mulN_eq (a t : BitVec 128) : mulN a (ext8 t t) = mulV a t := by
  apply Pmull.ρ_inj
  rw [ρ_mulV, mulN, ρ_reduceN, Prod.val, φ_xor, φ_xor, φ_polyMul, φ_polyMul, φ_polyMul, ψ_xor, ψ_xor,
    vdword_ext8_0, vdword_ext8_1, ρ, φ_v t]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword t 1) + ψ (vdword a 1) * ψ (vdword t 0))) * two_Q

/-! ## The key -/

/-- `sshr #63` is the mask of the top bit. -/
theorem sshr63 (q : BitVec 64) : q.sshiftRight 63 = if q.getMsbD 0 then BitVec.allOnes 64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (if 63 + i < 64 then q.getLsbD (63 + i) else q.msb) = q.msb := by
    split_ifs with h
    · obtain rfl : i = 0 := by omega_using [h]
      rw [BitVec.msb_eq_getLsbD_last]
    · rfl
  rw [BitVec.getLsbD_sshiftRight, hm, decide_eq_false (by omega_using [hi]), Bool.not_false, Bool.true_and]
  change q.getMsbD 0 = _
  cases q.getMsbD 0
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true]

theorem and_ofVDwords (a b c d : BitVec 64) :
    ofVDwords a b &&& ofVDwords c d = ofVDwords (a &&& c) (b &&& d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Gcm.Clmul.ofVDwords, BitVec.getLsbD_and, BitVec.getLsbD_append]
  by_cases h : i < 64 <;> simp only [h, ite_true, ite_false]

/-- The reduction constant under the mask of the top bit of the low
doubleword is its `pmull` by that bit. -/
theorem mask_poly (a : BitVec 128) :
    ofVDwords ((vdword a 0).sshiftRight 63) ((vdword a 1).sshiftRight 63) &&& ofVDwords poly 0#64 =
      polyMul (vdword a 0 >>> 63) poly := by
  rw [and_ofVDwords, ushr63, sshr63, BitVec.and_zero]
  cases (vdword a 0).getMsbD 0
  · simp only [Bool.false_eq_true, ite_false, BitVec.zero_and]
    exact (polyMul_zero_left poly).symm
  · simp only [ite_true, BitVec.allOnes_and]
    decide +kernel

theorem twistV_ρ' (a : BitVec 128) : x * ρ (twistV a) = ρ a := by
  rw [twistV, mask_poly]; exact twistV_ρ a

/-- `twist` computes the key of `vg_ghash_aes`. -/
theorem twistV_key (H : Spec.Gcm.Block) :
    ext8 (twistV (ext8 H H)) (twistV (ext8 H H)) = Pmull.keyV H := by
  apply φ_inj
  apply Pmull.x_cancel
  rw [φ_ext8_self, twistV_ρ', ρ_ext8_self, Pmull.keyV, φ_ext8_self, ρ_mulV, ρ_ext8_self]
  linear_combination (-(φ H)) * x2_φ_xInv2

theorem arith : Arith :=
  ⟨cl_polyMul, fun a b _ hi => msb_cl1 a b hi, mulN_eq, twistV_key, Pmull.mulV_keyV⟩

end VG.Proof.Gcm.AArch64.Neon

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

/-- `vg_ghash_prepared8_aes`, with PMULL. -/
def GhashPreparedImpl.aes : GhashPreparedImpl where
  fn := ⟨"vg_ghash_prepared8_aes", Impl.Gcm.AArch64.Pmull.ghashP⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashP_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashP_ct
  keepsV := by decide +kernel

/-- `vg_ghash_with_powers_aes`, with PMULL. -/
def GhashWithImpl.aes : GhashWithImpl where
  fn := ⟨"vg_ghash_with_powers_aes", Impl.Gcm.AArch64.Pmull.ghashW⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashW_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashW_ct
  keepsV := by decide +kernel

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.AArch64.ghash⟩
  noFrames := by lit_decide
  ok := Proof.Gcm.AArch64.ghash_correct
  ct := Proof.Gcm.AArch64.ghash_ct
  keepsV := by lit_decide
  suffix := ""
  features := []

/-- `vg_ghash_aes`, with PMULL (which Rust's `aes` feature stands for, with
the AES instructions). -/
def aes : GhashImpl where
  fn := ⟨"vg_ghash_aes", Impl.Gcm.AArch64.Pmull.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghash_correct
  ct := Proof.Gcm.AArch64.Pmull.ghash_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  pmull := true
  prepared := some .aes
  withPowers := some .aes

/-- `vg_ghash_neon`, with the `pmull` of bytes, which AdvSIMD has without
PMULL. -/
def neon : GhashImpl where
  fn := ⟨"vg_ghash_neon", Impl.Gcm.AArch64.Neon.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Neon.ghash_correct Proof.Gcm.AArch64.Neon.arith
  ct := Proof.Gcm.AArch64.Neon.ghash_ct
  keepsV := by decide +kernel
  suffix := "_neon"
  features := []

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .aes => .aes
  | .neon => .neon

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.key, v.gh.impl, v.stitch⟩

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64 VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Stitch (pa pb pk pl)

/-- `kadd` adds `x · a · s` (`s` as loaded) to the product. -/
theorem val_fix_kadd (p : Prod) (a s : BitVec 128) :
    (fix (kadd p a s (kkey s))).val = (fix p).val + x * ρ a * ρ s := by
  simp only [fix, kadd, kkey, Prod.val, φ_xor, φ_polyMul, ψ_xor, ρ]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword s 0) + ψ (vdword a 1) * ψ (vdword s 1))) *
    two_Q

theorem vdword_ofVDwords_0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := vdword_append_0 _ _
theorem vdword_ofVDwords_1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := vdword_append_1 _ _

theorem val_fix_zero : (fix ⟨0#128, 0#128, 0#128⟩).val = 0 := by
  simp only [fix, Prod.val, BitVec.xor_zero, φ_zero', mul_zero, add_zero]

/-- A pair's products, from the keys of the table. -/
theorem val_kpair (pv : Prod) (H : Spec.Gcm.Block) (a₁ a₂ : BitVec 128) (k l : Nat) :
    (fix (kpair pv a₁ (ext8 (pp H k) (pp H k)) a₂ (ext8 (pp H l) (pp H l)) (kpack H k l))).val =
      (fix pv).val + ρ a₁ * φ H ^ k + ρ a₂ * φ H ^ l := by
  rw [kpair, kpack, vdword_ofVDwords_0, vdword_ofVDwords_1, val_fix_kadd, val_fix_kadd, ρ_ext8_self,
    ρ_ext8_self, ← x_φ_pp H k, ← x_φ_pp H l]
  ring

theorem gh8Ok : Gh8Ok := by
  intro H y b
  apply ρ_inj
  simp only [gh8V, pk, pl, pa, pb, show (0 : Nat) = 3 ↔ False by decide, show (1 : Nat) = 3 ↔ False by decide,
    show (2 : Nat) = 3 ↔ False by decide, ite_false, ite_true, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  rw [ρ_reduce, val_kpair, val_kpair, val_kpair, val_kpair, val_fix_zero, ρ_ext8_self, ρ_xor]
  simp only [ρ_ext8_self, Spec.Gcm.ghashFrom, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor]
  ring

end VG.Proof.Gcm.AArch64.Stitch

namespace VG.Proof.AesGcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.AesGcm.AArch64 (GcmImpl GcmVariant gcmWn gcmInitWn gcmInitWn_cases gcmWn_cases openCode openToCode sealCode sealCode_framedW)

/-- `initOk` at `gcmInitWn v`. -/
theorem initOkW (v : GcmImpl) :
    ScrubAllOk (Spec.Gcm.initContract abi (gcmInitWn v)) (gcmInitWn v) (Spec.Gcm.initSig.retBits abi.ptrBits) :=
  initOk _ (by rcases gcmInitWn_cases v with h | h <;> rw [h] <;> decide)

/-- What `scrubAllOf` needs of `init` in its frame, with each variant's
implementations: evaluated here. -/
theorem initSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmInitWn g.impl) .x3
        (Impl.AesGcm.AArch64.init g.impl.callees)) (gcmInitWn g.impl) (Spec.Gcm.initSig.retBits abi.ptrBits)
      clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmInitWn g.impl) .x3
        (Impl.AesGcm.AArch64.init g.impl.callees)) (gcmInitWn g.impl) (Spec.Gcm.initSig.retBits abi.ptrBits)
      clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `open`. -/
theorem openSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 32) 2 (openCode g.impl))
      (gcmWn g.impl + 32) (Spec.Gcm.openSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 32) 2 (openCode g.impl))
        (gcmWn g.impl + 32) (Spec.Gcm.openSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `open_to`. -/
theorem openToSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 48) 4 (openToCode g.impl))
      (gcmWn g.impl + 48) (Spec.Gcm.openToSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 48) 4 (openToCode g.impl))
        (gcmWn g.impl + 48) (Spec.Gcm.openToSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `seal`. -/
theorem sealSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 16) 1 (sealCode g.impl))
      (gcmWn g.impl + 16) (Spec.Gcm.sealSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 16) 1 (sealCode g.impl))
        (gcmWn g.impl + 16) (Spec.Gcm.sealSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- The code of `vg_aes_gcm_seal` of the variant `g` as it is registered
(`ScrubAll.scrubAllOf`): in its frame, then its registers cleared and its
stack zeroed. -/
def sealScrubbed (g : GcmVariant) : Prog isa :=
  Impl.Residue.AArch64.scrubAll (gcmWn g.impl + 16) (Spec.Gcm.sealSig.retBits abi.ptrBits) clear
    (Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 16) 1 (sealCode g.impl))

/-- Its frames, the scrub's included, use at most the 2576 bytes that
`vg_aes_gcm_seal_gather` leaves to its call. -/
theorem sealScrubbed_depth (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    16 * (sealScrubbed g).aarch64Depth ≤ 2576 := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      decide (16 * (sealScrubbed g).aarch64Depth ≤ 2576)) = true := by lit_decide
  exact of_decide_eq_true (List.all_eq_true.mp h g hg)

/-- The scrubbed code of `seal`, against the contract its frame is proved
with, which `vg_aes_gcm_seal_gather`'s proof uses. -/
theorem sealScrubbed_verified (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants)
    (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Verified AArch64.target (sealScrubbed g) (Proof.AesGcm.sealRoundsContract AArch64.abi (gcmWn g.impl + 16)) :=
  Verified.scrubAllOfV (sealCode_framedW g.impl hMK) (sealRoundsOk _) (sealSide g hg)

/-- The instance of `seal` that `seal_gather` calls: the scrubbed code
registered as `vg_aes_gcm_seal` of `g`. -/
def sealFnW (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants)
    (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn .plain :=
  if h : gcmWn g.impl = 768 then
    .plain784 ⟨Spec.Gcm.sealApi.name ++ g.impl.suffix, sealScrubbed g⟩
      (by have := sealScrubbed_verified g hg hMK; rw [h] at this; exact this) (sealScrubbed_depth g hg)
  else
    .plain ⟨Spec.Gcm.sealApi.name ++ g.impl.suffix, sealScrubbed g⟩
      (by
        have := sealScrubbed_verified g hg hMK
        rw [(gcmWn_cases g.impl).resolve_left h] at this; exact this)
      (sealScrubbed_depth g hg)

theorem sealFnW_fn (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants)
    (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    (sealFnW g hg hMK).fn = ⟨Spec.Gcm.sealApi.name ++ g.impl.suffix, sealScrubbed g⟩ := by
  unfold sealFnW; split <;> rfl

/-- `initSide`, for `seal_gather`, which calls the scrubbed `seal`. -/
theorem sealGatherSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants)
    (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    scrubSide (Impl.AesGcm.AArch64.SealGather.sealGather (sealFnW g hg hMK).fn) 2592
      (Spec.Gcm.sealGatherSig.retBits abi.ptrBits) clear [] = true := by
  rw [sealFnW_fn]
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.AesGcm.AArch64.SealGather.sealGather ⟨Spec.Gcm.sealApi.name ++ g.impl.suffix, sealScrubbed g⟩)
        2592 (Spec.Gcm.sealGatherSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `sealBasePw` of the variants without code that reads the powers. -/
theorem sealBasePwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode g.impl)) 2576 (Spec.Gcm.sealWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode g.impl)) 2576 (Spec.Gcm.sealWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `openBasePw` of the variants without code that reads the powers. -/
theorem openBasePwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode g.impl)) 2592 (Spec.Gcm.openWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode g.impl)) 2592 (Spec.Gcm.openWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `openToBasePw` of the variants without code that reads the powers. -/
theorem openToBasePwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode g.impl)) 2608 (Spec.Gcm.openToWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode g.impl)) 2608 (Spec.Gcm.openToWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg


/-- `initSide`, for `seal_with_powers` of the variants with code that reads the powers, `w`. -/
theorem sealPwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) (w : GhashWithImpl)
    (hw : w ∈ g.impl.gh.withPowers) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 2 (sealPwCode g.impl w))
      (gcmPwWn g.impl + 32) (Spec.Gcm.sealWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g => g.impl.gh.withPowers.all fun w =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 2 (sealPwCode g.impl w))
        (gcmPwWn g.impl + 32) (Spec.Gcm.sealWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  have h₁ := List.all_eq_true.mp h g hg
  rw [Option.mem_def.mp hw, Option.all_some] at h₁
  exact h₁

/-- `initSide`, for `open_with_powers` of the variants with code that reads the powers, `w`. -/
theorem openPwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) (w : GhashWithImpl)
    (hw : w ∈ g.impl.gh.withPowers) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 3 (openPwCode g.impl w))
      (gcmPwWn g.impl + 32) (Spec.Gcm.openWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g => g.impl.gh.withPowers.all fun w =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 3 (openPwCode g.impl w))
        (gcmPwWn g.impl + 32) (Spec.Gcm.openWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  have h₁ := List.all_eq_true.mp h g hg
  rw [Option.mem_def.mp hw, Option.all_some] at h₁
  exact h₁

/-- `initSide`, for `openTo_with_powers` of the variants with code that reads the powers, `w`. -/
theorem openToPwSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) (w : GhashWithImpl)
    (hw : w ∈ g.impl.gh.withPowers) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 48) 5 (openToPwCode g.impl w))
      (gcmPwWn g.impl + 48) (Spec.Gcm.openToWithPowersSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g => g.impl.gh.withPowers.all fun w =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 48) 5 (openToPwCode g.impl w))
        (gcmPwWn g.impl + 48) (Spec.Gcm.openToWithPowersSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  have h₁ := List.all_eq_true.mp h g hg
  rw [Option.mem_def.mp hw, Option.all_some] at h₁
  exact h₁


/-- `initSide`, for `vg_aes_gcm_store_powers` without the instructions of `FEAT_PMULL`. -/
theorem storePowersSide :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 80 .x2 Impl.Gcm.AArch64.keyPowers) 80
      (Spec.Gcm.storePowersSig.retBits abi.ptrBits) clear [] = true := by lit_decide


/-- `initSide`, for `vg_aes_gcm_stream_init`. -/
theorem streamInitSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x4 (Impl.AesGcm.AArch64.streamInit g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x4 (Impl.AesGcm.AArch64.streamInit g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `vg_aes_gcm_stream_aad`. -/
theorem streamAadSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x5 (Impl.AesGcm.AArch64.streamAad g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x5 (Impl.AesGcm.AArch64.streamAad g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `vg_aes_gcm_stream_encrypt`. -/
theorem streamEncryptSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamEncrypt g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamEncrypt g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamDecrypt g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamDecrypt g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamCryptSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `vg_aes_gcm_stream_finish`. -/
theorem streamFinishSide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x6 (Impl.AesGcm.AArch64.streamFinish g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamFinishSig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x6 (Impl.AesGcm.AArch64.streamFinish g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamFinishSig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

/-- `initSide`, for `vg_aes_gcm_stream_verify`. -/
theorem streamVerifySide (g : GcmVariant) (hg : g ∈ Proof.Variants.AesGcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamVerify g.impl.callees))
      (gcmWn g.impl) (Spec.Gcm.streamVerifySig.retBits abi.ptrBits) clear [] = true := by
  have h : (Proof.Variants.AesGcm.AArch64.variants.all fun g =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamVerify g.impl.callees))
        (gcmWn g.impl) (Spec.Gcm.streamVerifySig.retBits abi.ptrBits) clear []) = true := by lit_decide
  exact List.all_eq_true.mp h g hg

end VG.Proof.AesGcm.AArch64.Scrub

/-! ## Without secret residue

The postconditions read the memory on return only within the buffers
(`Proof.Sm4Gcm.*PostOut_local`), and the code of each variant, in its frame,
leaves no secret in the registers it does not clear (`*Side`). -/

namespace VG.Proof.Sm4Gcm.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem initOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.initContract abi stack) stack (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.initSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.initPostOut_local _)

theorem sealOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.sealContract abi stack) stack (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.sealSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.sealPostOut_local _)

theorem openOk (stack : Nat) :
    ScrubAllOk (Spec.Sm4.Gcm.openContract abi stack) stack (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Sm4.Gcm.openSig) (Proof.Sm4Gcm.openPostOut_local _)

theorem streamEncryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamEncryptContract abi stack) stack (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamEncryptPostOut_local _)

theorem streamDecryptOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamDecryptContract abi stack) stack (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamCryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamDecryptPostOut_local _)

theorem streamFinishOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamFinishContract abi stack) stack (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamFinishSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamFinishPostOut_local _)

theorem streamVerifyOk (stack : Nat) (hW : 0 < stack) :
    ScrubAllOk (Spec.Sm4.Gcm.streamVerifyContract abi stack) stack (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.Gcm.streamVerifySig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sm4Gcm.streamVerifyPostOut_local _)

/-- The stacks of the stream functions and of `init`, of 4032 bytes: their
frames of 768 and their callees'. -/
theorem pos4032 : 0 < 4032 := by decide

/-- `init` of the variant `v` returns without secret residue in its frame. -/
theorem initSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.initSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `seal` of the variant `v` returns without secret residue in its frame. -/
theorem sealSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4048 (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4048 (Spec.Sm4.Gcm.sealSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `open` of the variant `v` returns without secret residue in its frame. -/
theorem openSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4048 (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4048 (Spec.Sm4.Gcm.openSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamEncrypt` of the variant `v` returns without secret residue in its frame. -/
theorem streamEncryptSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamDecrypt` of the variant `v` returns without secret residue in its frame. -/
theorem streamDecryptSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamCryptSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamFinish` of the variant `v` returns without secret residue in its frame. -/
theorem streamFinishSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x5 (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamFinishSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamVerify` of the variant `v` returns without secret residue in its frame. -/
theorem streamVerifySide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
      4032 (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch 768 .x6 (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : Proof.Sm4Gcm.AArch64.GcmImpl).callees))
        4032 (Spec.Sm4.Gcm.streamVerifySig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamInit` of the variant `v` returns without secret residue in its frame. -/
theorem streamInitSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x4 (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
      (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x4 (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
        (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamInitSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

/-- `streamAad` of the variant `v` returns without secret residue in its frame. -/
theorem streamAadSide (v : Proof.Sm4Gcm.AArch64.GcmVariant) (hv : v ∈ Proof.Variants.Sm4Gcm.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x5 (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
      (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear [] = true := by
  have h : (Proof.Variants.Sm4Gcm.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratch (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) .x5 (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees))
        (Proof.AesGcm.AArch64.gcmWn (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) (Spec.Gcm.streamAadSig.retBits abi.ptrBits) Proof.AesGcm.AArch64.Scrub.clear []) = true := by lit_decide
  exact List.all_eq_true.mp h v hv

end VG.Proof.Sm4Gcm.AArch64.Scrub

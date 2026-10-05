import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Gb`. -/
section

/-!
# Argon2 on x86-64 with AVX-512: P on both halves of four registers

The AVX-512 code of `round` (`Impl/Argon2/X86_64/CompressAvx512.lean`)
writes only vector registers, so a block of it runs as `zrun`, a function of
the state. Each step of GB is proven on every quadword `k < 8` at once (`qz`,
quadword `k` of a register), then GB (`gb_qz`), and P on the sixteen words
in each half of `zmm0`–`zmm3` (`round_words`), through
`Proof.Argon2.permute_lanes`.
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (vreg)
open VG.Proof.Poly1305.X86_64.Avx512 (qz qz_zbin div2_lt)
open VG.Proof.Poly1305.X86_64.Avx2 (qword_paddq qword_pmuludq sel4 sel4_lt qword256_perm qword_app0
  qword_app1)
open VG.Proof.Argon2.X86_64.Avx2 (qword_pxor addMul_eq cases_div4 sel4_39 sel4_4e sel4_93)
open VG.Proof.Argon2 (mix mixColumns rotRows mixAt)

/-! ## Blocks of AVX-512 instructions -/

/-- Run instructions that write only vector registers. -/
def zrun : List ZOp → State → State
  | [], s => s
  | o :: os, s => VG.Proof.Argon2.X86_64.Avx512.zrun os (o.exec s)

theorem runBlock_zops (os : List ZOp) (s : State) :
    runBlock isa (os.map .zop) s = some (VG.Proof.Argon2.X86_64.Avx512.zrun os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem zrun_append (a b : List ZOp) (s : State) : VG.Proof.Argon2.X86_64.Avx512.zrun (a ++ b) s = VG.Proof.Argon2.X86_64.Avx512.zrun b (VG.Proof.Argon2.X86_64.Avx512.zrun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

@[simp] theorem State.setZ_mxcsr (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).mxcsr = s.mxcsr := by
  cases s; rfl

theorem ZOp.exec_mxcsr (o : ZOp) (s : State) : (o.exec s).mxcsr = s.mxcsr := by
  cases o <;> rfl

@[simp] theorem zrun_gpr (os : List ZOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx512.zrun os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_gpr o s)

@[simp] theorem zrun_mem (os : List ZOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx512.zrun os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_mem o s)

@[simp] theorem zrun_rd (os : List ZOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx512.zrun os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_rd o s)

@[simp] theorem zrun_wr (os : List ZOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx512.zrun os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_wr o s)

@[simp] theorem zrun_mxcsr (os : List ZOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx512.zrun os s).mxcsr = s.mxcsr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_mxcsr o s)

/-! ## Quadwords of registers after an instruction -/

theorem qz_lane (s : State) (r : XReg) (k : Nat) : qword (s.zlane r (k / 2)) (k % 2) = qz s r k :=
  rfl

theorem qword_rorQwords (x : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 2) :
    qword (rorQwords x n) i = (qword x i).rotateRight (n.toNat % 64) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [rorQwords, qword_app0, qword_app1]

theorem zlane_vprorq (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vprorq d a n).exec s).zlane r i = if r = d then rorQwords (s.zlane a i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => rorQwords (s.zlane a i) n) hi]

theorem qz_vprorq (s : State) (d a r : XReg) (n : BitVec 8) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vprorq d a n).exec s) r k =
      if r = d then (qz s a k).rotateRight (n.toNat % 64) else qz s r k := by
  simp only [qz, VG.Proof.Argon2.X86_64.Avx512.zlane_vprorq _ _ _ _ _ (div2_lt hk)]
  split
  · exact VG.Proof.Argon2.X86_64.Avx512.qword_rorQwords _ _ (Nat.mod_lt _ (by decide))
  · rfl

/-- Quadword `j` of two lanes. -/
theorem qword256_append (a b : BitVec 128) {j : Nat} (hj : j < 4) :
    qword256 (a ++ b) j = if j < 2 then qword b j else qword a (j - 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [qword256, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  by_cases h2 : j < 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (show 64 * j + m < 128 by omega)), qword, BitVec.getLsbD_extractLsb']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 64 * j + m < 128 by omega)), qword, BitVec.getLsbD_extractLsb',
      show 64 * j + m - 128 = 64 * (j - 2) + m by omega]

/-- Quadword `i` of a 128-bit piece of a 256-bit value. -/
theorem qword_extract256 (Y : BitVec 256) (l : Nat) {i : Nat} (hi : i < 2) :
    qword (Y.extractLsb' (128 * l) 128) i = qword256 Y (2 * l + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega)]
  congr 1; omega

theorem zlane_vpermq (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpermq d a o).exec s).zlane r i =
      if r = d then (permQwords (s.zlane a (2 * (i / 2) + 1) ++ s.zlane a (2 * (i / 2))) o).extractLsb'
        (128 * (i % 2)) 128 else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi]
  split
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- `vpermq` permutes the quadwords of each half. -/
theorem qz_vpermq (s : State) (d a r : XReg) (o : BitVec 8) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vpermq d a o).exec s) r k =
      if r = d then qz s a (4 * (k / 4) + sel4 o.toNat (k % 4)) else qz s r k := by
  simp only [qz, VG.Proof.Argon2.X86_64.Avx512.zlane_vpermq _ _ _ _ _ (div2_lt hk)]
  split
  · have hs := sel4_lt o.toNat (k % 4)
    rw [VG.Proof.Argon2.X86_64.Avx512.qword_extract256 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2 % 2) + k % 2 = k % 4 by omega, qword256_perm _ _ (Nat.mod_lt _ (by decide)),
      VG.Proof.Argon2.X86_64.Avx512.qword256_append _ _ hs]
    split <;> congr 2 <;> omega
  · rfl

/-! ## The steps of GB, on each quadword -/

def addMulOps (a b : XReg) : List ZOp :=
  [.zbin .vpmuludq .xmm4 a b, .zbin .vpaddq a a b, .zbin .vpaddq .xmm4 .xmm4 .xmm4,
    .zbin .vpaddq a a .xmm4]

def xorRorOps (d a : XReg) (n : BitVec 8) : List ZOp := [.zbin .vpxord d d a, .vprorq d d n]

theorem addMul_qz {a b : XReg} (ha : a ≠ .xmm4) (hb : b ≠ .xmm4) (s : State)
    {r : XReg} (hr : r ≠ .xmm4) {k : Nat} (hk : k < 8) :
    qz (VG.Proof.Argon2.X86_64.Avx512.zrun (VG.Proof.Argon2.X86_64.Avx512.addMulOps a b) s) r k =
      if r = a then Spec.Argon2.addMul (qz s a k) (qz s b k) else qz s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx512.addMulOps, VG.Proof.Argon2.X86_64.Avx512.zrun, qz_zbin _ _ _ _ _ _ hk, ZBinOp.sse, qword_paddq _ _ h2,
    qword_pmuludq _ _ h2, zlane_zbin _ _ _ _ _ _ (div2_lt hk), VG.Proof.Argon2.X86_64.Avx512.qz_lane, hr, ha, hb, ha.symm,
    ite_true, ite_false]
  split
  · rw [addMul_eq]
  · rfl

theorem xorRor_qz (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    qz (VG.Proof.Argon2.X86_64.Avx512.zrun (VG.Proof.Argon2.X86_64.Avx512.xorRorOps d a n) s) r k =
      if r = d then (qz s d k ^^^ qz s a k).rotateRight (n.toNat % 64) else qz s r k := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.xorRorOps, VG.Proof.Argon2.X86_64.Avx512.zrun, VG.Proof.Argon2.X86_64.Avx512.qz_vprorq _ _ _ _ _ hk, qz_zbin _ _ _ _ _ _ hk, ZBinOp.sse,
    qword_pxor, VG.Proof.Argon2.X86_64.Avx512.qz_lane, ite_true]
  split <;> rfl

/-! ## GB -/

abbrev x0 : XReg := .xmm0
abbrev x1 : XReg := .xmm1
abbrev x2 : XReg := .xmm2
abbrev x3 : XReg := .xmm3

def gbOps : List ZOp :=
  VG.Proof.Argon2.X86_64.Avx512.addMulOps VG.Proof.Argon2.X86_64.Avx512.x0 VG.Proof.Argon2.X86_64.Avx512.x1 ++ VG.Proof.Argon2.X86_64.Avx512.xorRorOps VG.Proof.Argon2.X86_64.Avx512.x3 VG.Proof.Argon2.X86_64.Avx512.x0 32 ++ VG.Proof.Argon2.X86_64.Avx512.addMulOps VG.Proof.Argon2.X86_64.Avx512.x2 VG.Proof.Argon2.X86_64.Avx512.x3 ++ VG.Proof.Argon2.X86_64.Avx512.xorRorOps VG.Proof.Argon2.X86_64.Avx512.x1 VG.Proof.Argon2.X86_64.Avx512.x2 24 ++
  VG.Proof.Argon2.X86_64.Avx512.addMulOps VG.Proof.Argon2.X86_64.Avx512.x0 VG.Proof.Argon2.X86_64.Avx512.x1 ++ VG.Proof.Argon2.X86_64.Avx512.xorRorOps VG.Proof.Argon2.X86_64.Avx512.x3 VG.Proof.Argon2.X86_64.Avx512.x0 16 ++ VG.Proof.Argon2.X86_64.Avx512.addMulOps VG.Proof.Argon2.X86_64.Avx512.x2 VG.Proof.Argon2.X86_64.Avx512.x3 ++ VG.Proof.Argon2.X86_64.Avx512.xorRorOps VG.Proof.Argon2.X86_64.Avx512.x1 VG.Proof.Argon2.X86_64.Avx512.x2 63

theorem gb_eq : gb = gbOps.map .zop := rfl

/-- GB on each quadword of `zmm0`–`zmm3`. -/
theorem gb_qz (s : State) {k : Nat} (hk : k < 8) :
    (qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.gbOps s) VG.Proof.Argon2.X86_64.Avx512.x0 k, qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.gbOps s) VG.Proof.Argon2.X86_64.Avx512.x1 k, qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.gbOps s) VG.Proof.Argon2.X86_64.Avx512.x2 k,
      qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.gbOps s) VG.Proof.Argon2.X86_64.Avx512.x3 k) = mix (qz s VG.Proof.Argon2.X86_64.Avx512.x0 k) (qz s VG.Proof.Argon2.X86_64.Avx512.x1 k) (qz s VG.Proof.Argon2.X86_64.Avx512.x2 k) (qz s VG.Proof.Argon2.X86_64.Avx512.x3 k) := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.gbOps, VG.Proof.Argon2.X86_64.Avx512.zrun_append]
  simp (disch := decide) only [VG.Proof.Argon2.X86_64.Avx512.addMul_qz (a := VG.Proof.Argon2.X86_64.Avx512.x0) (b := VG.Proof.Argon2.X86_64.Avx512.x1) (by decide) (by decide) _ _ hk,
    VG.Proof.Argon2.X86_64.Avx512.addMul_qz (a := VG.Proof.Argon2.X86_64.Avx512.x2) (b := VG.Proof.Argon2.X86_64.Avx512.x3) (by decide) (by decide) _ _ hk, VG.Proof.Argon2.X86_64.Avx512.xorRor_qz _ _ _ _ _ hk,
    ↓reduceIte, reduceCtorEq]
  rfl

/-! ## P on each half -/

def diagOps : List ZOp := [.vpermq VG.Proof.Argon2.X86_64.Avx512.x1 VG.Proof.Argon2.X86_64.Avx512.x1 0x39, .vpermq VG.Proof.Argon2.X86_64.Avx512.x2 VG.Proof.Argon2.X86_64.Avx512.x2 0x4e, .vpermq VG.Proof.Argon2.X86_64.Avx512.x3 VG.Proof.Argon2.X86_64.Avx512.x3 0x93]
def undiagOps : List ZOp := [.vpermq VG.Proof.Argon2.X86_64.Avx512.x1 VG.Proof.Argon2.X86_64.Avx512.x1 0x93, .vpermq VG.Proof.Argon2.X86_64.Avx512.x2 VG.Proof.Argon2.X86_64.Avx512.x2 0x4e, .vpermq VG.Proof.Argon2.X86_64.Avx512.x3 VG.Proof.Argon2.X86_64.Avx512.x3 0x39]
def roundOps : List ZOp := VG.Proof.Argon2.X86_64.Avx512.gbOps ++ VG.Proof.Argon2.X86_64.Avx512.diagOps ++ VG.Proof.Argon2.X86_64.Avx512.gbOps ++ VG.Proof.Argon2.X86_64.Avx512.undiagOps

theorem round_eq : round = roundOps.map .zop := rfl

/-- The sixteen words in half `h` of `zmm0`–`zmm3`: word `4i + q` is quadword
`4h + q` of `vreg i`. -/
def words (s : State) (h : Nat) : Vector Word 16 :=
  Vector.ofFn fun j => qz s (vreg (j.val / 4)) (4 * h + j.val % 4)

theorem words_get (s : State) (h j : Nat) (hj : j < 16) :
    (VG.Proof.Argon2.X86_64.Avx512.words s h)[j] = qz s (vreg (j / 4)) (4 * h + j % 4) := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.words, Vector.getElem_ofFn]

theorem gb_words (s : State) {h : Nat} (hh : h < 2) :
    VG.Proof.Argon2.X86_64.Avx512.words (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.gbOps s) h = mixColumns (VG.Proof.Argon2.X86_64.Avx512.words s h) := by
  apply Vector.ext
  intro j hj
  have g := VG.Proof.Argon2.X86_64.Avx512.gb_qz s (k := 4 * h + j % 4) (by omega)
  rw [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega),
    VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega), VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega), VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem diag_words (s : State) {h : Nat} (hh : h < 2) :
    VG.Proof.Argon2.X86_64.Avx512.words (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.diagOps s) h = rotRows 1 (VG.Proof.Argon2.X86_64.Avx512.words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega]
  have e4 : (4 * h + j % 4) / 4 = h := by omega
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega
  simp only [VG.Proof.Argon2.X86_64.Avx512.diagOps, VG.Proof.Argon2.X86_64.Avx512.zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, VG.Proof.Argon2.X86_64.Avx512.qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) {h : Nat} (hh : h < 2) :
    VG.Proof.Argon2.X86_64.Avx512.words (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.undiagOps s) h = rotRows 3 (VG.Proof.Argon2.X86_64.Avx512.words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega]
  have e4 : (4 * h + j % 4) / 4 = h := by omega
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega
  simp only [VG.Proof.Argon2.X86_64.Avx512.undiagOps, VG.Proof.Argon2.X86_64.Avx512.zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, VG.Proof.Argon2.X86_64.Avx512.qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega

/-- P on the sixteen words of each half of `zmm0`–`zmm3`. -/
theorem round_words (s : State) {h : Nat} (hh : h < 2) :
    VG.Proof.Argon2.X86_64.Avx512.words (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.roundOps s) h = permute (VG.Proof.Argon2.X86_64.Avx512.words s h) := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.roundOps, VG.Proof.Argon2.X86_64.Avx512.zrun_append]
  rw [Proof.Argon2.permute_lanes, VG.Proof.Argon2.X86_64.Avx512.undiag_words _ hh, VG.Proof.Argon2.X86_64.Avx512.gb_words _ hh, VG.Proof.Argon2.X86_64.Avx512.diag_words _ hh, VG.Proof.Argon2.X86_64.Avx512.gb_words _ hh]

end VG.Proof.Argon2.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Mem`. -/
section

/-!
# Argon2 on x86-64 with AVX-512: 64-byte loads and stores

Quadword `k` of a register after a 64-byte load (`qz_load`), of a register
as a stored value (`zmm_qz`), and a word of memory after a 64-byte store
(`read_write512`); the block P permutes as scratch holds it, by pairs of
columns (`cv`, with the word of each quadword of each 64-byte chunk:
`cvIdx`).
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Proof.Argon2.X86_64 (off Scratch ea_at)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep)
open VG.Proof.Poly1305.X86_64.Avx512 (qz)

/-! ## Registers -/

theorem qz_setMem (s : State) (m : Mem) (r : XReg) (k : Nat) : qz (s.setMem m) r k = qz s r k := by
  simp only [qz, State.setMem_zlane]

theorem qword_extract512 (v : BitVec 512) (l : Nat) {i : Nat} (hi : i < 2) :
    qword (v.extractLsb' (128 * l) 128) i = v.extractLsb' (64 * (2 * l + i)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega)]
  congr 1; omega

theorem pick4_extract (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128) l = v.extractLsb' (128 * l) 128 := by
  have := pick4_lanes (fun l => v.extractLsb' (128 * l) 128) hl
  simpa only [Nat.reduceMul] using this

theorem qz_setZ_load (s : State) (d r : XReg) (v : BitVec 512) {k : Nat} (hk : k < 8) :
    qz (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)) r k = if r = d then v.extractLsb' (64 * k) 64 else qz s r k := by
  simp only [qz, State.zlane_setZ _ _ _ _ _ _ _ (show k / 2 < 4 by omega)]
  split
  · rw [VG.Proof.Argon2.X86_64.Avx512.pick4_extract _ (show k / 2 < 4 by omega), VG.Proof.Argon2.X86_64.Avx512.qword_extract512 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2) + k % 2 = k by omega]
  · rfl

theorem qz_load (s : State) (d r : XReg) (m : Mem) (a : Addr) {k : Nat} (hk : k < 8) :
    qz (s.setZ d ((m.readW a 512).extractLsb' 0 128) ((m.readW a 512).extractLsb' 128 128)
      ((m.readW a 512).extractLsb' 256 128) ((m.readW a 512).extractLsb' 384 128)) r k =
      if r = d then m.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qz s r k := by
  rw [VG.Proof.Argon2.X86_64.Avx512.qz_setZ_load _ _ _ _ hk, show 64 * k = 8 * (8 * k) by omega,
    readW_extract _ _ (k := 8 * k) (n := 8) (by omega)]

/-- Quadword `k` of a register, as a stored value. -/
theorem extract64_split (x : BitVec 512) (a : Nat) :
    x.extractLsb' a 64 = x.extractLsb' (a + 32) 32 ++ x.extractLsb' a 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rename_i h
    rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_true (show j - 32 < 32 by omega), Bool.true_and]
    congr 1; omega

theorem zmm_qz (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    (s.zmm r).extractLsb' (64 * k) 64 = qz s r k := by
  have e0 : (s.zmm r).extractLsb' (64 * k) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2)) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2)) (by omega) (by omega)
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2))) = 64 * k by omega] at this
    exact this
  have e1 : (s.zmm r).extractLsb' (64 * k + 32) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2) + 1) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2) + 1) (by omega) (by omega)
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2) + 1)) = 64 * k + 32 by omega] at this
    exact this
  rw [qz, Proof.Poly1305.X86_64.Avx2.qword_eq, VG.Proof.Argon2.X86_64.Avx512.extract64_split, e0, e1]

/-! ## Memory -/

/-- A word at `p + d` after 64 bytes are written at `p + e`. -/
theorem read_write512 (m : Mem) (p : Addr) {d e : Nat} (hd : d + 8 ≤ 4096) (he : e + 64 ≤ 4096)
    (h8 : d % 8 = 0) (he8 : e % 8 = 0) (v : BitVec 512) :
    (m.writeW (off p e) v).readW (off p d) 64 =
      if e ≤ d ∧ d < e + 64 then v.extractLsb' (64 * ((d - e) / 8)) 64 else m.readW (off p d) 64 := by
  split
  · rename_i h
    rw [show off p d = off p e + BitVec.ofNat 64 (8 * ((d - e) / 8)) from
      (Offset.add_add_eq p (by omega)).symm]
    refine (readW_writeW_inside _ _ v (k := 8 * ((d - e) / 8)) (n := 8) (by omega) (by decide)).trans ?_
    rw [show 8 * (8 * ((d - e) / 8)) = 64 * ((d - e) / 8) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- The offset in `[1024, 2048)` of scratch of word `i` of the block P
permutes: in register `i / 32` of columns `2c`, `2c + 1` (`c = i % 16 / 4`),
quadword `cvQ i`. -/
def cvQ (i : Nat) : Nat := 4 * (i % 16 / 2 % 2) + 2 * (i / 16 % 2) + i % 2

def cvOff (i : Nat) : Nat := 256 * (i % 16 / 4) + 64 * (i / 32) + 8 * VG.Proof.Argon2.X86_64.Avx512.cvQ i

/-- The block P permutes, as scratch holds it. -/
def cv (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => m.readW (off p (1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff i.val)) 64

theorem cv_get (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) :
    (VG.Proof.Argon2.X86_64.Avx512.cv m p)[i] = m.readW (off p (1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff i)) 64 := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.cv, Vector.getElem_ofFn]

/-- Where the words are, as bounded facts. -/
theorem cvOff_lt : ∀ i < 128, VG.Proof.Argon2.X86_64.Avx512.cvOff i + 8 ≤ 1024 ∧ VG.Proof.Argon2.X86_64.Avx512.cvOff i % 8 = 0 := by decide

theorem cvOff_in : ∀ i < 128, ∀ c < 4, ∀ k < 4,
    (1024 + 256 * c + 64 * k ≤ 1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff i ∧ 1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff i < 1024 + 256 * c + 64 * k + 64 ↔
      i % 16 / 4 = c ∧ i / 32 = k) := by decide

theorem cvOff_q : ∀ i < 128, (1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff i - (1024 + 256 * (i % 16 / 4) + 64 * (i / 32))) / 8 = VG.Proof.Argon2.X86_64.Avx512.cvQ i := by
  decide

theorem cvQ_lt : ∀ i < 128, VG.Proof.Argon2.X86_64.Avx512.cvQ i < 8 := by decide

/-- The word of quadword `e` of register `k` of columns `2c`, `2c + 1`: word
`4k + e % 4` of column `2c + e / 4`. -/
def cvIdx (c k e : Nat) : Nat := 16 * (2 * k + e % 4 / 2) + 4 * c + 2 * (e / 4) + e % 2

theorem cvIdx_colIndex {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) :
    (colIndex ⟨2 * c + e / 4, by omega⟩ ⟨4 * k + e % 4, by omega⟩).val = VG.Proof.Argon2.X86_64.Avx512.cvIdx c k e := by
  simp only [colIndex, VG.Proof.Argon2.X86_64.Avx512.cvIdx]; omega

theorem cvOff_cvIdx : ∀ c < 4, ∀ k < 4, ∀ e < 8, VG.Proof.Argon2.X86_64.Avx512.cvOff (VG.Proof.Argon2.X86_64.Avx512.cvIdx c k e) = 256 * c + 64 * k + 8 * e := by
  decide

theorem cvIdx_lt {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) : VG.Proof.Argon2.X86_64.Avx512.cvIdx c k e < 128 := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.cvIdx]; omega

/-- A word of `cv` after a 64-byte write to the chunk at `colOff c k`. -/
theorem cv_write512 (m : Mem) (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) (v : BitVec 512)
    (i : Nat) (hi : i < 128) :
    (VG.Proof.Argon2.X86_64.Avx512.cv (m.writeW (off p (colOff c k)) v) p)[i] =
      if i % 16 / 4 = c ∧ i / 32 = k then v.extractLsb' (64 * VG.Proof.Argon2.X86_64.Avx512.cvQ i) 64 else (VG.Proof.Argon2.X86_64.Avx512.cv m p)[i] := by
  have ho := VG.Proof.Argon2.X86_64.Avx512.cvOff_lt i hi
  rw [VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ hi, VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ hi, colOff, VG.Proof.Argon2.X86_64.Avx512.read_write512 _ _ (by omega) (by omega)
    (by omega) (by omega)]
  by_cases h : i % 16 / 4 = c ∧ i / 32 = k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((VG.Proof.Argon2.X86_64.Avx512.cvOff_in i hi c hc k hk).mpr h)),
      ite_eq_left_of_eq_true _ _ (eq_true h), ← h.1, ← h.2, VG.Proof.Argon2.X86_64.Avx512.cvOff_q i hi]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (VG.Proof.Argon2.X86_64.Avx512.cvOff_in i hi c hc k hk).mp h)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The register of columns `2c`, `2c + 1` at `colOff c k`, as `cv` holds it. -/
theorem cv_chunk (m : Mem) (p : Addr) {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) :
    m.readW (off p (colOff c k) + BitVec.ofNat 64 (8 * e)) 64 =
      (VG.Proof.Argon2.X86_64.Avx512.cv m p)[VG.Proof.Argon2.X86_64.Avx512.cvIdx c k e]'(VG.Proof.Argon2.X86_64.Avx512.cvIdx_lt hc hk he) := by
  rw [VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ (VG.Proof.Argon2.X86_64.Avx512.cvIdx_lt hc hk he), VG.Proof.Argon2.X86_64.Avx512.cvOff_cvIdx c hc k hk e he, Offset.add_add, colOff,
    show 1024 + 256 * c + 64 * k + 8 * e = 1024 + (256 * c + 64 * k + 8 * e) by omega]

end VG.Proof.Argon2.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Rows`. -/
section

/-!
# Argon2 on x86-64 with AVX-512: P on two rows

Rows `2p` and `2p + 1` of R (`[0, 1024)` of scratch, `blockAt`) are loaded
into the halves of `zmm0`–`zmm3` (`loadRows_ok`), permuted (`round_words`)
and stored to their places in the block P permutes, as scratch holds it by
pairs of columns (`cv`, `storeRows_ok`): `rows_ok`.
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (vreg)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at blockAt_get)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl cases_div4)
open VG.Proof.Poly1305.X86_64.Avx512 (qz qz_vshufi32x4)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)
open VG.Proof.Argon2 (gather gather_get)

/-! ## Selectors of `vshufi32x4` -/

theorem sel4_44 {m : Nat} (hm : m < 4) : sel4 (0x44 : BitVec 8).toNat m = m % 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_ee {m : Nat} (hm : m < 4) : sel4 (0xee : BitVec 8).toNat m = 2 + m % 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_d8 {m : Nat} (hm : m < 4) : sel4 (0xd8 : BitVec 8).toNat m = 2 * (m % 2) + m / 2 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_88 {m : Nat} (hm : m < 4) : sel4 (0x88 : BitVec 8).toNat m = 2 * (m % 2) := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_dd {m : Nat} (hm : m < 4) : sel4 (0xdd : BitVec 8).toNat m = 2 * (m % 2) + 1 := by
  rcases cases4 hm with rfl | rfl | rfl | rfl <;> rfl

theorem vreg_ne4 (i : Nat) : vreg i ≠ .xmm4 := by unfold vreg; split <;> decide

@[simp] theorem State.setMem_mxcsr' (s : State) (m : Mem) : (s.setMem m).mxcsr = s.mxcsr := by
  cases s; rfl

theorem setMem_vkeep (s : State) (m : Mem) : VKeep s (s.setMem m) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem zop_vkeep (o : ZOp) (s : State) : VKeep s (o.exec s) :=
  ⟨ZOp.exec_gpr o s, ZOp.exec_rd o s, ZOp.exec_wr o s, ZOp.exec_mxcsr o s⟩

theorem setZ_vkeep (s : State) (r : XReg) (a b c d : BitVec 128) : VKeep s (s.setZ r a b c d) :=
  ⟨State.setZ_gpr _ _ _ _ _ _, State.setZ_rd _ _ _ _ _ _, State.setZ_wr _ _ _ _ _ _,
    State.setZ_mxcsr _ _ _ _ _ _⟩

theorem zrun_vkeep (os : List ZOp) (s : State) : VKeep s (VG.Proof.Argon2.X86_64.Avx512.zrun os s) :=
  ⟨VG.Proof.Argon2.X86_64.Avx512.zrun_gpr os s, VG.Proof.Argon2.X86_64.Avx512.zrun_rd os s, VG.Proof.Argon2.X86_64.Avx512.zrun_wr os s, VG.Proof.Argon2.X86_64.Avx512.zrun_mxcsr os s⟩

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.roundOps s)) :
    WP isa (.block round) s Q := by
  rw [VG.Proof.Argon2.X86_64.Avx512.round_eq]
  exact WP.of_runBlock ⟨_, VG.Proof.Argon2.X86_64.Avx512.runBlock_zops _ _, h⟩

/-! ## Loading two rows -/

theorem loadRows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadRows pp)) s fun t =>
      (∀ h (hh : h < 2), VG.Proof.Argon2.X86_64.Avx512.words t h = gather (rowIndex ⟨2 * pp + h, by omega⟩) (blockAt s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := hs.read (d := 256 * pp) (n := 64) (by omega)
  have r1 := hs.read (d := 256 * pp + 64) (n := 64) (by omega)
  have r2 := hs.read (d := 256 * pp + 128) (n := 64) (by omega)
  have r3 := hs.read (d := 256 * pp + 192) (n := 64) (by omega)
  apply WP.of_runBlock
  simp only [loadRows, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, VG.Proof.Argon2.X86_64.ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r2, r3, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, by simp only [ZOp.exec_mem, State.setZ_mem], ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ hj, show (gather (rowIndex ⟨2 * pp + h, by omega⟩) (blockAt s.mem p))[j] =
        (blockAt s.mem p)[rowIndex ⟨2 * pp + h, by omega⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      blockAt_get]
    simp only [rowIndex]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
      simp (disch := omega) only [vreg, qz_vshufi32x4, VG.Proof.Argon2.X86_64.Avx512.qz_load, VG.Proof.Argon2.X86_64.Avx512.sel4_44, VG.Proof.Argon2.X86_64.Avx512.sel4_ee, ↓reduceIte,
        reduceCtorEq, show (4 * 0 + j % 4) / 2 < 2 by omega, show ¬ (4 * 1 + j % 4) / 2 < 2 by omega] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;> omega
  · exact (((((((VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _)

/-! ## Storing two rows -/

/-- The working half of scratch contains the chunk at `colOff c k`. -/
theorem colOff_contains (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (colOff c k)) 64 :=
  Offset.contains p (by unfold colOff; omega) (by unfold colOff; omega) (by omega)

theorem colOff_write {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions s.wr (off p (colOff c k)) 64 :=
  hs.write (by unfold colOff; omega)

/-- The quadword `vshufi32x4` with `0xd8` moves to quadword `cvQ i`. -/
theorem rowQ : ∀ i < 128, 2 * sel4 (0xd8 : BitVec 8).toNat (VG.Proof.Argon2.X86_64.Avx512.cvQ i / 2) + VG.Proof.Argon2.X86_64.Avx512.cvQ i % 2 =
    4 * (i / 16 % 2) + i % 4 := by decide

def storeRow (pp k : Nat) : List Instr :=
  [.zop (.vshufi32x4 .xmm4 (vreg k) (vreg k) 0xd8), .vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rcx (colOff k pp)) .xmm4]

theorem storeRows_eq (pp : Nat) : storeRows pp = (List.range 4).flatMap (VG.Proof.Argon2.X86_64.Avx512.storeRow pp) := rfl

/-- What storing register `k` of rows `2p`, `2p + 1` leaves. -/
structure RowStored (p : Addr) (pp n : Nat) (s t : State) : Prop where
  cv : ∀ i (hi : i < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[i] = if i % 16 / 4 < n ∧ i / 32 = pp then
    qz s (vreg (i % 16 / 4)) (4 * (i / 16 % 2) + i % 4) else (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i]
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VKeep s t
  regs : ∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e

theorem storeRow_ok {pp k : Nat} (hp : pp < 4) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (VG.Proof.Argon2.X86_64.Avx512.storeRow pp k)) s fun t =>
      (∀ i (hi : i < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[i] = if i % 16 / 4 = k ∧ i / 32 = pp then
        qz s (vreg k) (4 * (i / 16 % 2) + i % 4) else (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧
      (∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e) := by
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx512.storeRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, VG.Proof.Argon2.X86_64.ea_at,
    ZOp.exec_wr, ZOp.exec_gpr, ZOp.exec_mem, hs.reg, VG.Proof.Argon2.X86_64.Avx512.colOff_write hs hk hp, ite_true,
    Option.some.injEq, exists_eq_left', State.setMem_mem]
  refine ⟨fun i hi => ?_, ?_, (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _), fun r hr e he => ?_⟩
  · rw [VG.Proof.Argon2.X86_64.Avx512.cv_write512 _ _ hk hp _ _ hi]
    split
    · rw [VG.Proof.Argon2.X86_64.Avx512.zmm_qz _ _ (VG.Proof.Argon2.X86_64.Avx512.cvQ_lt i hi), qz_vshufi32x4 _ _ _ _ _ _ (VG.Proof.Argon2.X86_64.Avx512.cvQ_lt i hi),
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_self]
      exact congrArg _ (VG.Proof.Argon2.X86_64.Avx512.rowQ i hi)
    · rfl
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx512.colOff_contains p hk hp)
  · rw [VG.Proof.Argon2.X86_64.Avx512.qz_setMem, qz_vshufi32x4 _ _ _ _ _ _ he, ite_eq_right_of_eq_false _ _ (eq_false hr)]

theorem storeRows_prefix {pp : Nat} (hp : pp < 4) (n : Nat) (hn : n ≤ 4) {s : State} {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block ((List.range n).flatMap (VG.Proof.Argon2.X86_64.Avx512.storeRow pp))) s (VG.Proof.Argon2.X86_64.Avx512.RowStored p pp n s) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by simp, Frame.refl _ _, VKeep.refl s, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨hc, hf, hk, hr⟩
    refine (VG.Proof.Argon2.X86_64.Avx512.storeRow_ok hp (k := n) (by omega) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk', hr'⟩
    refine ⟨fun i hi => ?_, hf.trans hf', hk.trans hk', fun r h e he => (hr' r h e he).trans (hr r h e he)⟩
    rw [hc' i hi, hr _ (VG.Proof.Argon2.X86_64.Avx512.vreg_ne4 n) _ (by omega), hc i hi]
    by_cases h1 : i % 16 / 4 = n ∧ i / 32 = pp
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h1.1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : i % 16 / 4 < n ∧ i / 32 = pp
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-! ## Two rows -/

/-- P on rows `2p` and `2p + 1` of R, stored to `cv`. -/
theorem rows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (rows pp) s fun t =>
      (∀ i (hi : i < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[i] = if i / 32 = pp then
        (permute (gather (rowIndex ⟨i / 16, by omega⟩) (blockAt s.mem p)))[i % 16]'(by omega)
        else (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold rows
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx512.loadRows_ok hp hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine VG.Proof.Argon2.X86_64.Avx512.round_then ?_
  have hs2 : Scratch (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (VG.Proof.Argon2.X86_64.Avx512.zrun_vkeep _ _)
  rw [VG.Proof.Argon2.X86_64.Avx512.storeRows_eq]
  refine (VG.Proof.Argon2.X86_64.Avx512.storeRows_prefix hp 4 (by decide) hs2).mono ?_
  rintro t ⟨hc, hf, hk, -⟩
  rw [VG.Proof.Argon2.X86_64.Avx512.zrun_mem, hmem1] at hc hf
  refine ⟨fun i hi => ?_, hf, hk1.trans ((VG.Proof.Argon2.X86_64.Avx512.zrun_vkeep _ _).trans hk)⟩
  rw [hc i hi]
  by_cases h : i / 32 = pp
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i / 16 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[i % 16]'(by omega))
      ((VG.Proof.Argon2.X86_64.Avx512.round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (show i % 16 < 16 by omega), show i % 16 % 4 = i % 4 by omega] at e
    rw [e]
    have er : (⟨2 * pp + i / 16 % 2, by omega⟩ : Fin 8) = ⟨i / 16, by omega⟩ := Fin.ext (by simp only; omega)
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Cols`. -/
section

/-!
# Argon2 on x86-64 with AVX-512: P on two columns

The registers of columns `2c` and `2c + 1` are four consecutive 64-byte
chunks of `cv` (`loadCols_ok`); P on both halves of them (`round_words`),
stored back (`storeCols_ok`), is P on both columns (`cols_ok`).
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (vreg)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl cases_div4)
open VG.Proof.Poly1305.X86_64.Avx512 (qz)
open VG.Proof.Argon2 (gather gather_get)

/-- Where quadword `4h + j % 4` of register `j / 4` of columns `2c`, `2c + 1`
is: word `j` of column `2c + h`. -/
theorem colQ : ∀ c < 4, ∀ h < 2, ∀ j < 16,
    256 * c + 64 * (j / 4) + 8 * (4 * h + j % 4) = VG.Proof.Argon2.X86_64.Avx512.cvOff (16 * (j / 2) + 2 * (2 * c + h) + j % 2) := by
  decide

@[simp] theorem State.setMem_zmm (s : State) (m : Mem) (r : XReg) : (s.setMem m).zmm r = s.zmm r := by
  cases s; rfl

theorem loadCols_eq (c : Nat) : loadCols c =
    [.vmovdqu32Load .xmm0 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 0)), .vmovdqu32Load .xmm1 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 1)),
      .vmovdqu32Load .xmm2 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 2)), .vmovdqu32Load .xmm3 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 3))] := rfl

theorem storeCols_eq (c : Nat) : storeCols c =
    [.vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 0)) .xmm0, .vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 1)) .xmm1,
      .vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 2)) .xmm2, .vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rcx (colOff c 3)) .xmm3] := rfl

theorem colOff_read {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (off p (colOff c k)) 64 :=
  hs.read (by unfold colOff; omega)

theorem loadCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadCols c)) s fun t =>
      (∀ h (hh : h < 2), VG.Proof.Argon2.X86_64.Avx512.words t h = gather (colIndex ⟨2 * c + h, by omega⟩) (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx512.loadCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, VG.Proof.Argon2.X86_64.ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg,
    VG.Proof.Argon2.X86_64.Avx512.colOff_read hs hc (show 0 < 4 by decide), VG.Proof.Argon2.X86_64.Avx512.colOff_read hs hc (show 1 < 4 by decide),
    VG.Proof.Argon2.X86_64.Avx512.colOff_read hs hc (show 2 < 4 by decide), VG.Proof.Argon2.X86_64.Avx512.colOff_read hs hc (show 3 < 4 by decide), ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, trivial, ?_⟩
  · apply Vector.ext
    intro j hj
    rw [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ hj, show (gather (colIndex ⟨2 * c + h, by omega⟩) (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p))[j] =
        (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[colIndex ⟨2 * c + h, by omega⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      Fin.getElem_fin, VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ (colIndex _ _).isLt]
    have hq := VG.Proof.Argon2.X86_64.Avx512.colQ c hc h hh j hj
    simp only [colIndex]
    rcases cases_div4 hj with e | e | e | e <;> rw [e] at hq ⊢ <;>
      simp (disch := omega) only [vreg, VG.Proof.Argon2.X86_64.Avx512.qz_load, ↓reduceIte, reduceCtorEq] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;> unfold colOff <;> omega
  · exact (((VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)

theorem storeCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCols c)) s fun t =>
      (∀ i (hi : i < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[i] = if i % 16 / 4 = c then
        qz s (vreg (i / 32)) (VG.Proof.Argon2.X86_64.Avx512.cvQ i) else (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx512.storeCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, VG.Proof.Argon2.X86_64.ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, hs.reg,
    VG.Proof.Argon2.X86_64.Avx512.colOff_write hs hc (show 0 < 4 by decide), VG.Proof.Argon2.X86_64.Avx512.colOff_write hs hc (show 1 < 4 by decide),
    VG.Proof.Argon2.X86_64.Avx512.colOff_write hs hc (show 2 < 4 by decide), VG.Proof.Argon2.X86_64.Avx512.colOff_write hs hc (show 3 < 4 by decide), ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hq := VG.Proof.Argon2.X86_64.Avx512.cvQ_lt i hi
    rw [VG.Proof.Argon2.X86_64.Avx512.cv_write512 _ _ hc (show 3 < 4 by decide) _ _ hi, VG.Proof.Argon2.X86_64.Avx512.cv_write512 _ _ hc (show 2 < 4 by decide) _ _ hi,
      VG.Proof.Argon2.X86_64.Avx512.cv_write512 _ _ hc (show 1 < 4 by decide) _ _ hi, VG.Proof.Argon2.X86_64.Avx512.cv_write512 _ _ hc (show 0 < 4 by decide) _ _ hi]
    simp only [State.setMem_zmm, VG.Proof.Argon2.X86_64.Avx512.zmm_qz _ _ hq]
    by_cases h : i % 16 / 4 = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have : i / 32 = 0 ∨ i / 32 = 1 ∨ i / 32 = 2 ∨ i / 32 = 3 := by omega
      rcases this with e | e | e | e <;> simp only [e, h, vreg, and_self, ite_true, ite_false,
        show (0 : Nat) ≠ 1 by decide, show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 3 by decide,
        show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 3 by decide,
        and_false]
    · simp only [h, false_and, ite_false]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx512.colOff_contains p hc (by decide))
      | exact Frame.refl _ _)
  · exact (((VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _)

/-- P on columns `2c` and `2c + 1` of `cv`. -/
theorem cols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (cols c) s fun t =>
      VG.Proof.Argon2.X86_64.Avx512.cv t.mem p = permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold cols
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx512.loadCols_ok hc hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine VG.Proof.Argon2.X86_64.Avx512.round_then ?_
  have hs2 : Scratch (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (VG.Proof.Argon2.X86_64.Avx512.zrun_vkeep _ _)
  refine (VG.Proof.Argon2.X86_64.Avx512.storeCols_ok hc hs2).mono ?_
  rintro t ⟨hc', hf, hk⟩
  rw [VG.Proof.Argon2.X86_64.Avx512.zrun_mem, hmem1] at hc' hf
  refine ⟨?_, hf, hk1.trans ((VG.Proof.Argon2.X86_64.Avx512.zrun_vkeep _ _).trans hk)⟩
  apply Vector.ext
  intro i hi
  rw [hc' i hi, Proof.Argon2.colPair_get hc _ i hi]
  by_cases h : i % 16 / 4 = c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i % 16 / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[2 * (i / 16) + i % 2]'(by omega))
      ((VG.Proof.Argon2.X86_64.Avx512.round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [VG.Proof.Argon2.X86_64.Avx512.words_get _ _ _ (show 2 * (i / 16) + i % 2 < 16 by omega),
      show (2 * (i / 16) + i % 2) / 4 = i / 32 by omega,
      show 4 * (i % 16 / 2 % 2) + (2 * (i / 16) + i % 2) % 4 = VG.Proof.Argon2.X86_64.Avx512.cvQ i by simp only [VG.Proof.Argon2.X86_64.Avx512.cvQ]; omega] at e
    rw [e]
    have er : (⟨2 * c + i % 16 / 2 % 2, by omega⟩ : Fin 8) = ⟨i % 16 / 2, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Ends`. -/
section

/-!
# Argon2 on x86-64 with AVX-512: the first and last XOR

`initChunk k` writes 64 bytes of X XOR Y to R, and `finishChunk n k` writes
words `8n…8n+7` of rows `2k` and `2k + 1` of the output: `cv` XOR R. Each
is proven for any prefix of its chunks (`init_prefix`, `finish_prefix`).
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Proof.Argon2.X86_64 (off Scratch ea_at Inputs blockAt_get xorBlock_get input_unchanged
  scratch_unchanged)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl qword_pxor ifp ifn)
open VG.Proof.Poly1305.X86_64.Avx512 (qz qz_zbin qz_vshufi32x4)
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

theorem cv_idx (m : Mem) (p : Addr) {a b : Nat} (h : a = b) (ha : a < 128) (hb : b < 128) :
    (VG.Proof.Argon2.X86_64.Avx512.cv m p)[a]'ha = (VG.Proof.Argon2.X86_64.Avx512.cv m p)[b]'hb := by
  subst h; rfl

/-! ## R -/

theorem initChunk_ok {k : Nat} (hk : k < 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block (initChunk k)) s fun t => ∃ v : BitVec 512,
      (∀ q < 8, v.extractLsb' (64 * q) 64 =
        s.mem.readW (off x (64 * k + 8 * q)) 64 ^^^ s.mem.readW (off y (64 * k + 8 * q)) 64) ∧
      t.mem = s.mem.writeW (off p (64 * k)) v ∧ VKeep s t := by
  have lx : InRegions (s.rd ++ s.wr) (off x (64 * k)) 64 :=
    ⟨_, hin.xread, Offset.contains_base x (by omega) (by omega)⟩
  have ly : InRegions (s.rd ++ s.wr) (off y (64 * k)) 64 :=
    ⟨_, hin.yread, Offset.contains_base y (by omega) (by omega)⟩
  have w := hs.write (d := 64 * k) (n := 64) (by omega)
  apply WP.of_runBlock
  simp only [initChunk, z, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512,
    State.store512_eq, VG.Proof.Argon2.X86_64.ea_at, State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem,
    ZOp.exec_gpr, ZOp.exec_mem, ZOp.exec_wr, hs.reg, hin.xreg, hin.yreg, lx, ly, w, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ((((VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans
    (VG.Proof.Argon2.X86_64.Avx512.zop_vkeep _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _))⟩
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
  simp (disch := omega) only [VG.Proof.Argon2.X86_64.Avx512.zmm_qz _ _ hq, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor,
    VG.Proof.Argon2.X86_64.Avx512.qz_lane, VG.Proof.Argon2.X86_64.Avx512.qz_load, ↓reduceIte, reduceCtorEq, Offset.add_add]

/-- The chunks `k < n` of R hold `r`. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val / 8 < n → m.readW (off p (8 * i.val)) 64 = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat} (hn : n < 16)
    (h : VG.Proof.Argon2.X86_64.Avx512.Initialized m p r n) {v : BitVec 512} (hv : ∀ q < 8, ∀ hi : 8 * n + q < 128,
      v.extractLsb' (64 * q) 64 = r[8 * n + q]'hi) :
    VG.Proof.Argon2.X86_64.Avx512.Initialized (m.writeW (off p (64 * n)) v) p r (n + 1) := by
  intro i hi
  have hi' := i.isLt
  rw [VG.Proof.Argon2.X86_64.Avx512.read_write512 _ p (by omega) (by omega) (by omega) (by omega)]
  by_cases e : i.val / 8 = n
  · have q := hv (i.val % 8) (Nat.mod_lt _ (by decide)) (by omega)
    simp only [show 8 * n + i.val % 8 = i.val by omega] at q
    rw [ifp (by omega), show (8 * i.val - 64 * n) / 8 = i.val % 8 by omega, q]
    rfl
  · rw [ifn (by omega)]
    exact h i (by omega)

/-- Initialize the first `n` chunks of R, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initChunk)) s fun t =>
      VG.Proof.Argon2.X86_64.Avx512.Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VKeep s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, VKeep.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (VG.Proof.Argon2.X86_64.Avx512.initChunk_ok (by omega) (hs.of_vkeep hk) (hin.of_vkeep hk)).mono ?_
    rintro u ⟨v, hv, hmem, hk'⟩
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hmem]
      refine VG.Proof.Argon2.X86_64.Avx512.initialized_step (by omega) ht fun q hq hi => ?_
      rw [hv q hq, show 64 * n + 8 * q = 8 * (8 * n + q) by omega,
        input_unchanged hf hin.xsep ⟨8 * n + q, hi⟩, input_unchanged hf hin.ysep ⟨8 * n + q, hi⟩]
      simp only [xorBlock, Vector.getElem_zipWith, blockAt, Vector.getElem_ofFn]
      rfl
    · rw [hmem]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))

/-- R, initialized. -/
theorem initialized_all {m : Mem} {p : Addr} {r : Block} (h : VG.Proof.Argon2.X86_64.Avx512.Initialized m p r 16) :
    blockAt m p = r := by
  apply Vector.ext; intro i hi
  have := h ⟨i, hi⟩ (by simp only; omega)
  rw [← blockAt_get m p ⟨i, hi⟩] at this
  exact this

/-! ## The output -/

/-- The words of `cv` that `vshufi32x4` with `0x88` and `0xdd` join. -/
theorem finQ : ∀ n < 2, ∀ k < 4, ∀ q < 8,
    VG.Proof.Argon2.X86_64.Avx512.cvIdx (2 * n + q / 4) k (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) = 32 * k + 8 * n + q ∧
    VG.Proof.Argon2.X86_64.Avx512.cvIdx (2 * n + q / 4) k (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) =
      32 * k + 16 + 8 * n + q := by
  decide

/-- Quadword `q` of `vshufi32x4 d, a, b, sel`, from the halves of `a` and `b`. -/
theorem qz_shuf (s : State) (d a b : XReg) (n : BitVec 8) {q : Nat} (hq : q < 8) :
    qz ((ZOp.vshufi32x4 d a b n).exec s) d q =
      (if q < 4 then qz s a else qz s b) (2 * sel4 n.toNat (q / 2) + q % 2) := by
  rw [qz_vshufi32x4 _ _ _ _ _ _ hq, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  by_cases h : q < 4
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h)]

def joinOps : List ZOp :=
  [.vshufi32x4 .xmm2 .xmm0 .xmm1 0x88, .vshufi32x4 .xmm3 .xmm0 .xmm1 0xdd,
    .zbin .vpxord .xmm2 .xmm2 .xmm4, .zbin .vpxord .xmm3 .xmm3 .xmm5]

theorem join_qz2 (s : State) {q : Nat} (hq : q < 8) :
    qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.joinOps s) .xmm2 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm4 q := by
  simp only [VG.Proof.Argon2.X86_64.Avx512.joinOps, VG.Proof.Argon2.X86_64.Avx512.zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, VG.Proof.Argon2.X86_64.Avx512.qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]

theorem join_qz3 (s : State) {q : Nat} (hq : q < 8) :
    qz (VG.Proof.Argon2.X86_64.Avx512.zrun VG.Proof.Argon2.X86_64.Avx512.joinOps s) .xmm3 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm5 q := by
  have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
  simp only [VG.Proof.Argon2.X86_64.Avx512.joinOps, VG.Proof.Argon2.X86_64.Avx512.zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, VG.Proof.Argon2.X86_64.Avx512.qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]
  split <;> simp (disch := omega) only [qz_vshufi32x4, reduceCtorEq, ↓reduceIte]

def finLoads (n k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm0 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff (2 * n) k)),
    .vmovdqu32Load .xmm1 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff (2 * n + 1) k)),
    .vmovdqu32Load .xmm4 (VG.Impl.Argon2.X86_64.at_ .rcx (256 * k + 64 * n)),
    .vmovdqu32Load .xmm5 (VG.Impl.Argon2.X86_64.at_ .rcx (256 * k + 128 + 64 * n))]

def finStores (n k : Nat) : List Instr :=
  [.vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rdx (256 * k + 64 * n)) .xmm2,
    .vmovdqu32Store (VG.Impl.Argon2.X86_64.at_ .rdx (256 * k + 128 + 64 * n)) .xmm3]

theorem finishChunk_eq (n k : Nat) :
    finishChunk n k = VG.Proof.Argon2.X86_64.Avx512.finLoads n k ++ joinOps.map .zop ++ VG.Proof.Argon2.X86_64.Avx512.finStores n k := rfl

theorem finLoads_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (VG.Proof.Argon2.X86_64.Avx512.finLoads n k)) s fun t =>
      (∀ e (he : e < 8), qz t .xmm0 e = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[VG.Proof.Argon2.X86_64.Avx512.cvIdx (2 * n) k e]'(by simp only [VG.Proof.Argon2.X86_64.Avx512.cvIdx]; omega)) ∧
      (∀ e (he : e < 8), qz t .xmm1 e = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[VG.Proof.Argon2.X86_64.Avx512.cvIdx (2 * n + 1) k e]'(by simp only [VG.Proof.Argon2.X86_64.Avx512.cvIdx]; omega)) ∧
      (∀ q < 8, qz t .xmm4 q = s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q < 8, qz t .xmm5 q = s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := VG.Proof.Argon2.X86_64.Avx512.colOff_read hs (c := 2 * n) (k := k) (by omega) hk
  have r1 := VG.Proof.Argon2.X86_64.Avx512.colOff_read hs (c := 2 * n + 1) (k := k) (by omega) hk
  have r4 := hs.read (d := 256 * k + 64 * n) (n := 64) (by omega)
  have r5 := hs.read (d := 256 * k + 128 + 64 * n) (n := 64) (by omega)
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx512.finLoads, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, VG.Proof.Argon2.X86_64.ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r4, r5, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun e he => ?_, fun e he => ?_, fun q hq => ?_, fun q hq => ?_, trivial,
    (((VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx512.setZ_vkeep _ _ _ _ _ _)⟩
  · simp only [VG.Proof.Argon2.X86_64.Avx512.qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact VG.Proof.Argon2.X86_64.Avx512.cv_chunk _ _ (by omega) hk he
  · simp only [VG.Proof.Argon2.X86_64.Avx512.qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact VG.Proof.Argon2.X86_64.Avx512.cv_chunk _ _ (by omega) hk he
  · simp only [VG.Proof.Argon2.X86_64.Avx512.qz_load _ _ _ _ _ hq, reduceCtorEq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega))
  · simp only [VG.Proof.Argon2.X86_64.Avx512.qz_load _ _ _ _ _ hq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega))

theorem finStores_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {out : Addr}
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (VG.Proof.Argon2.X86_64.Avx512.finStores n k)) s fun t =>
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) (s.zmm .xmm2)).writeW
        (off out (256 * k + 128 + 64 * n)) (s.zmm .xmm3) ∧ VKeep s t := by
  have w1 : InRegions s.wr (off out (256 * k + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
  have w2 : InRegions s.wr (off out (256 * k + 128 + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx512.finStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, VG.Proof.Argon2.X86_64.ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setMem_zmm, ho, w1, w2, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _).trans (VG.Proof.Argon2.X86_64.Avx512.setMem_vkeep _ _)⟩

theorem finishChunk_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finishChunk n k)) s fun t => ∃ v w : BitVec 512,
      (∀ q (hq : q < 8), v.extractLsb' (64 * q) 64 = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[32 * k + 8 * n + q]'(by omega) ^^^
        s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q (hq : q < 8), w.extractLsb' (64 * q) 64 = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[32 * k + 16 + 8 * n + q]'(by omega) ^^^
        s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) v).writeW (off out (256 * k + 128 + 64 * n)) w ∧
      VKeep s t := by
  rw [VG.Proof.Argon2.X86_64.Avx512.finishChunk_eq, WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx512.finLoads_ok hn hk hs).mono ?_
  rintro t1 ⟨h0, h1, h4, h5, hm1, hk1⟩
  refine WP.of_runBlock ⟨_, VG.Proof.Argon2.X86_64.Avx512.runBlock_zops _ _, ?_⟩
  have hk2 := hk1.trans (VG.Proof.Argon2.X86_64.Avx512.zrun_vkeep VG.Proof.Argon2.X86_64.Avx512.joinOps t1)
  refine (VG.Proof.Argon2.X86_64.Avx512.finStores_ok (out := out) hn hk (hk2.gpr ▸ ho) (hk2.wr ▸ hw)).mono ?_
  rintro t ⟨hm, hk3⟩
  refine ⟨_, _, fun q hq => ?_, fun q hq => ?_, by rw [hm, VG.Proof.Argon2.X86_64.Avx512.zrun_mem, hm1], hk2.trans hk3⟩
  · have fq := (VG.Proof.Argon2.X86_64.Avx512.finQ n hn k hk q hq).1
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0x88 : BitVec 8).toNat (q / 2)
    rw [VG.Proof.Argon2.X86_64.Avx512.zmm_qz _ _ hq, VG.Proof.Argon2.X86_64.Avx512.join_qz2 _ hq, h4 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega)]
      rw [show q / 4 = 0 by omega, Nat.add_zero] at fq
      rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega)]
      rw [show q / 4 = 1 by omega] at fq
      rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ fq]
  · have fq := (VG.Proof.Argon2.X86_64.Avx512.finQ n hn k hk q hq).2
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
    rw [VG.Proof.Argon2.X86_64.Avx512.zmm_qz _ _ hq, VG.Proof.Argon2.X86_64.Avx512.join_qz3 _ hq, h5 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega)]
      rw [show q / 4 = 0 by omega, Nat.add_zero] at fq
      rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega)]
      rw [show q / 4 = 1 by omega] at fq
      rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ fq]

end VG.Proof.Argon2.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Lit`. -/
section

/-! # Argon2 compression with AVX-512 as a checked instruction literal -/

namespace VG

materialize_code Impl.Argon2.X86_64.Avx512.compress

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Compress`. -/
section

/-!
# Verified Argon2 block compression on x86-64 with AVX-512

`vg_argon2_compress_avx512` meets `compressContract`, as `vg_argon2_compress`
does: the initial XOR (`init_prefix`), the four pairs of rows and four pairs
of columns (`rows_ok`, `cols_ok`) and the final XOR (`finish_prefix`)
compose to `Spec.Argon2.compress`, between Intel's MXCSR prologue and
epilogue (those of the AVX2 code, and their proofs), which keep MXCSR's
control bits (`ctlOk`). Constant time is checked by evaluation, as for the
scalar code.
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (mxcsrOff)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at Inputs blockAt_get xorBlock_get compressLocal
  initial_agree initialTaint compress_implies original_preserved round_frame scratch_unchanged)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl ifp ifn save_ok set_ok restore_ok blockAt_mx
  ldmxcsr_ok mxR mxR_sub vzeroupper_ok)

/-! ## The output -/

/-- The output chunk of word `i`. -/
def fchunk (i : Nat) : Nat := 4 * (i % 16 / 8) + i / 32

theorem finish_eq : Impl.Argon2.X86_64.Avx512.finish = (List.range 8).flatMap fun i => finishChunk (i / 4) (i % 4) := rfl

/-- Finish the first `m` chunks, preserving scratch. -/
theorem finish_prefix (m : Nat) (hm : m ≤ 8) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range m).flatMap fun i => finishChunk (i / 4) (i % 4))) s fun t =>
      (∀ i (hi : i < 128), VG.Proof.Argon2.X86_64.Avx512.fchunk i < m →
        t.mem.readW (off out (8 * i)) 64 = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i] ^^^ s.mem.readW (off p (8 * i)) 64) ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction m with
  | zero => exact WP.block_nil ⟨fun i hi h => by simp only [VG.Proof.Argon2.X86_64.Avx512.fchunk] at h; omega, Frame.refl _ _, VKeep.refl s⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (VG.Proof.Argon2.X86_64.Avx512.finishChunk_ok (out := out) (n := m / 4) (k := m % 4) (by omega) (by omega) (hs.of_vkeep hk)
      (by rw [hk.gpr]; exact ho) (by rw [hk.wr]; exact hw)).mono ?_
    rintro u ⟨v, w, hv, hw', hmem, hk'⟩
    have cvs : ∀ j (hj : j < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[j] = (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[j] := fun j hj => by
      rw [VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ hj, VG.Proof.Argon2.X86_64.Avx512.cv_get _ _ _ hj,
        scratch_unchanged hf hd (d := 1024 + VG.Proof.Argon2.X86_64.Avx512.cvOff j) (by have := VG.Proof.Argon2.X86_64.Avx512.cvOff_lt j hj; omega)]
    have rs : ∀ d, d + 8 ≤ 4096 → t.mem.readW (off p d) 64 = s.mem.readW (off p d) 64 :=
      fun d hd' => scratch_unchanged hf hd hd'
    refine ⟨fun i hi hc => ?_, ?_, hk.trans hk'⟩
    · rw [hmem, VG.Proof.Argon2.X86_64.Avx512.read_write512 _ out (by omega) (by omega) (by omega) (by omega),
        VG.Proof.Argon2.X86_64.Avx512.read_write512 _ out (by omega) (by omega) (by omega) (by omega)]
      by_cases e : VG.Proof.Argon2.X86_64.Avx512.fchunk i = m
      · simp only [VG.Proof.Argon2.X86_64.Avx512.fchunk] at e
        by_cases h2 : i / 16 % 2 = 1
        · rw [ifp (by omega), show (8 * i - (256 * (m % 4) + 128 + 64 * (m / 4))) / 8 =
            i - (32 * (m % 4) + 16 + 8 * (m / 4)) by omega, hw' _ (by omega)]
          rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ (show 32 * (m % 4) + 16 + 8 * (m / 4) + (i - (32 * (m % 4) + 16 + 8 * (m / 4))) = i by
            omega) _ hi, cvs i hi, show 8 * (32 * (m % 4) + 16 + 8 * (m / 4) +
              (i - (32 * (m % 4) + 16 + 8 * (m / 4)))) = 8 * i by omega, rs _ (by omega)]
        · rw [ifn (by omega), ifp (by omega), show (8 * i - (256 * (m % 4) + 64 * (m / 4))) / 8 =
            i - (32 * (m % 4) + 8 * (m / 4)) by omega, hv _ (by omega)]
          rw [VG.Proof.Argon2.X86_64.Avx512.cv_idx _ _ (show 32 * (m % 4) + 8 * (m / 4) + (i - (32 * (m % 4) + 8 * (m / 4))) = i by
            omega) _ hi, cvs i hi, show 8 * (32 * (m % 4) + 8 * (m / 4) +
              (i - (32 * (m % 4) + 8 * (m / 4)))) = 8 * i by omega, rs _ (by omega)]
      · simp only [VG.Proof.Argon2.X86_64.Avx512.fchunk] at e hc
        rw [ifn (by omega), ifn (by omega)]
        exact ht i hi (by simp only [VG.Proof.Argon2.X86_64.Avx512.fchunk]; omega)
    · rw [hmem]
      exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))

/-! ## The passes -/

/-- P on row `i / 16` of `r`, word `i % 16`. -/
def rowWord (r : Block) (i : Nat) (hi : i < 128) : Word :=
  (permute (gather (rowIndex ⟨i / 16, by omega⟩) r))[i % 16]'(by omega)

theorem rowPass_list (ps : List Nat) (hps : ∀ pp ∈ ps, pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (ps.foldr (fun pp rest => .seq (rows pp) rest) (.block [])) s fun t =>
      (∀ i (hi : i < 128), (VG.Proof.Argon2.X86_64.Avx512.cv t.mem p)[i] = if i / 32 ∈ ps then VG.Proof.Argon2.X86_64.Avx512.rowWord (blockAt s.mem p) i hi
        else (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction ps generalizing s with
  | nil => exact WP.block_nil ⟨fun i hi => by simp, Frame.refl _ _, VKeep.refl s⟩
  | cons pp ps ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.X86_64.Avx512.rows_ok (hps pp List.mem_cons_self) hs).mono ?_
    rintro t ⟨hc, hf, hk⟩
    refine (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk'⟩
    refine ⟨fun i hi => ?_, hf.trans hf', hk.trans hk'⟩
    rw [hc' i hi, hc i hi, original_preserved hf]
    by_cases h1 : i / 32 ∈ ps
    · rw [ifp h1, ifp (List.mem_cons_of_mem _ h1)]
    · rw [ifn h1]
      by_cases h2 : i / 32 = pp
      · rw [ifp h2, ifp (by rw [h2]; exact List.mem_cons_self)]
        rfl
      · rw [ifn h2, ifn (fun h => (List.mem_cons.mp h).elim h2 h1)]

/-- P on columns `2c` and `2c + 1`. -/
def pairStep (b : Block) (c : Nat) : Block :=
  permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
    (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b)

theorem colPass_list (cs : List Nat) (hcs : ∀ c ∈ cs, c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (cs.foldr (fun c rest => .seq (cols c) rest) (.block [])) s fun t =>
      VG.Proof.Argon2.X86_64.Avx512.cv t.mem p = cs.foldl VG.Proof.Argon2.X86_64.Avx512.pairStep (VG.Proof.Argon2.X86_64.Avx512.cv s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction cs generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, VKeep.refl s⟩
  | cons c cs ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.X86_64.Avx512.cols_ok (hcs c List.mem_cons_self) hs).mono ?_
    rintro t ⟨hc, hf, hk⟩
    refine (ih (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    rw [hc', hc, List.foldl_cons]
    rfl

/-! ## G -/

/-- G between the MXCSR prologue and epilogue. -/
theorem body_ok {s : State} {p x y out : Addr} (hs : Scratch s p) (hin : Inputs s x y p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa body s fun t => blockAt t.mem out = Spec.Argon2.compress (blockAt s.mem x) (blockAt s.mem y) ∧
      Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold body
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx512.init_prefix 16 (by decide) hs hin).mono ?_
  rintro s1 ⟨hi1, hf1, hk1⟩
  have horig := VG.Proof.Argon2.X86_64.Avx512.initialized_all hi1
  have hs1 := hs.of_vkeep hk1
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx512.rowPass_list (List.range 4) (fun _ h => List.mem_range.mp h) hs1).mono ?_
  rintro s2 ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx512.colPass_list (List.range 4) (fun _ h => List.mem_range.mp h) (hs1.of_vkeep hk2)).mono ?_
  rintro s3 ⟨hcol, hf3, hk3⟩
  have hk13 := hk1.trans (hk2.trans hk3)
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx512.finish_prefix 8 (by decide) ((hs1.of_vkeep hk2).of_vkeep hk3)
    (by rw [hk13.gpr]; exact ho) (by rw [hk13.wr]; exact hw) hd).mono ?_
  rintro s4 ⟨hfin, hf4, hk4⟩
  refine (vzeroupper_ok s4).mono ?_
  rintro t ⟨hmt, hgt, hrt, hwt, hxt⟩
  have hq : VG.Proof.Argon2.X86_64.Avx512.cv s2.mem p = (List.finRange 8).foldl (fun b r => permuteAt (rowIndex r) b)
      (xorBlock (blockAt s.mem x) (blockAt s.mem y)) := by
    apply Vector.ext; intro i hi
    rw [hrow i hi, ifp (List.mem_range.mpr (by omega)), Proof.Argon2.rows_get _ i hi, horig]
    rfl
  have hz : VG.Proof.Argon2.X86_64.Avx512.cv s3.mem p = (List.finRange 8).foldl (fun b c => permuteAt (colIndex c) b) (VG.Proof.Argon2.X86_64.Avx512.cv s2.mem p) := by
    rw [hcol, Proof.Argon2.foldl_pairs]
    rfl
  have hr3 : blockAt s3.mem p = xorBlock (blockAt s.mem x) (blockAt s.mem y) := by
    rw [original_preserved hf3, original_preserved hf2, horig]
  refine ⟨?_, ?_, fun r _ => ?_, ?_, ?_, ?_⟩
  · apply Vector.ext; intro i hi
    have e := hfin i hi (by simp only [VG.Proof.Argon2.X86_64.Avx512.fchunk]; omega)
    show (blockAt t.mem out)[(⟨i, hi⟩ : Fin 128)] =
      (compress (blockAt s.mem x) (blockAt s.mem y))[(⟨i, hi⟩ : Fin 128)]
    have er := blockAt_get s3.mem p ⟨i, hi⟩
    rw [hr3] at er
    rw [blockAt_get, hmt, e, ← er, hz, hq]
    simp only [Spec.Argon2.compress, xorBlock, Vector.getElem_zipWith, Fin.getElem_fin]
  · rw [hmt]
    have f1 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f4 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s3.mem s4.mem :=
      hf4.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    exact ((f1.trans (round_frame hf2)).trans (round_frame hf3)).trans f4
  · rw [hgt, hk4.gpr, hk13.gpr]
  · rw [hrt, hk4.rd, hk13.rd]
  · rw [hwt, hk4.wr, hk13.wr]
  · rw [hxt, hk4.mxcsr, hk13.mxcsr]

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.Avx512.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  unfold Impl.Argon2.X86_64.Avx512.compress
  apply WP.seq
  refine (save_ok scr).mono ?_
  rintro s1 ⟨h11, hg1, hr1, hw1, -, hf1⟩
  have scr1 : Scratch s1 (s.gpr .rcx) := ⟨hg1 .rcx (by decide), hw1 ▸ scr.wr⟩
  apply WP.seq
  apply WP.seq
  refine (set_ok scr1).mono ?_
  rintro s2 ⟨-, hg2, hr2, hw2, hf2⟩
  have hg12 : ∀ r, r ≠ .rax → r ≠ .r11 → s2.gpr r = s.gpr r :=
    fun r h0 h11 => (hg2 r h0).trans (hg1 r h11)
  have scr2 : Scratch s2 (s.gpr .rcx) := ⟨hg12 .rcx (by decide) (by decide), hw2 ▸ scr1.wr⟩
  have hf12 := hf1.trans hf2
  have inputs : Inputs s2 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨hg12 .rdi (by decide) (by decide), hg12 .rsi (by decide) (by decide),
      by rw [hr2, hw2, hr1, hw1]; simp [hrd], by rw [hr2, hw2, hr1, hw1]; simp [hrd], hx, hy⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx512.body_ok scr2 inputs (out := s.gpr .rdx) (hg12 .rdx (by decide) (by decide))
    (by rw [hw2, hw1, hwr]; simp) hout.symm).mono ?_
  rintro s3 ⟨hpost, hf3, hg3, hr3, hw3, -⟩
  refine WP.of_runBlock ⟨s3, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec], ?_⟩
  have scr3 : Scratch s3 (s.gpr .rcx) := ⟨(hg3 .rcx (by decide)).trans scr2.reg, hw3 ▸ scr2.wr⟩
  have h113 : s3.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [hg3 .r11 (by decide), hg2 .r11 (by decide), h11]
  refine (restore_ok scr3 (by rw [h113]; exact ldmxcsr_ok _)).mono ?_
  rintro t ⟨-, hgt, -, -, hft⟩
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · change blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    rw [blockAt_mx hft hout, hpost, blockAt_mx hf12 hx, blockAt_mx hf12 hy]
  · have h0 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 : r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hgt, hg3 r h0, hg12 r h0 h1]
  · have hmx : ∀ {m m' : Mem}, Frame [mxR (s.gpr .rcx)] m m' →
        Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] m m' := fun h =>
      h.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨_, by simp, mxR_sub _⟩
    rw [hwr]
    exact ((hmx hf12).trans hf3).trans (hmx hft)

theorem compress_ctl : ctlOk Impl.Argon2.X86_64.Avx512.compress = true := by lit_decide

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.Avx512.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := VG.Proof.Argon2.X86_64.Avx512.compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_ctl VG.Proof.Argon2.X86_64.Avx512.compress_ctl he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.Avx512.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ hs ht hp => initial_agree hs ht hp)
    (by taint_decide)

/-- `vg_argon2_compress_avx512` meets the contract of `vg_argon2_compress`. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.Avx512.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Argon2.X86_64.Avx512.compress_correct VG.Proof.Argon2.X86_64.Avx512.compress_ct compress_implies

end VG.Proof.Argon2.X86_64.Avx512

end

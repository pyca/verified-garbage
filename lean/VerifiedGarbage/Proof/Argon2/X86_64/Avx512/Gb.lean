import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Gb
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512

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
  | o :: os, s => zrun os (o.exec s)

theorem runBlock_zops (os : List ZOp) (s : State) :
    runBlock isa (os.map .zop) s = some (zrun os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem zrun_append (a b : List ZOp) (s : State) : zrun (a ++ b) s = zrun b (zrun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

@[simp] theorem State.setZ_mxcsr (s : State) (r : XReg) (a b c d : BitVec 128) :
    (s.setZ r a b c d).mxcsr = s.mxcsr := by
  cases s; rfl

theorem ZOp.exec_mxcsr (o : ZOp) (s : State) : (o.exec s).mxcsr = s.mxcsr := by
  cases o <;> rfl

@[simp] theorem zrun_gpr (os : List ZOp) (s : State) : (zrun os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_gpr o s)

@[simp] theorem zrun_mem (os : List ZOp) (s : State) : (zrun os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_mem o s)

@[simp] theorem zrun_rd (os : List ZOp) (s : State) : (zrun os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_rd o s)

@[simp] theorem zrun_wr (os : List ZOp) (s : State) : (zrun os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (ZOp.exec_wr o s)

@[simp] theorem zrun_mxcsr (os : List ZOp) (s : State) : (zrun os s).mxcsr = s.mxcsr := by
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
  simp only [qz, zlane_vprorq _ _ _ _ _ (div2_lt hk)]
  split
  · exact qword_rorQwords _ _ (Nat.mod_lt _ (by decide))
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
  simp only [qz, zlane_vpermq _ _ _ _ _ (div2_lt hk)]
  split
  · have hs := sel4_lt o.toNat (k % 4)
    rw [qword_extract256 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2 % 2) + k % 2 = k % 4 by omega, qword256_perm _ _ (Nat.mod_lt _ (by decide)),
      qword256_append _ _ hs]
    split <;> congr 2 <;> omega
  · rfl

/-! ## The steps of GB, on each quadword -/

def addMulOps (a b : XReg) : List ZOp :=
  [.zbin .vpmuludq .xmm4 a b, .zbin .vpaddq a a b, .zbin .vpaddq .xmm4 .xmm4 .xmm4,
    .zbin .vpaddq a a .xmm4]

def xorRorOps (d a : XReg) (n : BitVec 8) : List ZOp := [.zbin .vpxord d d a, .vprorq d d n]

theorem addMul_qz {a b : XReg} (ha : a ≠ .xmm4) (hb : b ≠ .xmm4) (s : State)
    {r : XReg} (hr : r ≠ .xmm4) {k : Nat} (hk : k < 8) :
    qz (zrun (addMulOps a b) s) r k =
      if r = a then Spec.Argon2.addMul (qz s a k) (qz s b k) else qz s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [addMulOps, zrun, qz_zbin _ _ _ _ _ _ hk, ZBinOp.sse, qword_paddq _ _ h2,
    qword_pmuludq _ _ h2, zlane_zbin _ _ _ _ _ _ (div2_lt hk), qz_lane, hr, ha, hb, ha.symm,
    ite_true, ite_false]
  split
  · rw [addMul_eq]
  · rfl

theorem xorRor_qz (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    qz (zrun (xorRorOps d a n) s) r k =
      if r = d then (qz s d k ^^^ qz s a k).rotateRight (n.toNat % 64) else qz s r k := by
  simp only [xorRorOps, zrun, qz_vprorq _ _ _ _ _ hk, qz_zbin _ _ _ _ _ _ hk, ZBinOp.sse,
    qword_pxor, qz_lane, ite_true]
  split <;> rfl

/-! ## GB -/

abbrev x0 : XReg := .xmm0
abbrev x1 : XReg := .xmm1
abbrev x2 : XReg := .xmm2
abbrev x3 : XReg := .xmm3

def gbOps : List ZOp :=
  addMulOps x0 x1 ++ xorRorOps x3 x0 32 ++ addMulOps x2 x3 ++ xorRorOps x1 x2 24 ++
  addMulOps x0 x1 ++ xorRorOps x3 x0 16 ++ addMulOps x2 x3 ++ xorRorOps x1 x2 63

theorem gb_eq : gb = gbOps.map .zop := rfl

/-- GB on each quadword of `zmm0`–`zmm3`. -/
theorem gb_qz (s : State) {k : Nat} (hk : k < 8) :
    (qz (zrun gbOps s) x0 k, qz (zrun gbOps s) x1 k, qz (zrun gbOps s) x2 k,
      qz (zrun gbOps s) x3 k) = mix (qz s x0 k) (qz s x1 k) (qz s x2 k) (qz s x3 k) := by
  simp only [gbOps, zrun_append]
  simp (disch := decide) only [addMul_qz (a := x0) (b := x1) (by decide) (by decide) _ _ hk,
    addMul_qz (a := x2) (b := x3) (by decide) (by decide) _ _ hk, xorRor_qz _ _ _ _ _ hk,
    ↓reduceIte, reduceCtorEq]
  rfl

/-! ## P on each half -/

def diagOps : List ZOp := [.vpermq x1 x1 0x39, .vpermq x2 x2 0x4e, .vpermq x3 x3 0x93]
def undiagOps : List ZOp := [.vpermq x1 x1 0x93, .vpermq x2 x2 0x4e, .vpermq x3 x3 0x39]
def roundOps : List ZOp := gbOps ++ diagOps ++ gbOps ++ undiagOps

theorem round_eq : round = roundOps.map .zop := rfl

/-- The sixteen words in half `h` of `zmm0`–`zmm3`: word `4i + q` is quadword
`4h + q` of `vreg i`. -/
def words (s : State) (h : Nat) : Vector Word 16 :=
  Vector.ofFn fun j => qz s (vreg (j.val / 4)) (4 * h + j.val % 4)

theorem words_get (s : State) (h j : Nat) (hj : j < 16) :
    (words s h)[j] = qz s (vreg (j / 4)) (4 * h + j % 4) := by
  simp only [words, Vector.getElem_ofFn]

theorem gb_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun gbOps s) h = mixColumns (words s h) := by
  apply Vector.ext
  intro j hj
  have g := gb_qz s (k := 4 * h + j % 4) (by omega)
  rw [words_get _ _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, words_get _ _ _ (by omega),
    words_get _ _ _ (by omega), words_get _ _ _ (by omega), words_get _ _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem diag_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun diagOps s) h = rotRows 1 (words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega]
  have e4 : (4 * h + j % 4) / 4 = h := by omega
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega
  simp only [diagOps, zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun undiagOps s) h = rotRows 3 (words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega]
  have e4 : (4 * h + j % 4) / 4 = h := by omega
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega
  simp only [undiagOps, zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega

/-- P on the sixteen words of each half of `zmm0`–`zmm3`. -/
theorem round_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun roundOps s) h = permute (words s h) := by
  simp only [roundOps, zrun_append]
  rw [Proof.Argon2.permute_lanes, undiag_words _ hh, gb_words _ hh, diag_words _ hh, gb_words _ hh]

end VG.Proof.Argon2.X86_64.Avx512

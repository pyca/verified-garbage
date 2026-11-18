module

public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows
public import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Ends
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Argon2.X86_64.Finish
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym
public import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Argon2.X86_64.Avx512.Cols`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.Avx512.Rows`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.Avx512.Mem`, which this module and modules that import it used -/

section

/-!
# Argon2 on x86-64 with AVX-512: 64-byte loads and stores

Quadword `k` of a register after a 64-byte load (`qz_load`), of a register
as a stored value (`zmm_qz`), and a word of memory after a 64-byte store
(`read_write512`); the block P permutes as scratch holds it, by pairs of
columns (`cv`, with the word of each quadword of each 64-byte chunk:
`cvIdx`).
-/

@[expose] public section

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
    decide_eq_true (show 64 * i + j < 128 by omega_using [hi, hj])]
  congr 1; omega_using []

theorem pick4_extract (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128) l = v.extractLsb' (128 * l) 128 := by
  have := pick4_lanes (fun l => v.extractLsb' (128 * l) 128) hl
  simpa only [Nat.reduceMul] using this

theorem qz_setZ_load (s : State) (d r : XReg) (v : BitVec 512) {k : Nat} (hk : k < 8) :
    qz (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)) r k = if r = d then v.extractLsb' (64 * k) 64 else qz s r k := by
  simp only [qz, State.zlane_setZ _ _ _ _ _ _ _ (show k / 2 < 4 by omega_using [hk])]
  split
  · rw [pick4_extract _ (show k / 2 < 4 by omega_using [hk]), qword_extract512 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2) + k % 2 = k by omega_using []]
  · rfl

theorem qz_load (s : State) (d r : XReg) (m : Mem) (a : Addr) {k : Nat} (hk : k < 8) :
    qz (s.setZ d ((m.readW a 512).extractLsb' 0 128) ((m.readW a 512).extractLsb' 128 128)
      ((m.readW a 512).extractLsb' 256 128) ((m.readW a 512).extractLsb' 384 128)) r k =
      if r = d then m.readW (a + BitVec.ofNat 64 (8 * k)) 64 else qz s r k := by
  rw [qz_setZ_load _ _ _ _ hk, show 64 * k = 8 * (8 * k) by omega_using [],
    readW_extract _ _ (k := 8 * k) (n := 8) (by omega_using [hk])]

/-- Quadword `k` of a register, as a stored value. -/
theorem extract64_split (x : BitVec 512) (a : Nat) :
    x.extractLsb' a 64 = x.extractLsb' (a + 32) 32 ++ x.extractLsb' a 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rename_i h
    rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_true (show j - 32 < 32 by omega_using [hj]), Bool.true_and]
    congr 1; omega_arith

theorem zmm_qz (s : State) (r : XReg) {k : Nat} (hk : k < 8) :
    (s.zmm r).extractLsb' (64 * k) 64 = qz s r k := by
  have e0 : (s.zmm r).extractLsb' (64 * k) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2)) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2)) (by omega_using [hk]) (by omega_using [])
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2))) = 64 * k by omega_using []] at this
    exact this
  have e1 : (s.zmm r).extractLsb' (64 * k + 32) 32 = dword (s.zlane r (k / 2)) (2 * (k % 2) + 1) := by
    have := State.zmm_extract s r (l := k / 2) (q := 2 * (k % 2) + 1) (by omega_using [hk]) (by omega_using [])
    rw [show 8 * (16 * (k / 2) + 4 * (2 * (k % 2) + 1)) = 64 * k + 32 by omega_using []] at this
    exact this
  rw [qz, Proof.Poly1305.X86_64.Avx2.qword_eq, extract64_split, e0, e1]

/-! ## Memory -/

/-- A word at `p + d` after 64 bytes are written at `p + e`. -/
theorem read_write512 (m : Mem) (p : Addr) {d e : Nat} (hd : d + 8 ≤ 4096) (he : e + 64 ≤ 4096)
    (h8 : d % 8 = 0) (he8 : e % 8 = 0) (v : BitVec 512) :
    (m.writeW (off p e) v).readW (off p d) 64 =
      if e ≤ d ∧ d < e + 64 then v.extractLsb' (64 * ((d - e) / 8)) 64 else m.readW (off p d) 64 := by
  split
  · rename_i h
    rw [show off p d = off p e + BitVec.ofNat 64 (8 * ((d - e) / 8)) from
      (Offset.add_add_eq p (by omega_using [h8, he8, h])).symm]
    refine (readW_writeW_inside _ _ v (k := 8 * ((d - e) / 8)) (n := 8) (by omega_using [h]) (by decide)).trans ?_
    rw [show 8 * (8 * ((d - e) / 8)) = 64 * ((d - e) / 8) by omega_using []]
  · exact readW_writeW_off m p v (n := 8) (by omega_using [hd]) (by omega_using [he]) (by omega_arith)

/-- The offset in `[1024, 2048)` of scratch of word `i` of the block P
permutes: in register `i / 32` of columns `2c`, `2c + 1` (`c = i % 16 / 4`),
quadword `cvQ i`. -/
def cvQ (i : Nat) : Nat := 4 * (i % 16 / 2 % 2) + 2 * (i / 16 % 2) + i % 2

def cvOff (i : Nat) : Nat := 256 * (i % 16 / 4) + 64 * (i / 32) + 8 * cvQ i

/-- The block P permutes, as scratch holds it. -/
def cv (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => m.readW (off p (1024 + cvOff i.val)) 64

theorem cv_get (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) :
    (cv m p)[i] = m.readW (off p (1024 + cvOff i)) 64 := by
  simp only [cv, Vector.getElem_ofFn]

/-- Where the words are, as bounded facts. -/
theorem cvOff_lt : ∀ i < 128, cvOff i + 8 ≤ 1024 ∧ cvOff i % 8 = 0 := by decide

theorem cvOff_in : ∀ i < 128, ∀ c < 4, ∀ k < 4,
    (1024 + 256 * c + 64 * k ≤ 1024 + cvOff i ∧ 1024 + cvOff i < 1024 + 256 * c + 64 * k + 64 ↔
      i % 16 / 4 = c ∧ i / 32 = k) := by decide

theorem cvOff_q : ∀ i < 128, (1024 + cvOff i - (1024 + 256 * (i % 16 / 4) + 64 * (i / 32))) / 8 = cvQ i := by
  decide

theorem cvQ_lt : ∀ i < 128, cvQ i < 8 := by decide

/-- The word of quadword `e` of register `k` of columns `2c`, `2c + 1`: word
`4k + e % 4` of column `2c + e / 4`. -/
def cvIdx (c k e : Nat) : Nat := 16 * (2 * k + e % 4 / 2) + 4 * c + 2 * (e / 4) + e % 2

theorem cvOff_cvIdx : ∀ c < 4, ∀ k < 4, ∀ e < 8, cvOff (cvIdx c k e) = 256 * c + 64 * k + 8 * e := by
  decide

theorem cvIdx_lt {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) : cvIdx c k e < 128 := by
  simp only [cvIdx]; omega_using [hc, hk, he]

/-- A word of `cv` after a 64-byte write to the chunk at `colOff c k`. -/
theorem cv_write512 (m : Mem) (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) (v : BitVec 512)
    (i : Nat) (hi : i < 128) :
    (cv (m.writeW (off p (colOff c k)) v) p)[i] =
      if i % 16 / 4 = c ∧ i / 32 = k then v.extractLsb' (64 * cvQ i) 64 else (cv m p)[i] := by
  have ho := cvOff_lt i hi
  rw [cv_get _ _ _ hi, cv_get _ _ _ hi, colOff, read_write512 _ _ (by omega_using [ho]) (by omega_using [hc, hk])
    (by omega_using [ho]) (by omega_using [])]
  by_cases h : i % 16 / 4 = c ∧ i / 32 = k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((cvOff_in i hi c hc k hk).mpr h)),
      ite_eq_left_of_eq_true _ _ (eq_true h), ← h.1, ← h.2, cvOff_q i hi]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (cvOff_in i hi c hc k hk).mp h)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The register of columns `2c`, `2c + 1` at `colOff c k`, as `cv` holds it. -/
theorem cv_chunk (m : Mem) (p : Addr) {c k e : Nat} (hc : c < 4) (hk : k < 4) (he : e < 8) :
    m.readW (off p (colOff c k) + BitVec.ofNat 64 (8 * e)) 64 =
      (cv m p)[cvIdx c k e]'(cvIdx_lt hc hk he) := by
  rw [cv_get _ _ _ (cvIdx_lt hc hk he), cvOff_cvIdx c hc k hk e he, Offset.add_add, colOff,
    show 1024 + 256 * c + 64 * k + 8 * e = 1024 + (256 * c + 64 * k + 8 * e) by omega_using []]

end VG.Proof.Argon2.X86_64.Avx512

end

end

/-! ### `Argon2.X86_64.Avx512.Gb`, which this module and modules that import it used -/

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

@[expose] public section

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
  rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl <;> simp only [rorQwords, qword_app0, qword_app1]

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
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (show 64 * j + m < 128 by omega_arith)), qword, BitVec.getLsbD_extractLsb']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 64 * j + m < 128 by omega_arith)), qword, BitVec.getLsbD_extractLsb',
      show 64 * j + m - 128 = 64 * (j - 2) + m by omega_arith]

/-- Quadword `i` of a 128-bit piece of a 256-bit value. -/
theorem qword_extract256 (Y : BitVec 256) (l : Nat) {i : Nat} (hi : i < 2) :
    qword (Y.extractLsb' (128 * l) 128) i = qword256 Y (2 * l + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega_arith)]
  congr 1; omega_arith

theorem zlane_vpermq (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpermq d a o).exec s).zlane r i =
      if r = d then (permQwords (s.zlane a (2 * (i / 2) + 1) ++ s.zlane a (2 * (i / 2))) o).extractLsb'
        (128 * (i % 2)) 128 else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi]
  split
  · rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- `vpermq` permutes the quadwords of each half. -/
theorem qz_vpermq (s : State) (d a r : XReg) (o : BitVec 8) {k : Nat} (hk : k < 8) :
    qz ((ZOp.vpermq d a o).exec s) r k =
      if r = d then qz s a (4 * (k / 4) + sel4 o.toNat (k % 4)) else qz s r k := by
  simp only [qz, zlane_vpermq _ _ _ _ _ (div2_lt hk)]
  split
  · have hs := sel4_lt o.toNat (k % 4)
    rw [qword_extract256 _ _ (Nat.mod_lt _ (by decide)),
      show 2 * (k / 2 % 2) + k % 2 = k % 4 by omega_arith, qword256_perm _ _ (Nat.mod_lt _ (by decide)),
      qword256_append _ _ hs]
    split <;> congr 2 <;> omega_arith
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
  have g := gb_qz s (k := 4 * h + j % 4) (by omega_arith)
  rw [words_get _ _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, words_get _ _ _ (by omega_arith),
    words_get _ _ _ (by omega_arith), words_get _ _ _ (by omega_arith), words_get _ _ _ (by omega_arith),
    show j % 4 / 4 = 0 by omega_arith, show (4 + j % 4) / 4 = 1 by omega_arith, show (8 + j % 4) / 4 = 2 by omega_arith,
    show (12 + j % 4) / 4 = 3 by omega_arith, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega_arith,
    show (8 + j % 4) % 4 = j % 4 by omega_arith, show (12 + j % 4) % 4 = j % 4 by omega_arith]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem diag_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun diagOps s) h = rotRows 1 (words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ _ (by omega_arith),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega_arith,
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega_arith]
  have e4 : (4 * h + j % 4) / 4 = h := by omega_arith
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega_arith
  simp only [diagOps, zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega_arith) only [vreg, qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun undiagOps s) h = rotRows 3 (words s h) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ _ (by omega_arith),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega_arith,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega_arith]
  have e4 : (4 * h + j % 4) / 4 = h := by omega_arith
  have m4 : (4 * h + j % 4) % 4 = j % 4 := by omega_arith
  simp only [undiagOps, zrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega_arith) only [vreg, qz_vpermq, e4, m4, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega_arith

/-- P on the sixteen words of each half of `zmm0`–`zmm3`. -/
theorem round_words (s : State) {h : Nat} (hh : h < 2) :
    words (zrun roundOps s) h = permute (words s h) := by
  simp only [roundOps, zrun_append]
  rw [Proof.Argon2.permute_lanes, undiag_words _ hh, gb_words _ hh, diag_words _ hh, gb_words _ hh]

end VG.Proof.Argon2.X86_64.Avx512

end

end

/-!
# Argon2 on x86-64 with AVX-512: P on two rows

Rows `2p` and `2p + 1` of R (`[0, 1024)` of scratch, `blockAt`) are loaded
into the halves of `zmm0`–`zmm3` (`loadRows_ok`), permuted (`round_words`)
and stored to their places in the block P permutes, as scratch holds it by
pairs of columns (`cv`, `storeRows_ok`): `rows_ok`.
-/

@[expose] public section

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

theorem zrun_vkeep (os : List ZOp) (s : State) : VKeep s (zrun os s) :=
  ⟨zrun_gpr os s, zrun_rd os s, zrun_wr os s, zrun_mxcsr os s⟩

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (zrun roundOps s)) :
    WP isa (.block round) s Q := by
  rw [round_eq]
  exact WP.of_runBlock ⟨_, runBlock_zops _ _, h⟩

/-! ## Loading two rows -/

theorem loadRows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadRows pp)) s fun t =>
      (∀ h (hh : h < 2), words t h = gather (rowIndex ⟨2 * pp + h, by omega_arith⟩) (blockAt s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := hs.read (d := 256 * pp) (n := 64) (by omega_arith)
  have r1 := hs.read (d := 256 * pp + 64) (n := 64) (by omega_arith)
  have r2 := hs.read (d := 256 * pp + 128) (n := 64) (by omega_arith)
  have r3 := hs.read (d := 256 * pp + 192) (n := 64) (by omega_arith)
  apply WP.of_runBlock
  simp only [loadRows, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r2, r3, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, by simp only [ZOp.exec_mem, State.setZ_mem], ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [words_get _ _ _ hj, show (gather (rowIndex ⟨2 * pp + h, by omega_arith⟩) (blockAt s.mem p))[j] =
        (blockAt s.mem p)[rowIndex ⟨2 * pp + h, by omega_arith⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      blockAt_get]
    simp only [rowIndex]
    have l0 : (4 * 0 + j % 4) / 2 < 2 := by omega_arith
    have l1 : ¬ (4 * 1 + j % 4) / 2 < 2 := by omega_arith
    have n0 : ∀ c, 2 * ((4 * c + j % 4) / 2 % 2) + (4 * c + j % 4) % 2 = j % 4 := by
      intro c; omega_using [hk]
    have n1 : ∀ c, 2 * (2 + (4 * c + j % 4) / 2 % 2) + (4 * c + j % 4) % 2 = 4 + j % 4 := by
      intro c; omega_using [hk]
    rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
      simp (disch := omega_using [hk]) only [vreg, qz_vshufi32x4, qz_load, sel4_44, sel4_ee, ↓reduceIte,
        reduceCtorEq, l0, l1] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;>
      simp only [n0, n1] <;> omega_using [e, Nat.div_add_mod j 4]
  · exact (((((((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)).trans (zop_vkeep _ _)).trans
      (zop_vkeep _ _)).trans (zop_vkeep _ _)).trans (zop_vkeep _ _)

/-! ## Storing two rows -/

/-- The working half of scratch contains the chunk at `colOff c k`. -/
theorem colOff_contains (p : Addr) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (colOff c k)) 64 :=
  Offset.contains p (by unfold colOff; omega_arith) (by unfold colOff; omega_arith) (by omega_arith)

theorem colOff_write {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions s.wr (off p (colOff c k)) 64 :=
  hs.write (by unfold colOff; omega_arith)

/-- The quadword `vshufi32x4` with `0xd8` moves to quadword `cvQ i`. -/
theorem rowQ : ∀ i < 128, 2 * sel4 (0xd8 : BitVec 8).toNat (cvQ i / 2) + cvQ i % 2 =
    4 * (i / 16 % 2) + i % 4 := by decide

def storeRow (pp k : Nat) : List Instr :=
  [.zop (.vshufi32x4 .xmm4 (vreg k) (vreg k) 0xd8), .vmovdqu32Store (at_ .rcx (colOff k pp)) .xmm4]

theorem storeRows_eq (pp : Nat) : storeRows pp = (List.range 4).flatMap (storeRow pp) := rfl

/-- What storing register `k` of rows `2p`, `2p + 1` leaves. -/
structure RowStored (p : Addr) (pp n : Nat) (s t : State) : Prop where
  cv : ∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 < n ∧ i / 32 = pp then
    qz s (vreg (i % 16 / 4)) (4 * (i / 16 % 2) + i % 4) else (cv s.mem p)[i]
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VKeep s t
  regs : ∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e

theorem storeRow_ok {pp k : Nat} (hp : pp < 4) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeRow pp k)) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 = k ∧ i / 32 = pp then
        qz s (vreg k) (4 * (i / 16 % 2) + i % 4) else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧
      (∀ r, r ≠ .xmm4 → ∀ e < 8, qz t r e = qz s r e) := by
  apply WP.of_runBlock
  simp only [storeRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    ZOp.exec_wr, ZOp.exec_gpr, ZOp.exec_mem, hs.reg, colOff_write hs hk hp, ite_true,
    Option.some.injEq, exists_eq_left', State.setMem_mem]
  refine ⟨fun i hi => ?_, ?_, (zop_vkeep _ _).trans (setMem_vkeep _ _), fun r hr e he => ?_⟩
  · rw [cv_write512 _ _ hk hp _ _ hi]
    split
    · rw [zmm_qz _ _ (cvQ_lt i hi), qz_vshufi32x4 _ _ _ _ _ _ (cvQ_lt i hi),
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_self]
      exact congrArg _ (rowQ i hi)
    · rfl
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (colOff_contains p hk hp)
  · rw [qz_setMem, qz_vshufi32x4 _ _ _ _ _ _ he, ite_eq_right_of_eq_false _ _ (eq_false hr)]

theorem storeRows_prefix {pp : Nat} (hp : pp < 4) (n : Nat) (hn : n ≤ 4) {s : State} {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block ((List.range n).flatMap (storeRow pp))) s (RowStored p pp n s) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by simp, Frame.refl _ _, VKeep.refl s, fun _ _ _ _ => rfl⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨hc, hf, hk, hr⟩
    refine (storeRow_ok hp (k := n) (by omega_arith) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk', hr'⟩
    refine ⟨fun i hi => ?_, hf.trans hf', hk.trans hk', fun r h e he => (hr' r h e he).trans (hr r h e he)⟩
    rw [hc' i hi, hr _ (vreg_ne4 n) _ (by omega_arith), hc i hi]
    by_cases h1 : i % 16 / 4 = n ∧ i / 32 = pp
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), h1.1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : i % 16 / 4 < n ∧ i / 32 = pp
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

/-! ## Two rows -/

/-- P on rows `2p` and `2p + 1` of R, stored to `cv`. -/
theorem rows_ok {pp : Nat} (hp : pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (rows pp) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i / 32 = pp then
        (permute (gather (rowIndex ⟨i / 16, by omega_arith⟩) (blockAt s.mem p)))[i % 16]'(by omega_arith)
        else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold rows
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadRows_ok hp hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine round_then ?_
  have hs2 : Scratch (zrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (zrun_vkeep _ _)
  rw [storeRows_eq]
  refine (storeRows_prefix hp 4 (by decide) hs2).mono ?_
  rintro t ⟨hc, hf, hk, -⟩
  rw [zrun_mem, hmem1] at hc hf
  refine ⟨fun i hi => ?_, hf, hk1.trans ((zrun_vkeep _ _).trans hk)⟩
  rw [hc i hi]
  by_cases h : i / 32 = pp
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i / 16 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[i % 16]'(by omega_arith))
      ((round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [words_get _ _ _ (show i % 16 < 16 by omega_arith), show i % 16 % 4 = i % 4 by omega_arith] at e
    rw [e]
    have er : (⟨2 * pp + i / 16 % 2, by omega_arith⟩ : Fin 8) = ⟨i / 16, by omega_arith⟩ := Fin.ext (by simp only; omega_arith)
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512

end

end

/-! ### `Argon2.PermuteMany`, which this module and modules that import it used -/

section

/-!
# P on several rows or columns

Facts about `permuteAt` on a family of disjoint index sets (the rows, or
the columns): P on one set leaves the others alone, so the rows (or
columns) can be permuted in any grouping (`foldl_at`, `foldl_pairs`).
-/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem permuteAt_eq_scatter (index : Fin 16 → Fin 128) (b : Block) :
    permuteAt index b = scatter index (List.finRange 16) b (permute (gather index b)) := rfl

theorem permuteAt_at (index : Fin 16 → Fin 128) (hi : Function.Injective index) (b : Block)
    (j : Fin 16) : (permuteAt index b)[index j] = (permute (gather index b))[j] := by
  rw [permuteAt_eq_scatter]
  exact scatter_at index hi _ b _ j (List.mem_finRange j)

theorem permuteAt_outside (index : Fin 16 → Fin 128) (b : Block) (k : Fin 128)
    (hk : ∀ j, index j ≠ k) : (permuteAt index b)[k] = b[k] := by
  rw [permuteAt_eq_scatter]
  exact scatter_outside index _ b _ k (fun j _ => hk j)

/-- A family of injective index sets, pairwise disjoint. -/
structure Disjoint (index : Fin 8 → Fin 16 → Fin 128) : Prop where
  inj : ∀ a, Function.Injective (index a)
  disj : ∀ a b j j', a ≠ b → index a j ≠ index b j'

theorem rows_disjoint : Disjoint rowIndex :=
  ⟨rowIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [rowIndex] at this
    omega_using [this]))⟩

theorem cols_disjoint : Disjoint colIndex :=
  ⟨colIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [colIndex] at this
    omega_using [this]))⟩

/-- P on set `a` leaves set `r ≠ a` alone. -/
theorem gather_permuteAt {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {a r : Fin 8}
    (h : a ≠ r) (b : Block) : gather (index r) (permuteAt (index a) b) = gather (index r) b := by
  apply Vector.ext; intro j hj
  rw [show (gather (index r) (permuteAt (index a) b))[j] =
      (gather (index r) (permuteAt (index a) b))[(⟨j, hj⟩ : Fin 16)] from rfl,
    show (gather (index r) b)[j] = (gather (index r) b)[(⟨j, hj⟩ : Fin 16)] from rfl,
    gather_get, gather_get, permuteAt_outside _ _ _ (fun j' => hd.disj a r j' _ h)]

theorem foldl_outside {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hr : r ∉ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = b[index r j] := by
  induction L generalizing b with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, ih (fun h => hr (List.mem_cons_of_mem _ h)),
      permuteAt_outside _ _ _ (fun j' => hd.disj i r j' j (fun e => hr (e ▸ List.mem_cons_self)))]

/-- Set `r`, after P on each set of a list without repeats that contains it. -/
theorem foldl_at {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hn : L.Nodup) (hr : r ∈ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = (permute (gather (index r) b))[j] := by
  induction L generalizing b with
  | nil => simp only [List.not_mem_nil] at hr
  | cons i L ih =>
    rw [List.foldl_cons]
    have hn' := List.nodup_cons.mp hn
    by_cases e : i = r
    · subst e
      rw [foldl_outside hd L hn'.1, permuteAt_at _ (hd.inj i)]
    · rw [ih hn'.2 ((List.mem_cons.mp hr).resolve_left fun h => e h.symm), gather_permuteAt hd e]

/-- The eight sets, in order, as four pairs. -/
theorem foldl_pairs (index : Fin 8 → Fin 16 → Fin 128) (b : Block) :
    (List.finRange 8).foldl (fun b i => permuteAt (index i) b) b =
      (List.range 4).foldl (fun b c => permuteAt (index ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (index ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b)) b := by
  rw [show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide,
    show List.range 4 = [0, 1, 2, 3] by decide]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- Word `i` of a block after P on all rows. -/
theorem rows_get (b : Block) (i : Nat) (hi : i < 128) :
    ((List.finRange 8).foldl (fun b r => permuteAt (rowIndex r) b) b)[i] =
      (permute (gather (rowIndex ⟨i / 16, by omega_using [hi]⟩) b))[i % 16]'(by omega_using []) := by
  have := foldl_at rows_disjoint (List.finRange 8) (List.nodup_finRange 8)
    (List.mem_finRange ⟨i / 16, by omega_using [hi]⟩) b ⟨i % 16, by omega_using []⟩
  simpa only [rowIndex, Fin.getElem_fin, show 16 * (i / 16) + i % 16 = i by omega_using []] using this

/-- Word `i` of a block after P on columns `2c` and `2c + 1`. -/
theorem colPair_get {c : Nat} (hc : c < 4) (b : Block) (i : Nat) (hi : i < 128) :
    (permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b))[i] =
      if i % 16 / 4 = c then
        (permute (gather (colIndex ⟨i % 16 / 2, by omega_using []⟩) b))[2 * (i / 16) + i % 2]'(by omega_using [hi])
      else b[i] := by
  have hv : 16 * ((2 * (i / 16) + i % 2) / 2) + 2 * (i % 16 / 2) + (2 * (i / 16) + i % 2) % 2 = i := by
    omega_using []
  by_cases h1 : i % 16 / 2 = 2 * c + 1
  · have ec : (⟨i % 16 / 2, by omega_using []⟩ : Fin 8) = ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩ :=
      Fin.ext (by simp only; omega_using [h1])
    have := permuteAt_at _ (colIndex_injective ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨2 * (i / 16) + i % 2, by omega_using [hi]⟩
    rw [gather_permuteAt cols_disjoint (fun h => by have := congrArg Fin.val h; simp only at this; omega_using [this]),
      ← ec] at this
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [h1]))]
    simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
  · by_cases h0 : i % 16 / 2 = 2 * c
    · have ec : (⟨i % 16 / 2, by omega_using []⟩ : Fin 8) = ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩ :=
        Fin.ext (by simp only; omega_using [h0])
      have := permuteAt_at _ (colIndex_injective ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b
        ⟨2 * (i / 16) + i % 2, by omega_using [hi]⟩
      rw [← permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩) _ _
        (fun j' => cols_disjoint.disj _ _ j' _
          (fun h => by have := congrArg Fin.val h; simp only at this; omega_using [this])), ← ec] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_using [h0]))]
      simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h1, h0]))]
      have := permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨i, hi⟩
        (fun j' h => by have := congrArg Fin.val h; simp only [colIndex] at this; omega_using [hc, h1, this])
      rw [permuteAt_outside (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b ⟨i, hi⟩ (fun j' h => by
          have := congrArg Fin.val h; simp only [colIndex] at this; omega_using [hc, h0, this])] at this
      simpa only [Fin.getElem_fin] using this

end VG.Proof.Argon2

end

end

/-!
# Argon2 on x86-64 with AVX-512: P on two columns

The registers of columns `2c` and `2c + 1` are four consecutive 64-byte
chunks of `cv` (`loadCols_ok`); P on both halves of them (`round_words`),
stored back (`storeCols_ok`), is P on both columns (`cols_ok`).
-/

@[expose] public section

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
    256 * c + 64 * (j / 4) + 8 * (4 * h + j % 4) = cvOff (16 * (j / 2) + 2 * (2 * c + h) + j % 2) := by
  decide

@[simp] theorem State.setMem_zmm (s : State) (m : Mem) (r : XReg) : (s.setMem m).zmm r = s.zmm r := by
  cases s; rfl

theorem loadCols_eq (c : Nat) : loadCols c =
    [.vmovdqu32Load .xmm0 (at_ .rcx (colOff c 0)), .vmovdqu32Load .xmm1 (at_ .rcx (colOff c 1)),
      .vmovdqu32Load .xmm2 (at_ .rcx (colOff c 2)), .vmovdqu32Load .xmm3 (at_ .rcx (colOff c 3))] := rfl

theorem storeCols_eq (c : Nat) : storeCols c =
    [.vmovdqu32Store (at_ .rcx (colOff c 0)) .xmm0, .vmovdqu32Store (at_ .rcx (colOff c 1)) .xmm1,
      .vmovdqu32Store (at_ .rcx (colOff c 2)) .xmm2, .vmovdqu32Store (at_ .rcx (colOff c 3)) .xmm3] := rfl

theorem colOff_read {s : State} {p : Addr} (hs : Scratch s p) {c k : Nat} (hc : c < 4) (hk : k < 4) :
    InRegions (s.rd ++ s.wr) (off p (colOff c k)) 64 :=
  hs.read (by unfold colOff; omega_using [hc, hk])

theorem loadCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (loadCols c)) s fun t =>
      (∀ h (hh : h < 2), words t h = gather (colIndex ⟨2 * c + h, by omega_using [hc, hh]⟩) (cv s.mem p)) ∧
      t.mem = s.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [loadCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg,
    colOff_read hs hc (show 0 < 4 by decide), colOff_read hs hc (show 1 < 4 by decide),
    colOff_read hs hc (show 2 < 4 by decide), colOff_read hs hc (show 3 < 4 by decide), ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun h hh => ?_, trivial, ?_⟩
  · apply Vector.ext
    intro j hj
    rw [words_get _ _ _ hj, show (gather (colIndex ⟨2 * c + h, by omega_using [hc, hh]⟩) (cv s.mem p))[j] =
        (cv s.mem p)[colIndex ⟨2 * c + h, by omega_using [hc, hh]⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩,
      Fin.getElem_fin, cv_get _ _ _ (colIndex _ _).isLt]
    have hq := colQ c hc h hh j hj
    simp only [colIndex]
    rcases cases_div4 hj with e | e | e | e <;> rw [e] at hq ⊢ <;>
      simp (disch := omega_arith) only [vreg, qz_load, ↓reduceIte, reduceCtorEq] <;>
      refine congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ ?_) <;> unfold colOff <;> omega_using [hq]
  · exact (((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)

theorem storeCols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCols c)) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i % 16 / 4 = c then
        qz s (vreg (i / 32)) (cvQ i) else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  apply WP.of_runBlock
  simp only [storeCols_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, hs.reg,
    colOff_write hs hc (show 0 < 4 by decide), colOff_write hs hc (show 1 < 4 by decide),
    colOff_write hs hc (show 2 < 4 by decide), colOff_write hs hc (show 3 < 4 by decide), ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hq := cvQ_lt i hi
    rw [cv_write512 _ _ hc (show 3 < 4 by decide) _ _ hi, cv_write512 _ _ hc (show 2 < 4 by decide) _ _ hi,
      cv_write512 _ _ hc (show 1 < 4 by decide) _ _ hi, cv_write512 _ _ hc (show 0 < 4 by decide) _ _ hi]
    simp only [State.setMem_zmm, zmm_qz _ _ hq]
    by_cases h : i % 16 / 4 = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      have : i / 32 = 0 ∨ i / 32 = 1 ∨ i / 32 = 2 ∨ i / 32 = 3 := by omega_using [hi]
      rcases this with e | e | e | e <;> simp only [e, h, vreg, and_self, ite_true, ite_false,
        show (0 : Nat) ≠ 1 by decide, show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 3 by decide,
        show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 3 by decide,
        and_false]
    · simp only [h, false_and, ite_false]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (colOff_contains p hc (by decide))
      | exact Frame.refl _ _)
  · exact (((setMem_vkeep _ _).trans (setMem_vkeep _ _)).trans (setMem_vkeep _ _)).trans
      (setMem_vkeep _ _)

/-- P on columns `2c` and `2c + 1` of `cv`. -/
theorem cols_ok {c : Nat} (hc : c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (cols c) s fun t =>
      cv t.mem p = permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) (cv s.mem p)) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  unfold cols
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadCols_ok hc hs).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1⟩
  refine round_then ?_
  have hs2 : Scratch (zrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (zrun_vkeep _ _)
  refine (storeCols_ok hc hs2).mono ?_
  rintro t ⟨hc', hf, hk⟩
  rw [zrun_mem, hmem1] at hc' hf
  refine ⟨?_, hf, hk1.trans ((zrun_vkeep _ _).trans hk)⟩
  apply Vector.ext
  intro i hi
  rw [hc' i hi, Proof.Argon2.colPair_get hc _ i hi]
  by_cases h : i % 16 / 4 = c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
    have hh : i % 16 / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
    have e := congrArg (fun v : Vector Word 16 => v[2 * (i / 16) + i % 2]'(by omega_using [hi]))
      ((round_words t1 hh).trans (congrArg permute (hw1 _ hh)))
    simp only [words_get _ _ _ (show 2 * (i / 16) + i % 2 < 16 by omega_using [hi]),
      show (2 * (i / 16) + i % 2) / 4 = i / 32 by omega_using [],
      show 4 * (i % 16 / 2 % 2) + (2 * (i / 16) + i % 2) % 4 = cvQ i by simp only [cvQ]; omega_using []] at e
    rw [e]
    have er : (⟨2 * c + i % 16 / 2 % 2, by omega_using [hc]⟩ : Fin 8) = ⟨i % 16 / 2, by omega_using []⟩ :=
      Fin.ext (by simp only; omega_using [h])
    rw [er]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]

end VG.Proof.Argon2.X86_64.Avx512

end

end

/-!
# Argon2 on x86-64 with AVX-512: the first and last XOR

`initChunk k` writes 64 bytes of X XOR Y to R, and `finishChunk n k` writes
words `8n…8n+7` of rows `2k` and `2k + 1` of the output: `cv` XOR R. Each
is proven for any prefix of its chunks (`init_prefix`, `finish_prefix`).
-/

@[expose] public section

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
    (cv m p)[a]'ha = (cv m p)[b]'hb := by
  subst h; rfl

/-! ## R -/

theorem initChunk_ok {k : Nat} (hk : k < 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block (initChunk k)) s fun t => ∃ v : BitVec 512,
      (∀ q < 8, v.extractLsb' (64 * q) 64 =
        s.mem.readW (off x (64 * k + 8 * q)) 64 ^^^ s.mem.readW (off y (64 * k + 8 * q)) 64) ∧
      t.mem = s.mem.writeW (off p (64 * k)) v ∧ VKeep s t := by
  have lx : InRegions (s.rd ++ s.wr) (off x (64 * k)) 64 :=
    ⟨_, hin.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
  have ly : InRegions (s.rd ++ s.wr) (off y (64 * k)) 64 :=
    ⟨_, hin.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
  have w := hs.write (d := 64 * k) (n := 64) (by omega_arith)
  apply WP.of_runBlock
  simp only [initChunk, z, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512,
    State.store512_eq, ea_at, State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem,
    ZOp.exec_gpr, ZOp.exec_mem, ZOp.exec_wr, hs.reg, hin.xreg, hin.yreg, lx, ly, w, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ((((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans
    (zop_vkeep _ _)).trans (setMem_vkeep _ _))⟩
  have h2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
  simp (disch := omega_arith) only [zmm_qz _ _ hq, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor,
    qz_lane, qz_load, ↓reduceIte, reduceCtorEq, Offset.add_add]

/-- The chunks `k < n` of R hold `r`. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val / 8 < n → m.readW (off p (8 * i.val)) 64 = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat} (hn : n < 16)
    (h : Initialized m p r n) {v : BitVec 512} (hv : ∀ q < 8, ∀ hi : 8 * n + q < 128,
      v.extractLsb' (64 * q) 64 = r[8 * n + q]'hi) :
    Initialized (m.writeW (off p (64 * n)) v) p r (n + 1) := by
  intro i hi
  have hi' := i.isLt
  rw [read_write512 _ p (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)]
  by_cases e : i.val / 8 = n
  · have q := hv (i.val % 8) (Nat.mod_lt _ (by decide)) (by omega_arith)
    simp only [show 8 * n + i.val % 8 = i.val by omega_arith] at q
    rw [ifp (by omega_arith), show (8 * i.val - 64 * n) / 8 = i.val % 8 by omega_arith, q]
    rfl
  · rw [ifn (by omega_arith)]
    exact h i (by omega_arith)

/-- Initialize the first `n` chunks of R, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 16) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initChunk)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VKeep s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, VKeep.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (initChunk_ok (by omega_arith) (hs.of_vkeep hk) (hin.of_vkeep hk)).mono ?_
    rintro u ⟨v, hv, hmem, hk'⟩
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hmem]
      refine initialized_step (by omega_arith) ht fun q hq hi => ?_
      rw [hv q hq, show 64 * n + 8 * q = 8 * (8 * n + q) by omega_arith,
        input_unchanged hf hin.xsep ⟨8 * n + q, hi⟩, input_unchanged hf hin.ysep ⟨8 * n + q, hi⟩]
      simp only [xorBlock, Vector.getElem_zipWith, blockAt, Vector.getElem_ofFn]
      rfl
    · rw [hmem]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_arith) (by omega_arith))

/-- R, initialized. -/
theorem initialized_all {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 16) :
    blockAt m p = r := by
  apply Vector.ext; intro i hi
  have := h ⟨i, hi⟩ (by simp only; omega_arith)
  rw [← blockAt_get m p ⟨i, hi⟩] at this
  exact this

/-! ## The output -/

/-- The words of `cv` that `vshufi32x4` with `0x88` and `0xdd` join. -/
theorem finQ : ∀ n < 2, ∀ k < 4, ∀ q < 8,
    cvIdx (2 * n + q / 4) k (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) = 32 * k + 8 * n + q ∧
    cvIdx (2 * n + q / 4) k (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) =
      32 * k + 16 + 8 * n + q := by
  decide

def joinOps : List ZOp :=
  [.vshufi32x4 .xmm2 .xmm0 .xmm1 0x88, .vshufi32x4 .xmm3 .xmm0 .xmm1 0xdd,
    .zbin .vpxord .xmm2 .xmm2 .xmm4, .zbin .vpxord .xmm3 .xmm3 .xmm5]

theorem join_qz2 (s : State) {q : Nat} (hq : q < 8) :
    qz (zrun joinOps s) .xmm2 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0x88 : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm4 q := by
  simp only [joinOps, zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]

theorem join_qz3 (s : State) {q : Nat} (hq : q < 8) :
    qz (zrun joinOps s) .xmm3 q =
      (if q / 2 < 2 then qz s .xmm0 else qz s .xmm1) (2 * sel4 (0xdd : BitVec 8).toNat (q / 2) + q % 2) ^^^
        qz s .xmm5 q := by
  have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
  simp only [joinOps, zrun, qz_zbin _ _ _ _ _ _ hq, ZBinOp.sse, qword_pxor, qz_lane, reduceCtorEq,
    ↓reduceIte, qz_vshufi32x4 _ _ _ _ _ _ hq]
  split <;> simp (disch := omega_arith) only [qz_vshufi32x4, reduceCtorEq, ↓reduceIte]

def finLoads (n k : Nat) : List Instr :=
  [.vmovdqu32Load .xmm0 (at_ .rcx (colOff (2 * n) k)),
    .vmovdqu32Load .xmm1 (at_ .rcx (colOff (2 * n + 1) k)),
    .vmovdqu32Load .xmm4 (at_ .rcx (256 * k + 64 * n)),
    .vmovdqu32Load .xmm5 (at_ .rcx (256 * k + 128 + 64 * n))]

def finStores (n k : Nat) : List Instr :=
  [.vmovdqu32Store (at_ .rdx (256 * k + 64 * n)) .xmm2,
    .vmovdqu32Store (at_ .rdx (256 * k + 128 + 64 * n)) .xmm3]

theorem finishChunk_eq (n k : Nat) :
    finishChunk n k = finLoads n k ++ joinOps.map .zop ++ finStores n k := rfl

theorem finLoads_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (finLoads n k)) s fun t =>
      (∀ e (he : e < 8), qz t .xmm0 e = (cv s.mem p)[cvIdx (2 * n) k e]'(by simp only [cvIdx]; omega_arith)) ∧
      (∀ e (he : e < 8), qz t .xmm1 e = (cv s.mem p)[cvIdx (2 * n + 1) k e]'(by simp only [cvIdx]; omega_arith)) ∧
      (∀ q < 8, qz t .xmm4 q = s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q < 8, qz t .xmm5 q = s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = s.mem ∧ VKeep s t := by
  have r0 := colOff_read hs (c := 2 * n) (k := k) (by omega_arith) hk
  have r1 := colOff_read hs (c := 2 * n + 1) (k := k) (by omega_arith) hk
  have r4 := hs.read (d := 256 * k + 64 * n) (n := 64) (by omega_arith)
  have r5 := hs.read (d := 256 * k + 128 + 64 * n) (n := 64) (by omega_arith)
  apply WP.of_runBlock
  simp only [finLoads, runBlock_cons, runStep_some, runBlock_nil, exec, State.load512, ea_at,
    State.setZ_rd, State.setZ_wr, State.setZ_gpr, State.setZ_mem, hs.reg, r0, r1, r4, r5, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun e he => ?_, fun e he => ?_, fun q hq => ?_, fun q hq => ?_, trivial,
    (((setZ_vkeep _ _ _ _ _ _).trans (setZ_vkeep _ _ _ _ _ _)).trans (setZ_vkeep _ _ _ _ _ _)).trans
      (setZ_vkeep _ _ _ _ _ _)⟩
  · simp only [qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact cv_chunk _ _ (by omega_arith) hk he
  · simp only [qz_load _ _ _ _ _ he, reduceCtorEq, ↓reduceIte]
    exact cv_chunk _ _ (by omega_arith) hk he
  · simp only [qz_load _ _ _ _ _ hq, reduceCtorEq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega_arith))
  · simp only [qz_load _ _ _ _ _ hq, ↓reduceIte, Offset.add_add]
    exact congrArg (Mem.readW _ · 64) (congrArg (off p) (by omega_arith))

theorem finStores_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {out : Addr}
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finStores n k)) s fun t =>
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) (s.zmm .xmm2)).writeW
        (off out (256 * k + 128 + 64 * n)) (s.zmm .xmm3) ∧ VKeep s t := by
  have w1 : InRegions s.wr (off out (256 * k + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  have w2 : InRegions s.wr (off out (256 * k + 128 + 64 * n)) 64 :=
    ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [finStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store512_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setMem_zmm, ho, w1, w2, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (setMem_vkeep _ _).trans (setMem_vkeep _ _)⟩

theorem finishChunk_ok {n k : Nat} (hn : n < 2) (hk : k < 4) {s : State} {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finishChunk n k)) s fun t => ∃ v w : BitVec 512,
      (∀ q (hq : q < 8), v.extractLsb' (64 * q) 64 = (cv s.mem p)[32 * k + 8 * n + q]'(by omega_arith) ^^^
        s.mem.readW (off p (8 * (32 * k + 8 * n + q))) 64) ∧
      (∀ q (hq : q < 8), w.extractLsb' (64 * q) 64 = (cv s.mem p)[32 * k + 16 + 8 * n + q]'(by omega_arith) ^^^
        s.mem.readW (off p (8 * (32 * k + 16 + 8 * n + q))) 64) ∧
      t.mem = (s.mem.writeW (off out (256 * k + 64 * n)) v).writeW (off out (256 * k + 128 + 64 * n)) w ∧
      VKeep s t := by
  rw [finishChunk_eq, WP.block_append_iff, WP.block_append_iff]
  refine (finLoads_ok hn hk hs).mono ?_
  rintro t1 ⟨h0, h1, h4, h5, hm1, hk1⟩
  refine WP.of_runBlock ⟨_, runBlock_zops _ _, ?_⟩
  have hk2 := hk1.trans (zrun_vkeep joinOps t1)
  refine (finStores_ok (out := out) hn hk (hk2.gpr ▸ ho) (hk2.wr ▸ hw)).mono ?_
  rintro t ⟨hm, hk3⟩
  refine ⟨_, _, fun q hq => ?_, fun q hq => ?_, by rw [hm, zrun_mem, hm1], hk2.trans hk3⟩
  · have fq := (finQ n hn k hk q hq).1
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0x88 : BitVec 8).toNat (q / 2)
    rw [zmm_qz _ _ hq, join_qz2 _ hq, h4 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega_arith)]
      rw [show q / 4 = 0 by omega_arith, Nat.add_zero] at fq
      rw [cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega_arith)]
      rw [show q / 4 = 1 by omega_arith] at fq
      rw [cv_idx _ _ fq]
  · have fq := (finQ n hn k hk q hq).2
    have hs8 := Proof.Poly1305.X86_64.Avx2.sel4_lt (0xdd : BitVec 8).toNat (q / 2)
    rw [zmm_qz _ _ hq, join_qz3 _ hq, h5 q hq]
    by_cases h2 : q / 2 < 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), h0 _ (by omega_arith)]
      rw [show q / 4 = 0 by omega_arith, Nat.add_zero] at fq
      rw [cv_idx _ _ fq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), h1 _ (by omega_arith)]
      rw [show q / 4 = 1 by omega_arith] at fq
      rw [cv_idx _ _ fq]

end VG.Proof.Argon2.X86_64.Avx512

module

public import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Mem
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Sym
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Gb
public import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx512
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

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

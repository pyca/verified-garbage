module

public import VerifiedGarbage.Proof.Argon2.X86_64.Words
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
public import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Argon2.X86_64.Avx2.Gb`, which this module and modules that import it used -/

section

/-! ### `Argon2.PermuteRows`, which this module and modules that import it used -/

section

/-!
# P on four columns at once

The sixteen words P permutes, as four rows of four (`4k…4k+3` for
`k < 4`): the four column GBs of P are GB on each column of the rows at once
(`mixColumns`), and the four diagonal GBs are the same after row `k` is
rotated left by `k` places (`rotRows 1`), rotated back after it
(`rotRows 3`). This is how code keeping each row in one vector register
(of four 64-bit lanes) computes P (`permute_lanes`).
-/

@[expose] public section

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Component `k` of the result of `mix`. -/
def mixAt (k : Nat) (x : Word × Word × Word × Word) : Word :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- GB on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once. -/
def mixColumns (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => mixAt (j.val / 4)
    (mix (v[j.val % 4]'(by omega_using [])) (v[4 + j.val % 4]'(by omega_using [])) (v[8 + j.val % 4]'(by omega_using []))
      (v[12 + j.val % 4]'(by omega_using [])))

/-- Row `k` (words `4k…4k+3`) rotated left by `n · k` places. -/
def rotRows (n : Nat) (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + n * (j.val / 4)) % 4]'(by omega_using [])

theorem mixColumns_get (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (mixColumns v)[j] = mixAt (j / 4) (mix (v[j % 4]'(by omega_using [])) (v[4 + j % 4]'(by omega_using []))
      (v[8 + j % 4]'(by omega_using [])) (v[12 + j % 4]'(by omega_using []))) := by
  simp only [mixColumns, Vector.getElem_ofFn]

theorem rotRows_get (n : Nat) (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (rotRows n v)[j] = v[4 * (j / 4) + (j % 4 + n * (j / 4)) % 4]'(by omega_using [hj]) := by
  simp only [rotRows, Vector.getElem_ofFn]

theorem GB_get' (v : Vector Word 16) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (k : Nat) (hk : k < 16) :
    (GB v a b c d)[k]'hk =
      if b.1 = k then (mix (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2)).2.1
      else if c.1 = k then (mix (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2)).2.2.1
      else if d.1 = k then (mix (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2)).2.2.2
      else if a.1 = k then (mix (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2)).1 else (v[k]'hk) :=
  GB_get v hab hac had hbc hbd hcd k hk

theorem cases16 {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega_using [hj]

/-- The value of a literal index. -/
theorem val_lit (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

/-- The four column GBs of P. -/
theorem columns_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 = mixColumns v := by
  apply Vector.ext
  intro j hj
  simp only [mixColumns_get]
  obtain g0 := fun (w : Vector Word 16) => GB_get' w (a := 0) (b := 4) (c := 8) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g1 := fun (w : Vector Word 16) => GB_get' w (a := 1) (b := 5) (c := 9) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g2 := fun (w : Vector Word 16) => GB_get' w (a := 2) (b := 6) (c := 10) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g3 := fun (w : Vector Word 16) => GB_get' w (a := 3) (b := 7) (c := 11) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp only [g0, g1, g2, g3, val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- The four diagonal GBs of P. -/
theorem diagonals_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 =
      rotRows 3 (mixColumns (rotRows 1 v)) := by
  apply Vector.ext
  intro j hj
  simp only [rotRows_get, mixColumns_get]
  obtain g0 := fun (w : Vector Word 16) => GB_get' w (a := 0) (b := 5) (c := 10) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g1 := fun (w : Vector Word 16) => GB_get' w (a := 1) (b := 6) (c := 11) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g2 := fun (w : Vector Word 16) => GB_get' w (a := 2) (b := 7) (c := 8) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain g3 := fun (w : Vector Word 16) => GB_get' w (a := 3) (b := 4) (c := 9) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp only [g0, g1, g2, g3, val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- P is two rounds of GB on the columns of the rows. -/
theorem permute_lanes (v : Vector Word 16) :
    permute v = rotRows 3 (mixColumns (rotRows 1 (mixColumns v))) := by
  rw [← diagonals_eq, ← columns_eq]
  rfl

end VG.Proof.Argon2

end

end

/-!
# Argon2 on x86-64 with AVX2: P on four registers

The AVX code of `round` (`Impl/Argon2/X86_64/CompressAvx2.lean`) writes only
vector registers, so a block of it runs as `vrun`, a function of the state.
Each step of GB is proven on every quadword `k < 4` at once (`qw`, quadword
`k` of a register), then GB (`gb_qw`), and P on the sixteen words of
`ymm0`–`ymm3` (`round_words`), through `Proof.Argon2.permute_lanes`.
-/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword_paddq qword_pmuludq qword_psrlq qw_vbin qw_vshift
  qw_vpermq sel4 lo32 dword_lo dword_hi qword_eq qword_ofDwords qw_lane)
open VG.Proof.Argon2 (mix mixColumns rotRows mixAt)

/-! ## Blocks of AVX instructions -/

/-- Run instructions that write only vector registers. -/
def vrun : List VOp → State → State
  | [], s => s
  | o :: os, s => vrun os (o.exec s)

theorem runBlock_vops (os : List VOp) (s : State) :
    runBlock isa (os.map .vop) s = some (vrun os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem vrun_append (a b : List VOp) (s : State) : vrun (a ++ b) s = vrun b (vrun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

theorem VOp.exec_mxcsr (o : VOp) (s : State) : (o.exec s).mxcsr = s.mxcsr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

@[simp] theorem vrun_gpr (os : List VOp) (s : State) : (vrun os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_gpr o s)

@[simp] theorem vrun_mem (os : List VOp) (s : State) : (vrun os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_mem o s)

@[simp] theorem vrun_rd (os : List VOp) (s : State) : (vrun os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_rd o s)

@[simp] theorem vrun_wr (os : List VOp) (s : State) : (vrun os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_wr o s)

@[simp] theorem vrun_mxcsr (os : List VOp) (s : State) : (vrun os s).mxcsr = s.mxcsr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_mxcsr o s)

/-! ## Quadword operations -/

theorem qword_pxor (x y : BitVec 128) (i : Nat) :
    qword (XBinOp.eval .pxor x y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, qword, hj]

theorem lo32_eq (x : Word) : lo32 x = x &&& 0xffffffff := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [lo32, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hj,
    decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : j < 32
  · simp only [h, decide_true, Bool.true_and]
    rw [show (0xffffffff : BitVec 64).getLsbD j = true by revert j; decide, Bool.and_true]
  · simp only [h, decide_false, Bool.false_and]
    rw [show (0xffffffff : BitVec 64).getLsbD j = false by revert h; revert j; decide,
      Bool.and_false]

/-- What `addMul` computes. -/
theorem addMul_eq (a b : Word) :
    a + b + (lo32 a * lo32 b + lo32 a * lo32 b) = Spec.Argon2.addMul a b := by
  simp only [Spec.Argon2.addMul, lo32_eq]
  generalize a &&& 0xffffffff = x
  generalize b &&& 0xffffffff = y
  grind

theorem rotateRight_32 (h l : BitVec 32) : (h ++ l).rotateRight 32 = l ++ h := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_append]
  by_cases h1 : j < 32
  · simp [h1, show ¬ 32 % 64 + j < 32 by omega_using []]
  · simp [h1, decide_eq_true (show j < 64 by omega_using [hj]), show j - 32 < 32 by omega_using [hj]]

theorem qword_shuf_b1 (x : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (shufDwords x 0xb1) i = (qword x i).rotateRight 32 := by
  have e : shufDwords x 0xb1 = ofDwords (dword x 1) (dword x 0) (dword x 3) (dword x 2) := by
    simp only [shufDwords]; rfl
  rw [e, qword_ofDwords _ _ _ _ hi, qword_eq]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [ite_true, rotateRight_32]
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, rotateRight_32]

/-- The `vpshufb` masks rotating each quadword right by 24 and by 16 bits. -/
abbrev rot24Mask : BitVec 128 := 0x0a09080f0e0d0c0b0201000706050403#128
abbrev rot16Mask : BitVec 128 := 0x09080f0e0d0c0b0a0100070605040302#128

theorem getLsbD_qword (x : BitVec 128) {q i : Nat} (hi : i < 64) :
    (qword x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qword, hi]

theorem getLsbD_qword_ofBytes (f : Nat → BitVec 8) {i m : Nat} (hi : i < 2) (hm : m < 64) :
    (qword (ofBytes f) i).getLsbD m = (f (8 * i + m / 8)).getLsbD (m % 8) := by
  rw [getLsbD_qword _ hm, show 64 * i + m = 8 * (8 * i + m / 8) + m % 8 by omega_using [],
    getLsbD_ofBytes _ (by omega_using [hi, hm]) (Nat.mod_lt _ (by omega_using []))]

theorem pshufb_rot24_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rot24Mask = ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + 3) % 8) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_rot16_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rot16Mask = ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + 2) % 8) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem qword_bytes_rot (a : BitVec 128) (n : Nat) (hn : n < 8) {i : Nat} (hi : i < 2) :
    qword (ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + n) % 8)) i =
      (qword a i).rotateRight (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_qword_ofBytes _ hi hm, BitVec.getLsbD_rotateRight]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega_using [])
  simp only [byte, BitVec.getLsbD_extractLsb', h8,
    decide_true, Bool.true_and, Nat.mod_eq_of_lt (show 8 * n < 64 by omega_using [hn])]
  by_cases h : m < 64 - 8 * n
  · simp only [h, ite_true]
    rw [getLsbD_qword _ (by omega_using [h])]
    exact congrArg _ (by omega_using [h])
  · simp only [h, ite_false]
    rw [decide_eq_true (by omega_using [hm]), Bool.true_and,
      getLsbD_qword _ (by omega_using [hm])]
    exact congrArg _ (by omega_using [hn, hm, h])

theorem qword_pshufb_rot24 (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pshufb a rot24Mask) i = (qword a i).rotateRight 24 := by
  rw [pshufb_rot24_bytes, qword_bytes_rot a 3 (by decide) hi]

theorem qword_pshufb_rot16 (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pshufb a rot16Mask) i = (qword a i).rotateRight 16 := by
  rw [pshufb_rot16_bytes, qword_bytes_rot a 2 (by decide) hi]

/-- `(x ⊕ y) >>> 63` as `vpsrlq`, `vpaddq` and `vpxor`. -/
theorem rot63_eq (x : Word) : (x + x) ^^^ x >>> 63 = x.rotateRight 63 := by
  rw [show x + x = x <<< 1 by bv_omega]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateRight]
  by_cases h : j = 0
  · subst j; simp
  · simp only [BitVec.getLsbD_of_ge x (63 + j) (by omega_using [h]), Bool.xor_false]
    simp [h]

/-! ## Quadwords of registers after an instruction -/

theorem qw_vpshufd (s : State) (d a r : XReg) (o : BitVec 8) (k : Nat) :
    qw ((VOp.vpshufd .l256 d a o).exec s) r k =
      if r = d then qword (shufDwords (s.lane a (k / 2)) o) (k % 2) else qw s r k := by
  simp only [qw, lane_vpshufd256]
  split <;> rfl

theorem lane_vpermq (s : State) (d a r : XReg) (o : BitVec 8) {l : Nat} (hr : r ≠ d) :
    ((VOp.vpermq d a o).exec s).lane r l = s.lane r l := by
  simp only [VOp.exec, State.lane_setV256, hr, ite_false]

/-- The selectors of `vpermq` with `0x39`, `0x4e` and `0x93`: rotations by
one, two and three places. -/
theorem sel4_39 {k : Nat} (hk : k < 4) : sel4 (0x39 : BitVec 8).toNat k = (k + 1) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_4e {k : Nat} (hk : k < 4) : sel4 (0x4e : BitVec 8).toNat k = (k + 2) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel4_93 {k : Nat} (hk : k < 4) : sel4 (0x93 : BitVec 8).toNat k = (k + 3) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-! ## The steps of GB, on each quadword -/

/-- The masks of `vpshufb` in `ymm14` and `ymm15`. -/
def Masks (s : State) : Prop :=
  ∀ l < 2, s.lane .xmm14 l = rot24Mask ∧ s.lane .xmm15 l = rot16Mask

def addMulOps (a b : XReg) : List VOp :=
  [.vbin .vpmuludq .l256 .xmm4 a b, .vbin .vpaddq .l256 a a b, .vbin .vpaddq .l256 .xmm4 .xmm4 .xmm4,
    .vbin .vpaddq .l256 a a .xmm4]
def xorRot32Ops (d a : XReg) : List VOp := [.vbin .vpxor .l256 d d a, .vpshufd .l256 d d 0xb1]
def xorRot24Ops (d a : XReg) : List VOp := [.vbin .vpxor .l256 d d a, .vbin .vpshufb .l256 d d .xmm14]
def xorRot16Ops (d a : XReg) : List VOp := [.vbin .vpxor .l256 d d a, .vbin .vpshufb .l256 d d .xmm15]
def xorRot63Ops (d a : XReg) : List VOp :=
  [.vbin .vpxor .l256 d d a, .vshift .psrlq .l256 .xmm4 d 63, .vbin .vpaddq .l256 d d d,
    .vbin .vpxor .l256 d d .xmm4]

theorem addMul_qw {a b : XReg} (ha : a ≠ .xmm4) (hb : b ≠ .xmm4) (s : State)
    {r : XReg} (hr : r ≠ .xmm4) (k : Nat) :
    qw (vrun (addMulOps a b) s) r k =
      if r = a then Spec.Argon2.addMul (qw s a k) (qw s b k) else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [addMulOps, vrun, qw_vbin, VBinOp.sse, qword_paddq _ _ h2, qword_pmuludq _ _ h2, qw_lane,
    lane_vbin256, hr, ha, hb, ha.symm, ite_true, ite_false]
  split
  · rw [addMul_eq]
  · rfl

theorem xorRot32_qw {d a : XReg} (s : State) (r : XReg) (k : Nat) :
    qw (vrun (xorRot32Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 32 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRot32Ops, vrun, qw_vpshufd, qw_vbin, VBinOp.sse, lane_vbin256, qword_shuf_b1 _ h2,
    qword_pxor, qw_lane, ite_true]
  split <;> rfl

theorem xorRot24_qw {d a : XReg} (hd : d ≠ .xmm14) (s : State) (hm : Masks s)
    (r : XReg) {k : Nat} (hk : k < 4) :
    qw (vrun (xorRot24Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 24 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRot24Ops, vrun, qw_vbin, VBinOp.sse, lane_vbin256, hd.symm, ite_true,
    ite_false, (hm (k / 2) (by omega_using [hk])).1, qword_pshufb_rot24 _ h2, qword_pxor, qw_lane]
  split <;> rfl

theorem xorRot16_qw {d a : XReg} (hd : d ≠ .xmm15) (s : State) (hm : Masks s)
    (r : XReg) {k : Nat} (hk : k < 4) :
    qw (vrun (xorRot16Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 16 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRot16Ops, vrun, qw_vbin, VBinOp.sse, lane_vbin256, hd.symm, ite_true,
    ite_false, (hm (k / 2) (by omega_using [hk])).2, qword_pshufb_rot16 _ h2, qword_pxor, qw_lane]
  split <;> rfl

theorem xorRot63_qw {d a : XReg} (hd : d ≠ .xmm4) (s : State) {r : XReg}
    (hr : r ≠ .xmm4) (k : Nat) :
    qw (vrun (xorRot63Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 63 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRot63Ops, vrun, qw_vbin, qw_vshift, VBinOp.sse, lane_vbin256, lane_vshift256,
    hd, hd.symm, hr, ite_true, ite_false, qword_pxor, qword_paddq _ _ h2,
    qword_psrlq _ (show (63 : BitVec 8).toNat < 64 by decide) h2, qw_lane]
  split
  · rw [show (63 : BitVec 8).toNat = 63 from rfl, rot63_eq]
  · rfl

/-! ### The masks -/

theorem Masks.vbin {s : State} (h : Masks s) {op : VBinOp} {d a b : XReg} (h14 : d ≠ .xmm14)
    (h15 : d ≠ .xmm15) : Masks ((VOp.vbin op .l256 d a b).exec s) := by
  intro l hl
  simp only [lane_vbin256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vshift {s : State} (h : Masks s) {op : XShiftOp} {d a : XReg} {n : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : Masks ((VOp.vshift op .l256 d a n).exec s) := by
  intro l hl
  simp only [lane_vshift256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vpshufd {s : State} (h : Masks s) {d a : XReg} {o : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : Masks ((VOp.vpshufd .l256 d a o).exec s) := by
  intro l hl
  simp only [lane_vpshufd256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vpermq {s : State} (h : Masks s) {d a : XReg} {o : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : Masks ((VOp.vpermq d a o).exec s) := by
  intro l hl
  rw [lane_vpermq _ _ _ _ _ h14.symm, lane_vpermq _ _ _ _ _ h15.symm]
  exact h l hl

/-! ## GB -/

abbrev x0 : XReg := .xmm0
abbrev x1 : XReg := .xmm1
abbrev x2 : XReg := .xmm2
abbrev x3 : XReg := .xmm3

def gbOps : List VOp :=
  addMulOps x0 x1 ++ xorRot32Ops x3 x0 ++ addMulOps x2 x3 ++ xorRot24Ops x1 x2 ++
  addMulOps x0 x1 ++ xorRot16Ops x3 x0 ++ addMulOps x2 x3 ++ xorRot63Ops x1 x2

section
variable {s : State} (h : Masks s) {a b : XReg} (h14 : a ≠ .xmm14) (h15 : a ≠ .xmm15)
include h h14 h15

theorem Masks.addMul : Masks (vrun (addMulOps a b) s) :=
  (((h.vbin (by decide) (by decide)).vbin h14 h15).vbin (by decide) (by decide)).vbin h14 h15

theorem Masks.xorRot32 : Masks (vrun (xorRot32Ops a b) s) := (h.vbin h14 h15).vpshufd h14 h15
theorem Masks.xorRot24 : Masks (vrun (xorRot24Ops a b) s) := (h.vbin h14 h15).vbin h14 h15
theorem Masks.xorRot16 : Masks (vrun (xorRot16Ops a b) s) := (h.vbin h14 h15).vbin h14 h15
theorem Masks.xorRot63 : Masks (vrun (xorRot63Ops a b) s) :=
  (((h.vbin h14 h15).vshift (by decide) (by decide)).vbin h14 h15).vbin h14 h15

end

theorem gb_masks {s : State} (h : Masks s) : Masks (vrun gbOps s) := by
  simp only [gbOps, vrun_append]
  exact (((((((h.addMul (by decide) (by decide)).xorRot32 (by decide) (by decide)).addMul
    (by decide) (by decide)).xorRot24 (by decide) (by decide)).addMul (by decide) (by decide)).xorRot16
    (by decide) (by decide)).addMul (by decide) (by decide)).xorRot63 (by decide) (by decide)

/-- GB on each quadword of `ymm0`–`ymm3`. -/
theorem gb_qw {s : State} (h : Masks s) {k : Nat} (hk : k < 4) :
    (qw (vrun gbOps s) x0 k, qw (vrun gbOps s) x1 k, qw (vrun gbOps s) x2 k,
      qw (vrun gbOps s) x3 k) = mix (qw s x0 k) (qw s x1 k) (qw s x2 k) (qw s x3 k) := by
  have m3 : Masks (vrun (addMulOps x2 x3) (vrun (xorRot32Ops x3 x0) (vrun (addMulOps x0 x1) s))) :=
    ((h.addMul (by decide) (by decide)).xorRot32 (by decide) (by decide)).addMul (by decide) (by decide)
  have m5 : Masks (vrun (addMulOps x0 x1) (vrun (xorRot24Ops x1 x2) (vrun (addMulOps x2 x3)
      (vrun (xorRot32Ops x3 x0) (vrun (addMulOps x0 x1) s))))) :=
    (m3.xorRot24 (by decide) (by decide)).addMul (by decide) (by decide)
  simp only [gbOps, vrun_append]
  simp (disch := decide) only [addMul_qw (a := x0) (b := x1) (by decide) (by decide),
    addMul_qw (a := x2) (b := x3) (by decide) (by decide),
    xorRot32_qw, xorRot24_qw (d := x1) (by decide) _ m3 _ hk,
    xorRot16_qw (d := x3) (by decide) _ m5 _ hk, xorRot63_qw (d := x1) (by decide),
    ↓reduceIte, reduceCtorEq]
  rfl

/-! ## P -/

def diagOps : List VOp := [.vpermq x1 x1 0x39, .vpermq x2 x2 0x4e, .vpermq x3 x3 0x93]
def undiagOps : List VOp := [.vpermq x1 x1 0x93, .vpermq x2 x2 0x4e, .vpermq x3 x3 0x39]
def roundOps : List VOp := gbOps ++ diagOps ++ gbOps ++ undiagOps

theorem round_eq : round = roundOps.map .vop := rfl

/-- The sixteen words in `ymm0`–`ymm3`: word `4i + k` is quadword `k` of `vreg i`. -/
def words (s : State) : Vector Word 16 :=
  Vector.ofFn fun j => qw s (vreg (j.val / 4)) (j.val % 4)

theorem words_get (s : State) (j : Nat) (hj : j < 16) :
    (words s)[j] = qw s (vreg (j / 4)) (j % 4) := by
  simp only [words, Vector.getElem_ofFn]

theorem cases_div4 {j : Nat} (hj : j < 16) : j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3 := by
  omega_using [hj]

theorem gb_words {s : State} (h : Masks s) : words (vrun gbOps s) = mixColumns (words s) := by
  apply Vector.ext
  intro j hj
  have g := gb_qw h (k := j % 4) (Nat.mod_lt _ (by decide))
  rw [words_get _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, words_get _ _ (by omega_using []),
    words_get _ _ (by omega_using []), words_get _ _ (by omega_using []), words_get _ _ (by omega_using []),
    show j % 4 / 4 = 0 by omega_using [], show (4 + j % 4) / 4 = 1 by omega_using [], show (8 + j % 4) / 4 = 2 by omega_using [],
    show (12 + j % 4) / 4 = 3 by omega_using [], Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega_using [],
    show (8 + j % 4) % 4 = j % 4 by omega_using [], show (12 + j % 4) % 4 = j % 4 by omega_using []]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem masks_diag {s : State} (h : Masks s) : Masks (vrun diagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem masks_undiag {s : State} (h : Masks s) : Masks (vrun undiagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem diag_words (s : State) : words (vrun diagOps s) = rotRows 1 (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ (by omega_using [hj]),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega_using [],
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega_using []]
  simp only [diagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega_using []) only [vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) : words (vrun undiagOps s) = rotRows 3 (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ (by omega_using [hj]),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega_using [],
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega_using []]
  simp only [undiagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega_using []) only [vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega_using []

theorem round_masks {s : State} (h : Masks s) : Masks (vrun roundOps s) := by
  simp only [roundOps, vrun_append]
  exact masks_undiag (gb_masks (masks_diag (gb_masks h)))

/-- P on the sixteen words of `ymm0`–`ymm3`. -/
theorem round_words {s : State} (h : Masks s) : words (vrun roundOps s) = permute (words s) := by
  simp only [roundOps, vrun_append]
  rw [Proof.Argon2.permute_lanes, undiag_words, gb_words (masks_diag (gb_masks h)), diag_words,
    gb_words h]

end VG.Proof.Argon2.X86_64.Avx2

end

end

/-!
# Argon2 on x86-64 with AVX2: rows and columns in scratch

A row of the block P permutes (`working`, `[1024, 2048)` of scratch) is
loaded into `ymm0`–`ymm3` with four 32-byte loads, permuted (`round_words`)
and stored back; a column with two 16-byte loads per register, joined by
`vinserti128`, and two 16-byte stores. Either way the block becomes
`Spec.Argon2.permuteAt` of the row or column (`row_ok`, `col_ok`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at)
open VG.Proof.Argon2 (gather gather_get eq_scatter rowIndex_injective colIndex_injective)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword256_ymm qword256_eq qw_setV256 qw_setV128 qw_lane)

/-! ## What the vector code keeps -/

/-- The general-purpose registers, permissions and MXCSR are those of `s`. -/
structure VKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem VKeep.refl (s : State) : VKeep s s := ⟨rfl, rfl, rfl, rfl⟩

theorem VKeep.trans {s t u : State} (h : VKeep s t) (h' : VKeep t u) : VKeep s u :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mxcsr.trans h.mxcsr⟩

theorem _root_.VG.Proof.Argon2.X86_64.Scratch.of_vkeep {s t : State} {p : Addr} (hs : Scratch s p) (h : VKeep s t) : Scratch t p :=
  ⟨by rw [h.gpr]; exact hs.reg, h.wr ▸ hs.wr⟩

theorem vrun_vkeep (os : List VOp) (s : State) : VKeep s (vrun os s) :=
  ⟨vrun_gpr os s, vrun_rd os s, vrun_wr os s, vrun_mxcsr os s⟩

/-! ## Loads and stores, quadword by quadword -/

theorem qword256_readW (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword256 (m.readW a 256) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword256, show 64 * k = 8 * (8 * k) by omega_using []]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega_using [hk])

theorem qword_readW128 (m : Mem) (a : Addr) {k : Nat} (hk : k < 2) :
    qword (m.readW a 128) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword, show 64 * k = 8 * (8 * k) by omega_using []]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega_using [hk])

theorem qw_set256 (s : State) (d r : XReg) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (v.extractLsb' 0 128) (v.extractLsb' 128 128)) r k =
      if r = d then qword256 v k else qw s r k := by
  rw [qw_setV256]
  split
  · rw [qword256_eq]
    rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- A word of `working` after a 32-byte write to it. -/
theorem working_write256 (m : Mem) (p : Addr) {c : Nat} (hc : c < 32) (v : BitVec 256) (i : Fin 128) :
    (working (m.writeW (off p (1024 + 32 * c)) v) p)[i] =
      if i.val / 4 = c then qword256 v (i.val % 4) else (working m p)[i] := by
  rw [working_get, working_get]
  split
  · rename_i h
    have e : off p (1024 + 8 * i.val) = off p (1024 + 32 * c) + BitVec.ofNat 64 (8 * (i.val % 4)) :=
      (Offset.add_add_eq p (by omega_using [h])).symm
    rw [word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 4)) (n := 8) (by omega_using []) (by decide)).trans ?_
    rw [qword256, show 8 * (8 * (i.val % 4)) = 64 * (i.val % 4) by omega_using []]
  · exact readW_writeW_off m p v (n := 8) (by omega_using []) (by omega_using [hc]) (by omega_arith)

/-- A word of `working` after a 16-byte write to it. -/
theorem working_write128 (m : Mem) (p : Addr) {c : Nat} (hc : c < 64) (v : BitVec 128) (i : Fin 128) :
    (working (m.writeW (off p (1024 + 16 * c)) v) p)[i] =
      if i.val / 2 = c then qword v (i.val % 2) else (working m p)[i] := by
  rw [working_get, working_get]
  split
  · rename_i h
    have e : off p (1024 + 8 * i.val) = off p (1024 + 16 * c) + BitVec.ofNat 64 (8 * (i.val % 2)) :=
      (Offset.add_add_eq p (by omega_using [h])).symm
    rw [word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 2)) (n := 8) (by omega_using []) (by decide)).trans ?_
    rw [qword, show 8 * (8 * (i.val % 2)) = 64 * (i.val % 2) by omega_using []]
  · exact readW_writeW_off m p v (n := 8) (by omega_using []) (by omega_using [hc]) (by omega_arith)

/-- A row or column is permuted if its words are P of what they were and the
others are unchanged. -/
theorem permuteAt_of (index : Fin 16 → Fin 128) (hi : Function.Injective index) (b t : Block)
    (hg : ∀ j : Fin 16, t[index j] = (permute (gather index b))[j])
    (ho : ∀ k : Fin 128, (∀ j, index j ≠ k) → t[k] = b[k]) :
    t = Spec.Argon2.permuteAt index b :=
  eq_scatter index hi b t _ (Vector.ext fun j hj => by
    rw [show (gather index t)[j] = (gather index t)[(⟨j, hj⟩ : Fin 16)] from rfl, gather_get, hg]
    rfl) ho


@[simp] theorem State.setV_mxcsr (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).mxcsr = s.mxcsr := by
  cases s; rfl

theorem Masks.setV {s : State} (h : Masks s) {len : VLen} {d : XReg} {lo hi : BitVec 128}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : Masks (s.setV len d lo hi) := by
  intro l hl
  cases len
  · simp only [State.lane_setV128, h14.symm, h15.symm, ite_false]; exact h l hl
  · simp only [State.lane_setV256, h14.symm, h15.symm, ite_false]; exact h l hl

/-! ## Rows -/

theorem loadRow_eq (i : Nat) : loadRow i =
    [.vmovdquLoad .l256 x0 (at_ .rcx (rowOff i 0)), .vmovdquLoad .l256 x1 (at_ .rcx (rowOff i 1)),
      .vmovdquLoad .l256 x2 (at_ .rcx (rowOff i 2)), .vmovdquLoad .l256 x3 (at_ .rcx (rowOff i 3))] :=
  rfl

theorem storeRow_eq (i : Nat) : storeRow i =
    [.vmovdquStore .l256 (at_ .rcx (rowOff i 0)) x0, .vmovdquStore .l256 (at_ .rcx (rowOff i 1)) x1,
      .vmovdquStore .l256 (at_ .rcx (rowOff i 2)) x2, .vmovdquStore .l256 (at_ .rcx (rowOff i 3)) x3] :=
  rfl

theorem loadRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (.block (loadRow i)) s fun t =>
      words t = gather (rowIndex ⟨i, hi⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VKeep s t ∧ Masks t := by
  have r (k : Nat) (hk : k < 4) := hs.read (d := rowOff i k) (n := 32) (by unfold rowOff; omega_using [hi, hk])
  apply WP.of_runBlock
  simp only [loadRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide),
    r 1 (by decide), r 2 (by decide), r 3 (by decide), ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨by simp only [State.setV_gpr], by simp only [State.setV_rd],
      by simp only [State.setV_wr], by simp only [State.setV_mxcsr]⟩,
    (((hm.setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)⟩
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, show (gather (rowIndex ⟨i, hi⟩) (working s.mem p))[j] =
      (working s.mem p)[rowIndex ⟨i, hi⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [vreg, qw_set256 _ _ _ _ hk, ↓reduceIte, reduceCtorEq, qword256_readW _ _ hk] <;>
    exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by simp only [rowIndex, rowOff]; omega_using [e]))


theorem ymm_setMem (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

theorem setMem_vkeep (s : State) (m : Mem) : VKeep s (s.setMem m) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Masks.setMem {s : State} (h : Masks s) (m : Mem) : Masks (s.setMem m) := by
  intro l hl; simp only [State.setMem_lane]; exact h l hl

theorem qw_setMem (s : State) (m : Mem) (r : XReg) (k : Nat) : qw (s.setMem m) r k = qw s r k := by
  simp only [qw, State.setMem_lane]

/-- The region of `working` contains a write at `1024 + d`. -/
theorem working_contains (p : Addr) {d n : Nat} (h : d + n ≤ 1024) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (1024 + d)) n :=
  Offset.contains p (by omega_using []) (by omega_using [h]) (by omega_using [])

theorem storeRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeRow i)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val / 16 = i then qw s (vreg (w.val % 16 / 4)) (w.val % 4) else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ words t = words s ∧
      (Masks s → Masks t) := by
  have w (k : Nat) (hk : k < 4) := hs.write (d := rowOff i k) (n := 32) (by unfold rowOff; omega_arith)
  have o (k : Nat) : rowOff i k = 1024 + 32 * (4 * i + k) := by unfold rowOff; omega_arith
  apply WP.of_runBlock
  simp only [storeRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, ymm_setMem, hs.reg, w 0 (by decide),
    w 1 (by decide), w 2 (by decide), w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left']
  simp only [o]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ((((h.setMem _).setMem _).setMem _).setMem _)⟩
  · have hx := x.isLt
    rw [working_write256 _ p (show 4 * i + 3 < 32 by omega_arith),
      working_write256 _ p (show 4 * i + 2 < 32 by omega_arith),
      working_write256 _ p (show 4 * i + 1 < 32 by omega_arith),
      working_write256 _ p (show 4 * i + 0 < 32 by omega_arith)]
    have hq : x.val % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases h : x.val / 16 = i
    · have : x.val % 16 / 4 = 0 ∨ x.val % 16 / 4 = 1 ∨ x.val % 16 / 4 = 2 ∨ x.val % 16 / 4 = 3 := by
        omega_arith
      rcases this with e | e | e | e <;>
        simp only [h, ite_true, e, vreg, show x.val / 4 = 4 * i + x.val % 16 / 4 by omega_arith,
          qword256_ymm _ _ hq] <;> simp
    · simp only [h, ite_false, show x.val / 4 ≠ 4 * i + 3 by omega_arith, show x.val / 4 ≠ 4 * i + 2 by omega_arith,
        show x.val / 4 ≠ 4 * i + 1 by omega_arith, show x.val / 4 ≠ 4 * i + 0 by omega_arith]
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (working_contains p (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (working_contains p (by omega_arith))
  · exact ((((setMem_vkeep _ _).trans (setMem_vkeep _ _)).trans (setMem_vkeep _ _)).trans
      (setMem_vkeep _ _))
  · apply Vector.ext; intro j hj
    simp only [words_get, qw_setMem]


/-- What a row or column step leaves. -/
structure Permuted (index : Fin 16 → Fin 128) (p : Addr) (s t : State) : Prop where
  working : working t.mem p = Spec.Argon2.permuteAt index (working s.mem p)
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VKeep s t
  masks : Masks t

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (vrun roundOps s)) :
    WP isa (.block round) s Q := by
  rw [round_eq]
  exact WP.of_runBlock ⟨_, runBlock_vops _ _, h⟩

/-- P on row `i`. -/
theorem row_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (row i) s (Permuted (rowIndex ⟨i, hi⟩) p s) := by
  unfold row
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadRow_ok hi hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine round_then ?_
  have hs2 : Scratch (vrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (vrun_vkeep _ _)
  refine (storeRow_ok hi hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := round_words hm1
  rw [vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((vrun_vkeep _ _).trans hk), hmt (round_masks hm1)⟩
  apply permuteAt_of _ (rowIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [rowIndex]; omega_using [])), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [words_get _ _ hj] at e
    simp only [rowIndex, show (16 * i + j.val) % 16 = j.val by omega_using [],
      show (16 * i + j.val) % 4 = j.val % 4 by omega_using [], e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨k.val % 16, by omega_using []⟩ (Fin.ext (by simp only [rowIndex]; omega_using [h])))]


/-! ## Columns -/

theorem xmm_eq_lane (s : State) (r : XReg) : s.xmm r = s.lane r 0 := rfl

theorem loadCol_eq (j : Nat) : loadCol j = [
    .vmovdquLoad .l128 x0 (at_ .rcx (colOff j 0 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 0 true)),
    .vop (.vinserti128 x0 x0 .xmm4 1),
    .vmovdquLoad .l128 x1 (at_ .rcx (colOff j 1 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 1 true)),
    .vop (.vinserti128 x1 x1 .xmm4 1),
    .vmovdquLoad .l128 x2 (at_ .rcx (colOff j 2 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 2 true)),
    .vop (.vinserti128 x2 x2 .xmm4 1),
    .vmovdquLoad .l128 x3 (at_ .rcx (colOff j 3 false)), .vmovdquLoad .l128 .xmm4 (at_ .rcx (colOff j 3 true)),
    .vop (.vinserti128 x3 x3 .xmm4 1)] := rfl

theorem storeCol_eq (j : Nat) : storeCol j = [
    .vmovdquStore .l128 (at_ .rcx (colOff j 0 false)) x0, .vop (.vextracti128 .xmm4 x0 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 0 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 1 false)) x1, .vop (.vextracti128 .xmm4 x1 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 1 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 2 false)) x2, .vop (.vextracti128 .xmm4 x2 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 2 true)) .xmm4,
    .vmovdquStore .l128 (at_ .rcx (colOff j 3 false)) x3, .vop (.vextracti128 .xmm4 x3 1),
    .vmovdquStore .l128 (at_ .rcx (colOff j 3 true)) .xmm4] := rfl

theorem vinserti128_1 (s : State) (d a b : XReg) :
    (VOp.vinserti128 d a b 1).exec s = s.setV .l256 d (s.lane a 0) (s.xmm b) := rfl

theorem vextracti128_1 (s : State) (d a : XReg) :
    (VOp.vextracti128 d a 1).exec s = s.setV .l128 d (s.lane a 1) 0 := rfl

theorem colOff_eq (j k : Nat) (hi : Bool) :
    colOff j k hi = 1024 + 16 * (16 * k + j + if hi then 8 else 0) := by
  unfold colOff; cases hi <;> simp <;> omega_using []

theorem loadCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (.block (loadCol c)) s fun t =>
      words t = gather (colIndex ⟨c, hc⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VKeep s t ∧ Masks t := by
  have r (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.read (d := colOff c k hi) (n := 16) (by rw [colOff_eq]; cases hi <;> simp <;> omega_using [hc, hk])
  apply WP.of_runBlock
  simp only [loadCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide), r 1 (by decide), r 2 (by decide),
    r 3 (by decide), ite_true, Option.map_some, Option.some.injEq, exists_eq_left', vinserti128_1]
  refine ⟨?_, trivial, ⟨by simp only [State.setV_gpr], by simp only [State.setV_rd],
    by simp only [State.setV_wr], by simp only [State.setV_mxcsr]⟩, ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [words_get _ _ hj, show (gather (colIndex ⟨c, hc⟩) (working s.mem p))[j] =
        (working s.mem p)[colIndex ⟨c, hc⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
    have h2 : j % 4 / 2 = 0 ∨ j % 4 / 2 = 1 := by omega_using []
    rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> rcases h2 with h | h <;>
      simp only [vreg, qw, State.lane_setV256, State.lane_setV128, xmm_eq_lane, h, ↓reduceIte,
        reduceCtorEq, qword_readW128 _ _ (Nat.mod_lt _ (by decide) : j % 4 % 2 < 2)]
    all_goals exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by
      simp only [colIndex, colOff, Bool.false_eq_true, ite_true, ite_false]; omega_using [e, h]))
  · exact (((((((((((hm.setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide) (by decide)


@[simp] theorem State.setMem_mxcsr (s : State) (m : Mem) : (s.setMem m).mxcsr = s.mxcsr := by
  cases s; rfl

theorem vreg_ne4 (i : Nat) : vreg i ≠ .xmm4 := by
  unfold vreg; split <;> decide

theorem qw_col (s : State) {k b x : Nat} (h1 : x / 32 = k) (h2 : x / 16 % 2 = b) :
    qword (s.lane (vreg k) b) (x % 2) = qw s (vreg (x / 32)) (2 * (x / 16 % 2) + x % 2) := by
  rw [h1, h2, qw, show (2 * b + x % 2) / 2 = b by omega_using [], show (2 * b + x % 2) % 2 = x % 2 by omega_using []]

/-- Whether word `8 q + r` of the block is in row `2 k` of column `c`. -/
theorem col_cond (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c) = (q = 2 * k ∧ r = c) := by
  apply propext; omega_using [hr, hc]

/-- Whether word `8 q + r` of the block is in row `2 k + 1` of column `c`. -/
theorem col_cond8 (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c + 8) = (q = 2 * k + 1 ∧ r = c) := by
  apply propext; omega_using [hr, hc]

theorem storeCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCol c)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val % 16 / 2 = c then qw s (vreg (w.val / 32)) (2 * (w.val / 16 % 2) + w.val % 2)
        else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ words t = words s ∧
      (Masks s → Masks t) := by
  have w (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.write (d := colOff c k hi) (n := 16) (by rw [colOff_eq]; cases hi <;> simp <;> omega_using [hc, hk])
  apply WP.of_runBlock
  simp only [storeCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128_eq, ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setV_wr, State.setV_gpr,
    State.setV_mem, State.setMem_xmm, hs.reg, w 0 (by decide), w 1 (by decide), w 2 (by decide),
    w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left', vextracti128_1]
  simp only [colOff_eq, Bool.false_eq_true, Nat.add_zero, xmm_eq_lane,
    State.setMem_lane, State.lane_setV128, ↓reduceIte, reduceCtorEq]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ?_⟩
  · have hx := x.isLt
    rw [working_write128 _ p (show 16 * 3 + c + 8 < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 3 + c < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 2 + c + 8 < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 2 + c < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 1 + c + 8 < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 1 + c < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 0 + c + 8 < 64 by omega_using [hc]),
      working_write128 _ p (show 16 * 0 + c < 64 by omega_using [hc])]
    obtain ⟨q, hq16⟩ : ∃ q, x.val / 16 = q := ⟨_, rfl⟩
    have hr : x.val % 16 / 2 < 8 := by omega_using []
    rw [show x.val / 2 = 8 * q + x.val % 16 / 2 by omega_using [hq16]]
    simp only [col_cond _ _ _ _ hr hc, col_cond8 _ _ _ _ hr hc]
    by_cases h : x.val % 16 / 2 = c
    · simp only [h, and_true, ↓reduceIte]
      rcases (by omega_using [hq16] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      · exact qw_col s (k := 0) (b := 0) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 0) (b := 1) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 1) (b := 0) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 1) (b := 1) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 2) (b := 0) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 2) (b := 1) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 3) (b := 0) (by omega_using [hq16]) (by omega_using [hq16])
      · exact qw_col s (k := 3) (b := 1) (by omega_using [hq16]) (by omega_using [hq16])
    · simp only [h, and_false, ↓reduceIte]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (working_contains p (by omega))
      | exact Frame.refl _ _)
  · exact ⟨by simp only [State.setMem_gpr, State.setV_gpr], by simp only [State.setMem_rd, State.setV_rd],
      by simp only [State.setMem_wr, State.setV_wr], by simp only [State.setMem_mxcsr, State.setV_mxcsr]⟩
  · apply Vector.ext; intro j hj
    simp only [words_get, qw_setMem, qw_setV128, vreg_ne4, ite_false]
  · exact ((((((((((((h.setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _)


/-- P on column `c`. -/
theorem col_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : Masks s) :
    WP isa (col c) s (Permuted (colIndex ⟨c, hc⟩) p s) := by
  unfold col
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (loadCol_ok hc hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine round_then ?_
  have hs2 : Scratch (vrun roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (vrun_vkeep _ _)
  refine (storeCol_ok hc hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := round_words hm1
  rw [vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((vrun_vkeep _ _).trans hk), hmt (round_masks hm1)⟩
  apply permuteAt_of _ (colIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [colIndex]; omega_using [hc])), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [words_get _ _ hj] at e
    simp only [colIndex, show (16 * (j.val / 2) + 2 * c + j.val % 2) / 32 = j.val / 4 by omega_using [hc],
      show 2 * ((16 * (j.val / 2) + 2 * c + j.val % 2) / 16 % 2) + (16 * (j.val / 2) + 2 * c +
        j.val % 2) % 2 = j.val % 4 by omega_using [hc], e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨4 * (k.val / 32) + 2 * (k.val / 16 % 2) + k.val % 2, by omega_using []⟩
        (Fin.ext (by simp only [colIndex]; omega_using [h])))]

end VG.Proof.Argon2.X86_64.Avx2

import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2

/-!
# Argon2 on x86-64 with AVX2: P on four registers

The AVX code of `round` (`Impl/Argon2/X86_64/CompressAvx2.lean`) writes only
vector registers, so a block of it runs as `vrun`, a function of the state.
Each step of GB is proven on every quadword `k < 4` at once (`qw`, quadword
`k` of a register), then GB (`gb_qw`), and P on the sixteen words of
`ymm0`–`ymm3` (`round_words`), through `Proof.Argon2.permute_lanes`.
-/

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
  · simp [h1, show ¬ 32 % 64 + j < 32 by omega]
  · simp [h1, decide_eq_true (show j < 64 by omega), show j - 32 < 32 by omega]

theorem qword_shuf_b1 (x : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (shufDwords x 0xb1) i = (qword x i).rotateRight 32 := by
  have e : shufDwords x 0xb1 = ofDwords (dword x 1) (dword x 0) (dword x 3) (dword x 2) := by
    simp only [shufDwords]; rfl
  rw [e, qword_ofDwords _ _ _ _ hi, qword_eq]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
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
  rw [getLsbD_qword _ hm, show 64 * i + m = 8 * (8 * i + m / 8) + m % 8 by omega,
    getLsbD_ofBytes _ (by omega) (Nat.mod_lt _ (by omega))]

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
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byte, BitVec.getLsbD_extractLsb', h8,
    decide_true, Bool.true_and, Nat.mod_eq_of_lt (show 8 * n < 64 by omega)]
  by_cases h : m < 64 - 8 * n
  · simp only [h, ite_true]
    rw [getLsbD_qword _ (by omega)]
    exact congrArg _ (by omega)
  · simp only [h, ite_false]
    rw [decide_eq_true (by omega), Bool.true_and,
      getLsbD_qword _ (by omega)]
    exact congrArg _ (by omega)

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
  · simp only [BitVec.getLsbD_of_ge x (63 + j) (by omega), Bool.xor_false]
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
    ite_false, (hm (k / 2) (by omega)).1, qword_pshufb_rot24 _ h2, qword_pxor, qw_lane]
  split <;> rfl

theorem xorRot16_qw {d a : XReg} (hd : d ≠ .xmm15) (s : State) (hm : Masks s)
    (r : XReg) {k : Nat} (hk : k < 4) :
    qw (vrun (xorRot16Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 16 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [xorRot16Ops, vrun, qw_vbin, VBinOp.sse, lane_vbin256, hd.symm, ite_true,
    ite_false, (hm (k / 2) (by omega)).2, qword_pshufb_rot16 _ h2, qword_pxor, qw_lane]
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

theorem gb_eq : gb = gbOps.map .vop := rfl

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
  omega

theorem gb_words {s : State} (h : Masks s) : words (vrun gbOps s) = mixColumns (words s) := by
  apply Vector.ext
  intro j hj
  have g := gb_qw h (k := j % 4) (Nat.mod_lt _ (by decide))
  rw [words_get _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, words_get _ _ (by omega),
    words_get _ _ (by omega), words_get _ _ (by omega), words_get _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem masks_diag {s : State} (h : Masks s) : Masks (vrun diagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem masks_undiag {s : State} (h : Masks s) : Masks (vrun undiagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem diag_words (s : State) : words (vrun diagOps s) = rotRows 1 (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega]
  simp only [diagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) : words (vrun undiagOps s) = rotRows 3 (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega]
  simp only [undiagOps, vrun]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qw_vpermq, sel4_39, sel4_4e, sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega

theorem round_masks {s : State} (h : Masks s) : Masks (vrun roundOps s) := by
  simp only [roundOps, vrun_append]
  exact masks_undiag (gb_masks (masks_diag (gb_masks h)))

/-- P on the sixteen words of `ymm0`–`ymm3`. -/
theorem round_words {s : State} (h : Masks s) : words (vrun roundOps s) = permute (words s) := by
  simp only [roundOps, vrun_append]
  rw [Proof.Argon2.permute_lanes, undiag_words, gb_words (masks_diag (gb_masks h)), diag_words,
    gb_words h]

end VG.Proof.Argon2.X86_64.Avx2

import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.X86_64.CompressAvx2
import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Gb`. -/
section

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
  | o :: os, s => VG.Proof.Argon2.X86_64.Avx2.vrun os (o.exec s)

theorem runBlock_vops (os : List VOp) (s : State) :
    runBlock isa (os.map .vop) s = some (VG.Proof.Argon2.X86_64.Avx2.vrun os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem vrun_append (a b : List VOp) (s : State) : VG.Proof.Argon2.X86_64.Avx2.vrun (a ++ b) s = VG.Proof.Argon2.X86_64.Avx2.vrun b (VG.Proof.Argon2.X86_64.Avx2.vrun a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

theorem VOp.exec_mxcsr (o : VOp) (s : State) : (o.exec s).mxcsr = s.mxcsr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

@[simp] theorem vrun_gpr (os : List VOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx2.vrun os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_gpr o s)

@[simp] theorem vrun_mem (os : List VOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx2.vrun os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_mem o s)

@[simp] theorem vrun_rd (os : List VOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx2.vrun os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_rd o s)

@[simp] theorem vrun_wr (os : List VOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx2.vrun os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_wr o s)

@[simp] theorem vrun_mxcsr (os : List VOp) (s : State) : (VG.Proof.Argon2.X86_64.Avx2.vrun os s).mxcsr = s.mxcsr := by
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
  simp only [Spec.Argon2.addMul, VG.Proof.Argon2.X86_64.Avx2.lo32_eq]
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
  · simp only [ite_true, VG.Proof.Argon2.X86_64.Avx2.rotateRight_32]
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, VG.Proof.Argon2.X86_64.Avx2.rotateRight_32]

/-- The `vpshufb` masks rotating each quadword right by 24 and by 16 bits. -/
abbrev rot24Mask : BitVec 128 := 0x0a09080f0e0d0c0b0201000706050403#128
abbrev rot16Mask : BitVec 128 := 0x09080f0e0d0c0b0a0100070605040302#128

theorem getLsbD_qword (x : BitVec 128) {q i : Nat} (hi : i < 64) :
    (qword x q).getLsbD i = x.getLsbD (64 * q + i) := by
  simp [qword, hi]

theorem getLsbD_qword_ofBytes (f : Nat → BitVec 8) {i m : Nat} (hi : i < 2) (hm : m < 64) :
    (qword (ofBytes f) i).getLsbD m = (f (8 * i + m / 8)).getLsbD (m % 8) := by
  rw [VG.Proof.Argon2.X86_64.Avx2.getLsbD_qword _ hm, show 64 * i + m = 8 * (8 * i + m / 8) + m % 8 by omega,
    getLsbD_ofBytes _ (by omega) (Nat.mod_lt _ (by omega))]

theorem pshufb_rot24_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a VG.Proof.Argon2.X86_64.Avx2.rot24Mask = ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + 3) % 8) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_rot16_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a VG.Proof.Argon2.X86_64.Avx2.rot16Mask = ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + 2) % 8) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem qword_bytes_rot (a : BitVec 128) (n : Nat) (hn : n < 8) {i : Nat} (hi : i < 2) :
    qword (ofBytes fun j => byte a (8 * (j / 8) + (j % 8 + n) % 8)) i =
      (qword a i).rotateRight (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [VG.Proof.Argon2.X86_64.Avx2.getLsbD_qword_ofBytes _ hi hm, BitVec.getLsbD_rotateRight]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byte, BitVec.getLsbD_extractLsb', h8,
    decide_true, Bool.true_and, Nat.mod_eq_of_lt (show 8 * n < 64 by omega)]
  by_cases h : m < 64 - 8 * n
  · simp only [h, ite_true]
    rw [VG.Proof.Argon2.X86_64.Avx2.getLsbD_qword _ (by omega)]
    exact congrArg _ (by omega)
  · simp only [h, ite_false]
    rw [decide_eq_true (by omega), Bool.true_and,
      VG.Proof.Argon2.X86_64.Avx2.getLsbD_qword _ (by omega)]
    exact congrArg _ (by omega)

theorem qword_pshufb_rot24 (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pshufb a VG.Proof.Argon2.X86_64.Avx2.rot24Mask) i = (qword a i).rotateRight 24 := by
  rw [VG.Proof.Argon2.X86_64.Avx2.pshufb_rot24_bytes, VG.Proof.Argon2.X86_64.Avx2.qword_bytes_rot a 3 (by decide) hi]

theorem qword_pshufb_rot16 (a : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (XBinOp.eval .pshufb a VG.Proof.Argon2.X86_64.Avx2.rot16Mask) i = (qword a i).rotateRight 16 := by
  rw [VG.Proof.Argon2.X86_64.Avx2.pshufb_rot16_bytes, VG.Proof.Argon2.X86_64.Avx2.qword_bytes_rot a 2 (by decide) hi]

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
  ∀ l < 2, s.lane .xmm14 l = VG.Proof.Argon2.X86_64.Avx2.rot24Mask ∧ s.lane .xmm15 l = VG.Proof.Argon2.X86_64.Avx2.rot16Mask

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
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps a b) s) r k =
      if r = a then Spec.Argon2.addMul (qw s a k) (qw s b k) else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.addMulOps, VG.Proof.Argon2.X86_64.Avx2.vrun, qw_vbin, VBinOp.sse, qword_paddq _ _ h2, qword_pmuludq _ _ h2, qw_lane,
    lane_vbin256, hr, ha, hb, ha.symm, ite_true, ite_false]
  split
  · rw [VG.Proof.Argon2.X86_64.Avx2.addMul_eq]
  · rfl


theorem xorRot32_qw {d a : XReg} (s : State) (r : XReg) (k : Nat) :
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 32 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops, VG.Proof.Argon2.X86_64.Avx2.vrun, VG.Proof.Argon2.X86_64.Avx2.qw_vpshufd, qw_vbin, VBinOp.sse, lane_vbin256, VG.Proof.Argon2.X86_64.Avx2.qword_shuf_b1 _ h2,
    VG.Proof.Argon2.X86_64.Avx2.qword_pxor, qw_lane, ite_true]
  split <;> rfl

theorem xorRot24_qw {d a : XReg} (hd : d ≠ .xmm14) (s : State) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s)
    (r : XReg) {k : Nat} (hk : k < 4) :
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot24Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 24 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.xorRot24Ops, VG.Proof.Argon2.X86_64.Avx2.vrun, qw_vbin, VBinOp.sse, lane_vbin256, hd.symm, ite_true,
    ite_false, (hm (k / 2) (by omega)).1, VG.Proof.Argon2.X86_64.Avx2.qword_pshufb_rot24 _ h2, VG.Proof.Argon2.X86_64.Avx2.qword_pxor, qw_lane]
  split <;> rfl

theorem xorRot16_qw {d a : XReg} (hd : d ≠ .xmm15) (s : State) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s)
    (r : XReg) {k : Nat} (hk : k < 4) :
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot16Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 16 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.xorRot16Ops, VG.Proof.Argon2.X86_64.Avx2.vrun, qw_vbin, VBinOp.sse, lane_vbin256, hd.symm, ite_true,
    ite_false, (hm (k / 2) (by omega)).2, VG.Proof.Argon2.X86_64.Avx2.qword_pshufb_rot16 _ h2, VG.Proof.Argon2.X86_64.Avx2.qword_pxor, qw_lane]
  split <;> rfl

theorem xorRot63_qw {d a : XReg} (hd : d ≠ .xmm4) (s : State) {r : XReg}
    (hr : r ≠ .xmm4) (k : Nat) :
    qw (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot63Ops d a) s) r k =
      if r = d then (qw s d k ^^^ qw s a k).rotateRight 63 else qw s r k := by
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.xorRot63Ops, VG.Proof.Argon2.X86_64.Avx2.vrun, qw_vbin, qw_vshift, VBinOp.sse, lane_vbin256, lane_vshift256,
    hd, hd.symm, hr, ite_true, ite_false, VG.Proof.Argon2.X86_64.Avx2.qword_pxor, qword_paddq _ _ h2,
    qword_psrlq _ (show (63 : BitVec 8).toNat < 64 by decide) h2, qw_lane]
  split
  · rw [show (63 : BitVec 8).toNat = 63 from rfl, VG.Proof.Argon2.X86_64.Avx2.rot63_eq]
  · rfl

/-! ### The masks -/

theorem Masks.vbin {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {op : VBinOp} {d a b : XReg} (h14 : d ≠ .xmm14)
    (h15 : d ≠ .xmm15) : VG.Proof.Argon2.X86_64.Avx2.Masks ((VOp.vbin op .l256 d a b).exec s) := by
  intro l hl
  simp only [lane_vbin256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vshift {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {op : XShiftOp} {d a : XReg} {n : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : VG.Proof.Argon2.X86_64.Avx2.Masks ((VOp.vshift op .l256 d a n).exec s) := by
  intro l hl
  simp only [lane_vshift256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vpshufd {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {d a : XReg} {o : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : VG.Proof.Argon2.X86_64.Avx2.Masks ((VOp.vpshufd .l256 d a o).exec s) := by
  intro l hl
  simp only [lane_vpshufd256, h14.symm, h15.symm, ite_false]
  exact h l hl

theorem Masks.vpermq {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {d a : XReg} {o : BitVec 8}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : VG.Proof.Argon2.X86_64.Avx2.Masks ((VOp.vpermq d a o).exec s) := by
  intro l hl
  rw [VG.Proof.Argon2.X86_64.Avx2.lane_vpermq _ _ _ _ _ h14.symm, VG.Proof.Argon2.X86_64.Avx2.lane_vpermq _ _ _ _ _ h15.symm]
  exact h l hl

/-! ## GB -/

abbrev x0 : XReg := .xmm0
abbrev x1 : XReg := .xmm1
abbrev x2 : XReg := .xmm2
abbrev x3 : XReg := .xmm3

def gbOps : List VOp :=
  VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1 ++ VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x0 ++ VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x3 ++ VG.Proof.Argon2.X86_64.Avx2.xorRot24Ops VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x2 ++
  VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1 ++ VG.Proof.Argon2.X86_64.Avx2.xorRot16Ops VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x0 ++ VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x3 ++ VG.Proof.Argon2.X86_64.Avx2.xorRot63Ops VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x2

theorem gb_eq : gb = gbOps.map .vop := rfl

section
variable {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {a b : XReg} (h14 : a ≠ .xmm14) (h15 : a ≠ .xmm15)
include h h14 h15

theorem Masks.addMul : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps a b) s) :=
  (((h.vbin (by decide) (by decide)).vbin h14 h15).vbin (by decide) (by decide)).vbin h14 h15

theorem Masks.xorRot32 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops a b) s) := (h.vbin h14 h15).vpshufd h14 h15
theorem Masks.xorRot24 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot24Ops a b) s) := (h.vbin h14 h15).vbin h14 h15
theorem Masks.xorRot16 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot16Ops a b) s) := (h.vbin h14 h15).vbin h14 h15
theorem Masks.xorRot63 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot63Ops a b) s) :=
  (((h.vbin h14 h15).vshift (by decide) (by decide)).vbin h14 h15).vbin h14 h15

end

theorem gb_masks {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) := by
  simp only [VG.Proof.Argon2.X86_64.Avx2.gbOps, VG.Proof.Argon2.X86_64.Avx2.vrun_append]
  exact (((((((h.addMul (by decide) (by decide)).xorRot32 (by decide) (by decide)).addMul
    (by decide) (by decide)).xorRot24 (by decide) (by decide)).addMul (by decide) (by decide)).xorRot16
    (by decide) (by decide)).addMul (by decide) (by decide)).xorRot63 (by decide) (by decide)

/-- GB on each quadword of `ymm0`–`ymm3`. -/
theorem gb_qw {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {k : Nat} (hk : k < 4) :
    (qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) VG.Proof.Argon2.X86_64.Avx2.x0 k, qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) VG.Proof.Argon2.X86_64.Avx2.x1 k, qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) VG.Proof.Argon2.X86_64.Avx2.x2 k,
      qw (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) VG.Proof.Argon2.X86_64.Avx2.x3 k) = mix (qw s VG.Proof.Argon2.X86_64.Avx2.x0 k) (qw s VG.Proof.Argon2.X86_64.Avx2.x1 k) (qw s VG.Proof.Argon2.X86_64.Avx2.x2 k) (qw s VG.Proof.Argon2.X86_64.Avx2.x3 k) := by
  have m3 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x3) (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x0) (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1) s))) :=
    ((h.addMul (by decide) (by decide)).xorRot32 (by decide) (by decide)).addMul (by decide) (by decide)
  have m5 : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1) (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot24Ops VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x2) (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x3)
      (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.xorRot32Ops VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x0) (VG.Proof.Argon2.X86_64.Avx2.vrun (VG.Proof.Argon2.X86_64.Avx2.addMulOps VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1) s))))) :=
    (m3.xorRot24 (by decide) (by decide)).addMul (by decide) (by decide)
  simp only [VG.Proof.Argon2.X86_64.Avx2.gbOps, VG.Proof.Argon2.X86_64.Avx2.vrun_append]
  simp (disch := decide) only [VG.Proof.Argon2.X86_64.Avx2.addMul_qw (a := VG.Proof.Argon2.X86_64.Avx2.x0) (b := VG.Proof.Argon2.X86_64.Avx2.x1) (by decide) (by decide),
    VG.Proof.Argon2.X86_64.Avx2.addMul_qw (a := VG.Proof.Argon2.X86_64.Avx2.x2) (b := VG.Proof.Argon2.X86_64.Avx2.x3) (by decide) (by decide),
    VG.Proof.Argon2.X86_64.Avx2.xorRot32_qw, VG.Proof.Argon2.X86_64.Avx2.xorRot24_qw (d := VG.Proof.Argon2.X86_64.Avx2.x1) (by decide) _ m3 _ hk,
    VG.Proof.Argon2.X86_64.Avx2.xorRot16_qw (d := VG.Proof.Argon2.X86_64.Avx2.x3) (by decide) _ m5 _ hk, VG.Proof.Argon2.X86_64.Avx2.xorRot63_qw (d := VG.Proof.Argon2.X86_64.Avx2.x1) (by decide),
    ↓reduceIte, reduceCtorEq]
  rfl


/-! ## P -/

def diagOps : List VOp := [.vpermq VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x1 0x39, .vpermq VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x2 0x4e, .vpermq VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x3 0x93]
def undiagOps : List VOp := [.vpermq VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x1 0x93, .vpermq VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x2 0x4e, .vpermq VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x3 0x39]
def roundOps : List VOp := VG.Proof.Argon2.X86_64.Avx2.gbOps ++ VG.Proof.Argon2.X86_64.Avx2.diagOps ++ VG.Proof.Argon2.X86_64.Avx2.gbOps ++ VG.Proof.Argon2.X86_64.Avx2.undiagOps

theorem round_eq : round = roundOps.map .vop := rfl

/-- The sixteen words in `ymm0`–`ymm3`: word `4i + k` is quadword `k` of `vreg i`. -/
def words (s : State) : Vector Word 16 :=
  Vector.ofFn fun j => qw s (vreg (j.val / 4)) (j.val % 4)

theorem words_get (s : State) (j : Nat) (hj : j < 16) :
    (VG.Proof.Argon2.X86_64.Avx2.words s)[j] = qw s (vreg (j / 4)) (j % 4) := by
  simp only [VG.Proof.Argon2.X86_64.Avx2.words, Vector.getElem_ofFn]

theorem cases_div4 {j : Nat} (hj : j < 16) : j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3 := by
  omega

theorem gb_words {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.gbOps s) = mixColumns (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have g := VG.Proof.Argon2.X86_64.Avx2.gb_qw h (k := j % 4) (Nat.mod_lt _ (by decide))
  rw [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj, Proof.Argon2.mixColumns_get _ _ hj, VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega),
    VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega), VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega), VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega),
    show j % 4 / 4 = 0 by omega, show (4 + j % 4) / 4 = 1 by omega, show (8 + j % 4) / 4 = 2 by omega,
    show (12 + j % 4) / 4 = 3 by omega, Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega,
    show (8 + j % 4) % 4 = j % 4 by omega, show (12 + j % 4) % 4 = j % 4 by omega]
  rcases VG.Proof.Argon2.X86_64.Avx2.cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [vreg, mixAt] <;> rw [← g]

theorem masks_diag {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.diagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem masks_undiag {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.undiagOps s) :=
  ((h.vpermq (by decide) (by decide)).vpermq (by decide) (by decide)).vpermq (by decide) (by decide)

theorem diag_words (s : State) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.diagOps s) = rotRows 1 (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 1 * (j / 4)) % 4) % 4 = (j % 4 + j / 4) % 4 by omega]
  simp only [VG.Proof.Argon2.X86_64.Avx2.diagOps, VG.Proof.Argon2.X86_64.Avx2.vrun]
  rcases VG.Proof.Argon2.X86_64.Avx2.cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qw_vpermq, VG.Proof.Argon2.X86_64.Avx2.sel4_39, VG.Proof.Argon2.X86_64.Avx2.sel4_4e, VG.Proof.Argon2.X86_64.Avx2.sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod]

theorem undiag_words (s : State) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.undiagOps s) = rotRows 3 (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj, Proof.Argon2.rotRows_get _ _ _ hj, VG.Proof.Argon2.X86_64.Avx2.words_get _ _ (by omega),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) / 4 = j / 4 by omega,
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4)) % 4) % 4 = (j % 4 + 3 * (j / 4)) % 4 by omega]
  simp only [VG.Proof.Argon2.X86_64.Avx2.undiagOps, VG.Proof.Argon2.X86_64.Avx2.vrun]
  rcases VG.Proof.Argon2.X86_64.Avx2.cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp (disch := omega) only [vreg, qw_vpermq, VG.Proof.Argon2.X86_64.Avx2.sel4_39, VG.Proof.Argon2.X86_64.Avx2.sel4_4e, VG.Proof.Argon2.X86_64.Avx2.sel4_93, ↓reduceIte,
      reduceCtorEq, Nat.add_zero, Nat.mod_mod, Nat.mul_zero, Nat.mul_one] <;> congr 1 <;> omega

theorem round_masks {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.Masks (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.roundOps s) := by
  simp only [VG.Proof.Argon2.X86_64.Avx2.roundOps, VG.Proof.Argon2.X86_64.Avx2.vrun_append]
  exact VG.Proof.Argon2.X86_64.Avx2.masks_undiag (VG.Proof.Argon2.X86_64.Avx2.gb_masks (VG.Proof.Argon2.X86_64.Avx2.masks_diag (VG.Proof.Argon2.X86_64.Avx2.gb_masks h)))

/-- P on the sixteen words of `ymm0`–`ymm3`. -/
theorem round_words {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) : VG.Proof.Argon2.X86_64.Avx2.words (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.roundOps s) = permute (VG.Proof.Argon2.X86_64.Avx2.words s) := by
  simp only [VG.Proof.Argon2.X86_64.Avx2.roundOps, VG.Proof.Argon2.X86_64.Avx2.vrun_append]
  rw [Proof.Argon2.permute_lanes, VG.Proof.Argon2.X86_64.Avx2.undiag_words, VG.Proof.Argon2.X86_64.Avx2.gb_words (VG.Proof.Argon2.X86_64.Avx2.masks_diag (VG.Proof.Argon2.X86_64.Avx2.gb_masks h)), VG.Proof.Argon2.X86_64.Avx2.diag_words,
    VG.Proof.Argon2.X86_64.Avx2.gb_words h]

end VG.Proof.Argon2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows`. -/
section

/-!
# Argon2 on x86-64 with AVX2: rows and columns in scratch

A row of the block P permutes (`working`, `[1024, 2048)` of scratch) is
loaded into `ymm0`–`ymm3` with four 32-byte loads, permuted (`round_words`)
and stored back; a column with two 16-byte loads per register, joined by
`vinserti128`, and two 16-byte stores. Either way the block becomes
`Spec.Argon2.permuteAt` of the row or column (`row_ok`, `col_ok`).
-/

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

theorem VKeep.refl (s : State) : VG.Proof.Argon2.X86_64.Avx2.VKeep s s := ⟨rfl, rfl, rfl, rfl⟩

theorem VKeep.trans {s t u : State} (h : VG.Proof.Argon2.X86_64.Avx2.VKeep s t) (h' : VG.Proof.Argon2.X86_64.Avx2.VKeep t u) : VG.Proof.Argon2.X86_64.Avx2.VKeep s u :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.mxcsr.trans h.mxcsr⟩

theorem _root_.VG.Proof.Argon2.X86_64.Scratch.of_vkeep {s t : State} {p : Addr} (hs : Scratch s p) (h : VG.Proof.Argon2.X86_64.Avx2.VKeep s t) : Scratch t p :=
  ⟨by rw [h.gpr]; exact hs.reg, h.wr ▸ hs.wr⟩

theorem vrun_vkeep (os : List VOp) (s : State) : VG.Proof.Argon2.X86_64.Avx2.VKeep s (VG.Proof.Argon2.X86_64.Avx2.vrun os s) :=
  ⟨VG.Proof.Argon2.X86_64.Avx2.vrun_gpr os s, VG.Proof.Argon2.X86_64.Avx2.vrun_rd os s, VG.Proof.Argon2.X86_64.Avx2.vrun_wr os s, VG.Proof.Argon2.X86_64.Avx2.vrun_mxcsr os s⟩

/-! ## Loads and stores, quadword by quadword -/

theorem qword256_readW (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword256 (m.readW a 256) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword256, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

theorem qword_readW128 (m : Mem) (a : Addr) {k : Nat} (hk : k < 2) :
    qword (m.readW a 128) k = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [qword, show 64 * k = 8 * (8 * k) by omega]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega)

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
      (Offset.add_add_eq p (by omega)).symm
    rw [VG.Proof.Argon2.X86_64.word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 4)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword256, show 8 * (8 * (i.val % 4)) = 64 * (i.val % 4) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- A word of `working` after a 16-byte write to it. -/
theorem working_write128 (m : Mem) (p : Addr) {c : Nat} (hc : c < 64) (v : BitVec 128) (i : Fin 128) :
    (working (m.writeW (off p (1024 + 16 * c)) v) p)[i] =
      if i.val / 2 = c then qword v (i.val % 2) else (working m p)[i] := by
  rw [working_get, working_get]
  split
  · rename_i h
    have e : off p (1024 + 8 * i.val) = off p (1024 + 16 * c) + BitVec.ofNat 64 (8 * (i.val % 2)) :=
      (Offset.add_add_eq p (by omega)).symm
    rw [VG.Proof.Argon2.X86_64.word, e]
    refine (readW_writeW_inside _ _ v (k := 8 * (i.val % 2)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword, show 8 * (8 * (i.val % 2)) = 64 * (i.val % 2) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

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

theorem Masks.setV {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) {len : VLen} {d : XReg} {lo hi : BitVec 128}
    (h14 : d ≠ .xmm14) (h15 : d ≠ .xmm15) : VG.Proof.Argon2.X86_64.Avx2.Masks (s.setV len d lo hi) := by
  intro l hl
  cases len
  · simp only [State.lane_setV128, h14.symm, h15.symm, ite_false]; exact h l hl
  · simp only [State.lane_setV256, h14.symm, h15.symm, ite_false]; exact h l hl

/-! ## Rows -/

theorem loadRow_eq (i : Nat) : loadRow i =
    [.vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x0 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 0)), .vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x1 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 1)),
      .vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x2 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 2)), .vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x3 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 3))] :=
  rfl

theorem storeRow_eq (i : Nat) : storeRow i =
    [.vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 0)) VG.Proof.Argon2.X86_64.Avx2.x0, .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 1)) VG.Proof.Argon2.X86_64.Avx2.x1,
      .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 2)) VG.Proof.Argon2.X86_64.Avx2.x2, .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (rowOff i 3)) VG.Proof.Argon2.X86_64.Avx2.x3] :=
  rfl

theorem loadRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s) :
    WP isa (.block (loadRow i)) s fun t =>
      VG.Proof.Argon2.X86_64.Avx2.words t = gather (rowIndex ⟨i, hi⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ VG.Proof.Argon2.X86_64.Avx2.Masks t := by
  have r (k : Nat) (hk : k < 4) := hs.read (d := rowOff i k) (n := 32) (by unfold rowOff; omega)
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.loadRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, VG.Proof.Argon2.X86_64.ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide),
    r 1 (by decide), r 2 (by decide), r 3 (by decide), ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, ⟨rfl, rfl, rfl, by simp only [State.setV_mxcsr]⟩,
    (((hm.setV (by decide) (by decide)).setV (by decide) (by decide)).setV (by decide)
      (by decide)).setV (by decide) (by decide)⟩
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj, show (gather (rowIndex ⟨i, hi⟩) (working s.mem p))[j] =
      (working s.mem p)[rowIndex ⟨i, hi⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
  rcases VG.Proof.Argon2.X86_64.Avx2.cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [vreg, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hk, ↓reduceIte, reduceCtorEq, VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hk] <;>
    exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by simp only [rowIndex, rowOff]; omega))


theorem ymm_setMem (s : State) (m : Mem) (r : XReg) : (s.setMem m).ymm r = s.ymm r := by
  cases s; rfl

theorem setMem_vkeep (s : State) (m : Mem) : VG.Proof.Argon2.X86_64.Avx2.VKeep s (s.setMem m) := by
  cases s; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Masks.setMem {s : State} (h : VG.Proof.Argon2.X86_64.Avx2.Masks s) (m : Mem) : VG.Proof.Argon2.X86_64.Avx2.Masks (s.setMem m) := by
  intro l hl; simp only [State.setMem_lane]; exact h l hl

theorem qw_setMem (s : State) (m : Mem) (r : XReg) (k : Nat) : qw (s.setMem m) r k = qw s r k := by
  simp only [qw, State.setMem_lane]

/-- The region of `working` contains a write at `1024 + d`. -/
theorem working_contains (p : Addr) {d n : Nat} (h : d + n ≤ 1024) :
    (⟨off p 1024, 1024⟩ : Region).Contains (off p (1024 + d)) n :=
  Offset.contains p (by omega) (by omega) (by omega)

theorem storeRow_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeRow i)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val / 16 = i then qw s (vreg (w.val % 16 / 4)) (w.val % 4) else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ VG.Proof.Argon2.X86_64.Avx2.words t = VG.Proof.Argon2.X86_64.Avx2.words s ∧
      (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  have w (k : Nat) (hk : k < 4) := hs.write (d := rowOff i k) (n := 32) (by unfold rowOff; omega)
  have o (k : Nat) : rowOff i k = 1024 + 32 * (4 * i + k) := by unfold rowOff; omega
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.storeRow_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, VG.Proof.Argon2.X86_64.ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, VG.Proof.Argon2.X86_64.Avx2.ymm_setMem, hs.reg, w 0 (by decide),
    w 1 (by decide), w 2 (by decide), w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left']
  simp only [o]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ((((h.setMem _).setMem _).setMem _).setMem _)⟩
  · have hx := x.isLt
    simp only [VG.Proof.Argon2.X86_64.Avx2.working_write256 _ p (show 4 * i + 3 < 32 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write256 _ p (show 4 * i + 2 < 32 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write256 _ p (show 4 * i + 1 < 32 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write256 _ p (show 4 * i + 0 < 32 by omega)]
    have hq : x.val % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases h : x.val / 16 = i
    · have : x.val % 16 / 4 = 0 ∨ x.val % 16 / 4 = 1 ∨ x.val % 16 / 4 = 2 ∨ x.val % 16 / 4 = 3 := by
        omega
      rcases this with e | e | e | e <;>
        simp only [h, ite_true, e, vreg, show x.val / 4 = 4 * i + x.val % 16 / 4 by omega,
          qword256_ymm _ _ hq] <;> simp
    · simp only [h, ite_false, show x.val / 4 ≠ 4 * i + 3 by omega, show x.val / 4 ≠ 4 * i + 2 by omega,
        show x.val / 4 ≠ 4 * i + 1 by omega, show x.val / 4 ≠ 4 * i + 0 by omega]
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.working_contains p (by omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.working_contains p (by omega))
  · exact ((((VG.Proof.Argon2.X86_64.Avx2.setMem_vkeep _ _).trans (VG.Proof.Argon2.X86_64.Avx2.setMem_vkeep _ _)).trans (VG.Proof.Argon2.X86_64.Avx2.setMem_vkeep _ _)).trans
      (VG.Proof.Argon2.X86_64.Avx2.setMem_vkeep _ _))
  · apply Vector.ext; intro j hj
    simp only [VG.Proof.Argon2.X86_64.Avx2.words_get, VG.Proof.Argon2.X86_64.Avx2.qw_setMem]


/-- What a row or column step leaves. -/
structure Permuted (index : Fin 16 → Fin 128) (p : Addr) (s t : State) : Prop where
  working : working t.mem p = Spec.Argon2.permuteAt index (working s.mem p)
  frame : Frame [⟨off p 1024, 1024⟩] s.mem t.mem
  keep : VG.Proof.Argon2.X86_64.Avx2.VKeep s t
  masks : VG.Proof.Argon2.X86_64.Avx2.Masks t

/-- The round, as a block, from the state the loads leave. -/
theorem round_then {s : State} {Q : State → Prop} (h : Q (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.roundOps s)) :
    WP isa (.block round) s Q := by
  rw [VG.Proof.Argon2.X86_64.Avx2.round_eq]
  exact WP.of_runBlock ⟨_, VG.Proof.Argon2.X86_64.Avx2.runBlock_vops _ _, h⟩

/-- P on row `i`. -/
theorem row_ok {i : Nat} (hi : i < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s) :
    WP isa (row i) s (VG.Proof.Argon2.X86_64.Avx2.Permuted (rowIndex ⟨i, hi⟩) p s) := by
  unfold row
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx2.loadRow_ok hi hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine VG.Proof.Argon2.X86_64.Avx2.round_then ?_
  have hs2 : Scratch (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (VG.Proof.Argon2.X86_64.Avx2.vrun_vkeep _ _)
  refine (VG.Proof.Argon2.X86_64.Avx2.storeRow_ok hi hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := VG.Proof.Argon2.X86_64.Avx2.round_words hm1
  rw [VG.Proof.Argon2.X86_64.Avx2.vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((VG.Proof.Argon2.X86_64.Avx2.vrun_vkeep _ _).trans hk), hmt (VG.Proof.Argon2.X86_64.Avx2.round_masks hm1)⟩
  apply VG.Proof.Argon2.X86_64.Avx2.permuteAt_of _ (rowIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [rowIndex]; omega)), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj] at e
    simp only [rowIndex, show (16 * i + j.val) % 16 = j.val by omega,
      show (16 * i + j.val) % 4 = j.val % 4 by omega, e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨k.val % 16, by omega⟩ (Fin.ext (by simp only [rowIndex]; omega)))]


/-! ## Columns -/

theorem xmm_eq_lane (s : State) (r : XReg) : s.xmm r = s.lane r 0 := rfl

theorem loadCol_eq (j : Nat) : loadCol j = [
    .vmovdquLoad .l128 VG.Proof.Argon2.X86_64.Avx2.x0 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 0 false)), .vmovdquLoad .l128 .xmm4 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 0 true)),
    .vop (.vinserti128 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x0 .xmm4 1),
    .vmovdquLoad .l128 VG.Proof.Argon2.X86_64.Avx2.x1 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 1 false)), .vmovdquLoad .l128 .xmm4 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 1 true)),
    .vop (.vinserti128 VG.Proof.Argon2.X86_64.Avx2.x1 VG.Proof.Argon2.X86_64.Avx2.x1 .xmm4 1),
    .vmovdquLoad .l128 VG.Proof.Argon2.X86_64.Avx2.x2 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 2 false)), .vmovdquLoad .l128 .xmm4 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 2 true)),
    .vop (.vinserti128 VG.Proof.Argon2.X86_64.Avx2.x2 VG.Proof.Argon2.X86_64.Avx2.x2 .xmm4 1),
    .vmovdquLoad .l128 VG.Proof.Argon2.X86_64.Avx2.x3 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 3 false)), .vmovdquLoad .l128 .xmm4 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 3 true)),
    .vop (.vinserti128 VG.Proof.Argon2.X86_64.Avx2.x3 VG.Proof.Argon2.X86_64.Avx2.x3 .xmm4 1)] := rfl

theorem storeCol_eq (j : Nat) : storeCol j = [
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 0 false)) VG.Proof.Argon2.X86_64.Avx2.x0, .vop (.vextracti128 .xmm4 VG.Proof.Argon2.X86_64.Avx2.x0 1),
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 0 true)) .xmm4,
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 1 false)) VG.Proof.Argon2.X86_64.Avx2.x1, .vop (.vextracti128 .xmm4 VG.Proof.Argon2.X86_64.Avx2.x1 1),
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 1 true)) .xmm4,
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 2 false)) VG.Proof.Argon2.X86_64.Avx2.x2, .vop (.vextracti128 .xmm4 VG.Proof.Argon2.X86_64.Avx2.x2 1),
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 2 true)) .xmm4,
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 3 false)) VG.Proof.Argon2.X86_64.Avx2.x3, .vop (.vextracti128 .xmm4 VG.Proof.Argon2.X86_64.Avx2.x3 1),
    .vmovdquStore .l128 (VG.Impl.Argon2.X86_64.at_ .rcx (colOff j 3 true)) .xmm4] := rfl

theorem vinserti128_1 (s : State) (d a b : XReg) :
    (VOp.vinserti128 d a b 1).exec s = s.setV .l256 d (s.lane a 0) (s.xmm b) := rfl

theorem vextracti128_1 (s : State) (d a : XReg) :
    (VOp.vextracti128 d a 1).exec s = s.setV .l128 d (s.lane a 1) 0 := rfl

theorem colOff_eq (j k : Nat) (hi : Bool) :
    colOff j k hi = 1024 + 16 * (16 * k + j + if hi then 8 else 0) := by
  unfold colOff; cases hi <;> simp <;> omega

theorem loadCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s) :
    WP isa (.block (loadCol c)) s fun t =>
      VG.Proof.Argon2.X86_64.Avx2.words t = gather (colIndex ⟨c, hc⟩) (working s.mem p) ∧ t.mem = s.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ VG.Proof.Argon2.X86_64.Avx2.Masks t := by
  have r (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.read (d := colOff c k hi) (n := 16) (by rw [VG.Proof.Argon2.X86_64.Avx2.colOff_eq]; cases hi <;> simp <;> omega)
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.loadCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, VG.Proof.Argon2.X86_64.ea_at,
    State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, hs.reg, r 0 (by decide), r 1 (by decide), r 2 (by decide),
    r 3 (by decide), ite_true, Option.map_some, Option.some.injEq, exists_eq_left', VG.Proof.Argon2.X86_64.Avx2.vinserti128_1]
  refine ⟨?_, trivial, ⟨by simp only [State.setV_gpr], by simp only [State.setV_rd],
    by simp only [State.setV_wr], by simp only [State.setV_mxcsr]⟩, ?_⟩
  · apply Vector.ext
    intro j hj
    have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj, show (gather (colIndex ⟨c, hc⟩) (working s.mem p))[j] =
        (working s.mem p)[colIndex ⟨c, hc⟩ ⟨j, hj⟩] from gather_get _ _ ⟨j, hj⟩, working_get]
    have h2 : j % 4 / 2 = 0 ∨ j % 4 / 2 = 1 := by omega
    rcases VG.Proof.Argon2.X86_64.Avx2.cases_div4 hj with e | e | e | e <;> rw [e] <;> rcases h2 with h | h <;>
      simp only [vreg, qw, State.lane_setV256, State.lane_setV128, VG.Proof.Argon2.X86_64.Avx2.xmm_eq_lane, h, ↓reduceIte,
        reduceCtorEq, VG.Proof.Argon2.X86_64.Avx2.qword_readW128 _ _ (Nat.mod_lt _ (by decide) : j % 4 % 2 < 2)]
    all_goals exact congrArg (Mem.readW _ · 64) (Offset.add_add_eq _ (by
      simp only [colIndex, colOff, Bool.false_eq_true, ite_true, ite_false]; omega))
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
  rw [h1, h2, qw, show (2 * b + x % 2) / 2 = b by omega, show (2 * b + x % 2) % 2 = x % 2 by omega]

/-- Whether word `8 q + r` of the block is in row `2 k` of column `c`. -/
theorem col_cond (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c) = (q = 2 * k ∧ r = c) := by
  apply propext; omega

/-- Whether word `8 q + r` of the block is in row `2 k + 1` of column `c`. -/
theorem col_cond8 (q r k c : Nat) (hr : r < 8) (hc : c < 8) :
    (8 * q + r = 16 * k + c + 8) = (q = 2 * k + 1 ∧ r = c) := by
  apply propext; omega

theorem storeCol_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block (storeCol c)) s fun t =>
      (∀ w : Fin 128, (working t.mem p)[w] =
        if w.val % 16 / 2 = c then qw s (vreg (w.val / 32)) (2 * (w.val / 16 % 2) + w.val % 2)
        else (working s.mem p)[w]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ VG.Proof.Argon2.X86_64.Avx2.words t = VG.Proof.Argon2.X86_64.Avx2.words s ∧
      (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  have w (k : Nat) (hk : k < 4) (hi : Bool) :=
    hs.write (d := colOff c k hi) (n := 16) (by rw [VG.Proof.Argon2.X86_64.Avx2.colOff_eq]; cases hi <;> simp <;> omega)
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.storeCol_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128_eq, VG.Proof.Argon2.X86_64.ea_at,
    State.setMem_wr, State.setMem_gpr, State.setMem_mem, State.setV_wr, State.setV_gpr,
    State.setV_mem, State.setMem_xmm, hs.reg, w 0 (by decide), w 1 (by decide), w 2 (by decide),
    w 3 (by decide), ite_true, Option.some.injEq, exists_eq_left', VG.Proof.Argon2.X86_64.Avx2.vextracti128_1]
  simp only [VG.Proof.Argon2.X86_64.Avx2.colOff_eq, Bool.false_eq_true, Nat.add_zero, VG.Proof.Argon2.X86_64.Avx2.xmm_eq_lane,
    State.setMem_lane, State.lane_setV128, ↓reduceIte, reduceCtorEq]
  refine ⟨fun x => ?_, ?_, ?_, ?_, fun h => ?_⟩
  · have hx := x.isLt
    rw [VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 3 + c + 8 < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 3 + c < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 2 + c + 8 < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 2 + c < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 1 + c + 8 < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 1 + c < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 0 + c + 8 < 64 by omega),
      VG.Proof.Argon2.X86_64.Avx2.working_write128 _ p (show 16 * 0 + c < 64 by omega)]
    obtain ⟨q, hq16⟩ : ∃ q, x.val / 16 = q := ⟨_, rfl⟩
    have hr : x.val % 16 / 2 < 8 := by omega
    rw [show x.val / 2 = 8 * q + x.val % 16 / 2 by omega]
    simp only [VG.Proof.Argon2.X86_64.Avx2.col_cond _ _ _ _ hr hc, VG.Proof.Argon2.X86_64.Avx2.col_cond8 _ _ _ _ hr hc]
    by_cases h : x.val % 16 / 2 = c
    · simp only [h, and_true, ↓reduceIte]
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 0) (b := 0) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 0) (b := 1) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 1) (b := 0) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 1) (b := 1) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 2) (b := 0) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 2) (b := 1) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 3) (b := 0) (by omega) (by omega)
      · exact VG.Proof.Argon2.X86_64.Avx2.qw_col s (k := 3) (b := 1) (by omega) (by omega)
    · simp only [h, and_false, ↓reduceIte]
  · repeat (first
      | refine Frame.writeW ?_ (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.working_contains p (by omega))
      | exact Frame.refl _ _)
  · exact ⟨by simp only [State.setMem_gpr, State.setV_gpr], by simp only [State.setMem_rd, State.setV_rd],
      by simp only [State.setMem_wr, State.setV_wr], by simp only [State.setMem_mxcsr, State.setV_mxcsr]⟩
  · apply Vector.ext; intro j hj
    simp only [VG.Proof.Argon2.X86_64.Avx2.words_get, VG.Proof.Argon2.X86_64.Avx2.qw_setMem, qw_setV128, VG.Proof.Argon2.X86_64.Avx2.vreg_ne4, ite_false]
  · exact ((((((((((((h.setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _).setMem _).setV (by decide) (by decide)).setMem _)


/-- P on column `c`. -/
theorem col_ok {c : Nat} (hc : c < 8) {s : State} {p : Addr} (hs : Scratch s p) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s) :
    WP isa (col c) s (VG.Proof.Argon2.X86_64.Avx2.Permuted (colIndex ⟨c, hc⟩) p s) := by
  unfold col
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx2.loadCol_ok hc hs hm).mono ?_
  rintro t1 ⟨hw1, hmem1, hk1, hm1⟩
  refine VG.Proof.Argon2.X86_64.Avx2.round_then ?_
  have hs2 : Scratch (VG.Proof.Argon2.X86_64.Avx2.vrun VG.Proof.Argon2.X86_64.Avx2.roundOps t1) p := (hs.of_vkeep hk1).of_vkeep (VG.Proof.Argon2.X86_64.Avx2.vrun_vkeep _ _)
  refine (VG.Proof.Argon2.X86_64.Avx2.storeCol_ok hc hs2).mono ?_
  rintro t ⟨hw, hf, hk, -, hmt⟩
  have hr := VG.Proof.Argon2.X86_64.Avx2.round_words hm1
  rw [VG.Proof.Argon2.X86_64.Avx2.vrun_mem, hmem1] at hw hf
  refine ⟨?_, hf, hk1.trans ((VG.Proof.Argon2.X86_64.Avx2.vrun_vkeep _ _).trans hk), hmt (VG.Proof.Argon2.X86_64.Avx2.round_masks hm1)⟩
  apply VG.Proof.Argon2.X86_64.Avx2.permuteAt_of _ (colIndex_injective _)
  · intro j
    have hj := j.isLt
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [colIndex]; omega)), ← hw1]
    have e := congrArg (fun v : Vector Word 16 => v[j.val]) hr
    simp only [VG.Proof.Argon2.X86_64.Avx2.words_get _ _ hj] at e
    simp only [colIndex, show (16 * (j.val / 2) + 2 * c + j.val % 2) / 32 = j.val / 4 by omega,
      show 2 * ((16 * (j.val / 2) + 2 * c + j.val % 2) / 16 % 2) + (16 * (j.val / 2) + 2 * c +
        j.val % 2) % 2 = j.val % 4 by omega, e]
    rfl
  · intro k hk
    rw [hw, ite_eq_right_of_eq_false _ _ (eq_false fun h =>
      hk ⟨4 * (k.val / 32) + 2 * (k.val / 16 % 2) + k.val % 2, by omega⟩
        (Fin.ext (by simp only [colIndex]; omega)))]

end VG.Proof.Argon2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Ends`. -/
section

/-!
# Argon2 on x86-64 with AVX2: the first and last XOR

`initChunk k` copies 32 bytes of X XOR Y to both halves of scratch, and
`finishChunk k` writes 32 bytes of the permuted block XOR R to `out`; each
is proven for any prefix of the 32 chunks (`init_prefix`, `finish_prefix`).
-/

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at Inputs blockAt_get
  xorBlock_get input_read input_unchanged Written scratch_unchanged)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword256_ymm qw_vbin qw_lane)

/-- A word at `p + d` after 32 bytes are written at `p + e`. -/
theorem read_write256 (m : Mem) (p : Addr) {d e : Nat} (hd : d + 8 ≤ 4096) (he : e + 32 ≤ 4096)
    (h8 : d % 8 = 0) (he8 : e % 8 = 0) (v : BitVec 256) :
    (m.writeW (off p e) v).readW (off p d) 64 =
      if e ≤ d ∧ d < e + 32 then qword256 v ((d - e) / 8) else m.readW (off p d) 64 := by
  split
  · rename_i h
    rw [show off p d = off p e + BitVec.ofNat 64 (8 * ((d - e) / 8)) from
      (Offset.add_add_eq p (by omega)).symm]
    refine (readW_writeW_inside _ _ v (k := 8 * ((d - e) / 8)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword256, show 8 * (8 * ((d - e) / 8)) = 64 * ((d - e) / 8) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- The chunks `k < n` of both halves of scratch hold `r`. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val / 4 < n → m.readW (off p (8 * i.val)) 64 = r[i] ∧ VG.Proof.Argon2.X86_64.word m p i.val = r[i]

theorem qw_xor_ymm (s : State) (k : Nat) (hk : k < 4) :
    qword256 (((VOp.vbin .vpxor .l256 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1).exec s).ymm VG.Proof.Argon2.X86_64.Avx2.x0) k = qw s VG.Proof.Argon2.X86_64.Avx2.x0 k ^^^ qw s VG.Proof.Argon2.X86_64.Avx2.x1 k := by
  rw [qword256_ymm _ _ hk]
  simp only [qw_vbin, VBinOp.sse, ite_true, VG.Proof.Argon2.X86_64.Avx2.qword_pxor, qw_lane]


theorem initChunk_eq (k : Nat) : initChunk k =
    [.vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x0 (VG.Impl.Argon2.X86_64.at_ .rdi (32 * k)), .vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x1 (VG.Impl.Argon2.X86_64.at_ .rsi (32 * k)),
      .vop (.vbin .vpxor .l256 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1), .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (32 * k)) VG.Proof.Argon2.X86_64.Avx2.x0,
      .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 32 * k)) VG.Proof.Argon2.X86_64.Avx2.x0] := rfl

/-- The 32 bytes `initChunk k` writes, quadword by quadword. -/
def XorChunk (s : State) (x y : Addr) (k : Nat) (v : BitVec 256) : Prop :=
  ∀ q < 4, qword256 v q = s.mem.readW (off x (32 * k + 8 * q)) 64 ^^^ s.mem.readW (off y (32 * k + 8 * q)) 64

theorem initChunk_ok {k : Nat} (hk : k < 32) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block (initChunk k)) s fun t => ∃ v, VG.Proof.Argon2.X86_64.Avx2.XorChunk s x y k v ∧
      t.mem = (s.mem.writeW (off p (32 * k)) v).writeW (off p (1024 + 32 * k)) v ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧
      (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  have lx : InRegions (s.rd ++ s.wr) (off x (32 * k)) 32 :=
    ⟨_, hin.xread, Offset.contains_base x (by omega) (by omega)⟩
  have ly : InRegions (s.rd ++ s.wr) (off y (32 * k)) 32 :=
    ⟨_, hin.yread, Offset.contains_base y (by omega) (by omega)⟩
  have w1 := hs.write (d := 32 * k) (n := 32) (by omega)
  have w2 := hs.write (d := 1024 + 32 * k) (n := 32) (by omega)
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.initChunk_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, VG.Proof.Argon2.X86_64.ea_at, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem,
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_wr, State.setMem_wr, State.setMem_gpr,
    VG.Proof.Argon2.X86_64.Avx2.ymm_setMem, hs.reg, hin.xreg, hin.yreg, lx, ly, w1, w2, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ?_, fun h => ?_⟩
  · simp only [VG.Proof.Argon2.X86_64.Avx2.qw_xor_ymm _ _ hq, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ↓reduceIte, reduceCtorEq,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add]
  · exact ⟨by simp only [State.setMem_gpr, VOp.exec_gpr, State.setV_gpr],
      by simp only [State.setMem_rd, VOp.exec_rd, State.setV_rd],
      by simp only [State.setMem_wr, VOp.exec_wr, State.setV_wr],
      by simp only [State.setMem_mxcsr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, State.setV_mxcsr]⟩
  · exact ((((h.setV (by decide) (by decide)).setV (by decide) (by decide)).vbin (by decide)
      (by decide)).setMem _).setMem _


theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat} (hn : n < 32)
    (h : VG.Proof.Argon2.X86_64.Avx2.Initialized m p r n) {v : BitVec 256} (hv : ∀ q < 4, ∀ hi : 4 * n + q < 128,
      qword256 v q = r[4 * n + q]'hi) :
    VG.Proof.Argon2.X86_64.Avx2.Initialized ((m.writeW (off p (32 * n)) v).writeW (off p (1024 + 32 * n)) v) p r (n + 1) := by
  intro i hi
  have hi' := i.isLt
  simp only [VG.Proof.Argon2.X86_64.word]
  rw [VG.Proof.Argon2.X86_64.Avx2.read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    VG.Proof.Argon2.X86_64.Avx2.read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    VG.Proof.Argon2.X86_64.Avx2.read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    VG.Proof.Argon2.X86_64.Avx2.read_write256 _ p (by omega) (by omega) (by omega) (by omega)]
  by_cases e : i.val / 4 = n
  · have q := hv (i.val % 4) (Nat.mod_lt _ (by decide)) (by omega)
    simp only [show 4 * n + i.val % 4 = i.val by omega] at q
    simp (disch := omega) only [VG.Proof.Argon2.X86_64.Avx2.ifp, VG.Proof.Argon2.X86_64.Avx2.ifn, Fin.getElem_fin,
      show (8 * i.val - 32 * n) / 8 = i.val % 4 by omega,
      show (1024 + 8 * i.val - (1024 + 32 * n)) / 8 = i.val % 4 by omega, q, and_self]
  · have := h i (by omega)
    simp (disch := omega) only [VG.Proof.Argon2.X86_64.Avx2.ifn]
    exact this

theorem _root_.VG.Proof.Argon2.X86_64.Inputs.of_vkeep {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : VG.Proof.Argon2.X86_64.Avx2.VKeep s t) :
    Inputs t x y p :=
  ⟨by rw [hk.gpr]; exact h.xreg, by rw [hk.gpr]; exact h.yreg, by rw [hk.rd, hk.wr]; exact h.xread,
    by rw [hk.rd, hk.wr]; exact h.yread, h.xsep, h.ysep⟩

/-- Initialize the first `n` chunks, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 32) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initChunk)) s fun t =>
      VG.Proof.Argon2.X86_64.Avx2.Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, VKeep.refl s, id⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk, hm⟩
    refine (VG.Proof.Argon2.X86_64.Avx2.initChunk_ok (by omega) (hs.of_vkeep hk) (hin.of_vkeep hk)).mono ?_
    rintro u ⟨v, hv, hmem, hk', hm'⟩
    refine ⟨?_, ?_, hk.trans hk', fun h => hm' (hm h)⟩
    · rw [hmem]
      refine VG.Proof.Argon2.X86_64.Avx2.initialized_step (by omega) ht fun q hq hi => ?_
      rw [hv q hq, show 32 * n + 8 * q = 8 * (4 * n + q) by omega,
        input_unchanged hf hin.xsep ⟨4 * n + q, hi⟩, input_unchanged hf hin.ysep ⟨4 * n + q, hi⟩]
      simp only [xorBlock, Vector.getElem_zipWith, blockAt, Vector.getElem_ofFn]
      rfl
    · rw [hmem]
      exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))


theorem finishChunk_eq (k : Nat) : finishChunk k =
    [.vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x0 (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 32 * k)), .vmovdquLoad .l256 VG.Proof.Argon2.X86_64.Avx2.x1 (VG.Impl.Argon2.X86_64.at_ .rcx (32 * k)),
      .vop (.vbin .vpxor .l256 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x0 VG.Proof.Argon2.X86_64.Avx2.x1), .vmovdquStore .l256 (VG.Impl.Argon2.X86_64.at_ .rdx (32 * k)) VG.Proof.Argon2.X86_64.Avx2.x0] := rfl

theorem finishChunk_ok {k : Nat} (hk : k < 32) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finishChunk k)) s fun t => ∃ v : BitVec 256,
      (∀ q < 4, qword256 v q = VG.Proof.Argon2.X86_64.word s.mem p (4 * k + q) ^^^ s.mem.readW (off p (8 * (4 * k + q))) 64) ∧
      t.mem = s.mem.writeW (off out (32 * k)) v ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  have r1 := hs.read (d := 1024 + 32 * k) (n := 32) (by omega)
  have r2 := hs.read (d := 32 * k) (n := 32) (by omega)
  have w : InRegions s.wr (off out (32 * k)) 32 := ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.finishChunk_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, VG.Proof.Argon2.X86_64.ea_at, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem,
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_wr, hs.reg, ho, r1, r2, w, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ?_, fun h => ?_⟩
  · simp only [VG.Proof.Argon2.X86_64.Avx2.qw_xor_ymm _ _ hq, VG.Proof.Argon2.X86_64.Avx2.qw_set256 _ _ _ _ hq, ↓reduceIte, reduceCtorEq,
      VG.Proof.Argon2.X86_64.Avx2.qword256_readW _ _ hq, Offset.add_add, VG.Proof.Argon2.X86_64.word]
    rw [show 1024 + 32 * k + 8 * q = 1024 + 8 * (4 * k + q) by omega,
      show 32 * k + 8 * q = 8 * (4 * k + q) by omega]
  · exact ⟨by simp only [State.setMem_gpr, VOp.exec_gpr, State.setV_gpr],
      by simp only [State.setMem_rd, VOp.exec_rd, State.setV_rd],
      by simp only [State.setMem_wr, VOp.exec_wr, State.setV_wr],
      by simp only [State.setMem_mxcsr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, State.setV_mxcsr]⟩
  · exact (((h.setV (by decide) (by decide)).setV (by decide) (by decide)).vbin (by decide)
      (by decide)).setMem _

/-- Finish the first `n` chunks, preserving scratch. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 32) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap finishChunk)) s fun t =>
      (∀ i : Fin 128, i.val / 4 < n →
        t.mem.readW (off out (8 * i.val)) 64 = (xorBlock (working s.mem p) (blockAt s.mem p))[i]) ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ (VG.Proof.Argon2.X86_64.Avx2.Masks s → VG.Proof.Argon2.X86_64.Avx2.Masks t) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, VKeep.refl s, id⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk, hm⟩
    refine (VG.Proof.Argon2.X86_64.Avx2.finishChunk_ok (out := out) (by omega) (hs.of_vkeep hk) (by rw [hk.gpr]; exact ho)
      (by rw [hk.wr]; exact hw)).mono ?_
    rintro u ⟨v, hv, hmem, hk', hm'⟩
    refine ⟨fun i hi => ?_, ?_, hk.trans hk', fun h => hm' (hm h)⟩
    · have hi' := i.isLt
      rw [hmem, VG.Proof.Argon2.X86_64.Avx2.read_write256 _ out (by omega) (by omega) (by omega) (by omega)]
      by_cases e : i.val / 4 = n
      · rw [VG.Proof.Argon2.X86_64.Avx2.ifp (by omega), show (8 * i.val - 32 * n) / 8 = i.val % 4 by omega,
          hv _ (Nat.mod_lt _ (by decide)), show 4 * n + i.val % 4 = i.val by omega, VG.Proof.Argon2.X86_64.word,
          scratch_unchanged hf hd (d := 1024 + 8 * i.val) (by omega),
          scratch_unchanged hf hd (d := 8 * i.val) (by omega), xorBlock_get, working_get, blockAt_get]
      · rw [VG.Proof.Argon2.X86_64.Avx2.ifn (by omega)]
        exact ht i (by omega)
    · rw [hmem]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))

end VG.Proof.Argon2.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Lit`. -/
section

/-! # Argon2 compression with AVX2 as a checked instruction literal -/

namespace VG

materialize_code Impl.Argon2.X86_64.Avx2.compress

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress`. -/
section

/-!
# Verified Argon2 block compression on x86-64 with AVX2

`vg_argon2_compress_avx2` meets `compressContract`, as `vg_argon2_compress`
does: the masks, the initial XOR (`init_prefix`), the eight rows and eight
columns (`row_ok`, `col_ok`) and the final XOR (`finish_prefix`) compose to
`Spec.Argon2.compress`, between Intel's MXCSR prologue and epilogue, which
keep MXCSR's control bits (`ctlOk`). Constant time is checked by evaluation,
as for the scalar code.
-/

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at Inputs blockAt_get
  xorBlock_get compressLocal initial_agree initialTaint compress_implies original_preserved
  round_frame)
open VG.Proof.Argon2 (rowIndex_injective colIndex_injective)
open VG.Proof.Poly1305.X86_64.Avx2 (qword256_perm sel4 qword_app0 qword_app1)

/-! ## The masks -/

theorem eq_of_qwords {a b : BitVec 128} (h0 : qword a 0 = qword b 0) (h1 : qword a 1 = qword b 1) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < 64
  · have := congrArg (·.getLsbD i) h0
    simpa [qword, h] using this
  · have := congrArg (·.getLsbD (i - 64)) h1
    simp [qword, show i - 64 < 64 by omega] at this
    rwa [show 64 + (i - 64) = i by omega] at this

theorem qword_ext (Y : BitVec 256) (k : Nat) {i : Nat} (hi : i < 2) :
    qword (Y.extractLsb' (128 * k) 128) i = qword256 Y (2 * k + i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * i + j < 128 by omega)]
  congr 1; omega

theorem qword256_lo (z : BitVec 128) {i : Nat} (hi : i < 2) : qword256 (0#128 ++ z) i = qword z i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, qword256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    BitVec.getLsbD_append, show 64 * i + j < 128 by omega, ite_true]

theorem ext_zero_app (x : BitVec 64) : BitVec.extractLsb' 0 64 (0#64 ++ x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
    Nat.zero_add, ite_true]

theorem perm44 (lo hi : BitVec 64) {k : Nat} (hk : k < 2) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' (128 * k) 128 = hi ++ lo := by
  have e : ∀ i < 2, sel4 (0x44 : BitVec 8).toNat (2 * k + i) = i := by
    intro i hi; rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  apply VG.Proof.Argon2.X86_64.Avx2.eq_of_qwords
  · rw [VG.Proof.Argon2.X86_64.Avx2.qword_ext _ _ (by decide), qword256_perm _ _ (by omega), e 0 (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qword256_lo _ (by decide)]
    simp only [qword_app0, VG.Proof.Argon2.X86_64.Avx2.ext_zero_app]
  · rw [VG.Proof.Argon2.X86_64.Avx2.qword_ext _ _ (by decide), qword256_perm _ _ (by omega), e 1 (by decide),
      VG.Proof.Argon2.X86_64.Avx2.qword256_lo _ (by decide)]
    simp only [qword_app1, VG.Proof.Argon2.X86_64.Avx2.ext_zero_app]

theorem perm44_0 (lo hi : BitVec 64) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' 0 128 = hi ++ lo :=
  VG.Proof.Argon2.X86_64.Avx2.perm44 lo hi (k := 0) (by decide)

theorem perm44_1 (lo hi : BitVec 64) :
    (permQwords (0#128 ++ (BitVec.extractLsb' 0 64 (0#64 ++ hi) ++ BitVec.extractLsb' 0 64 (0#64 ++ lo))) 0x44).extractLsb' 128 128 = hi ++ lo :=
  VG.Proof.Argon2.X86_64.Avx2.perm44 lo hi (k := 1) (by decide)


theorem lane_setReg (s : State) (r : Reg) (v : BitVec 64) (x : XReg) (l : Nat) :
    (s.setReg r v).lane x l = s.lane x l := rfl

theorem mask_eq (d : XReg) (lo hi : BitVec 64) : mask d lo hi =
    [.movImm64 .rax lo, .vop (.vmovq d .rax), .movImm64 .rax hi, .vop (.vmovq .xmm13 .rax),
      .vop (.vbin .vpunpcklqdq .l128 d d .xmm13), .vop (.vpermq d d 0x44)] := rfl

theorem mask_ok {d : XReg} (hd : d ≠ .xmm13) (lo hi : BitVec 64) (s : State) :
    WP isa (.block (mask d lo hi)) s fun t => (∀ l < 2, t.lane d l = hi ++ lo) ∧
      (∀ x, x ≠ d → x ≠ .xmm13 → ∀ l, t.lane x l = s.lane x l) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [VG.Proof.Argon2.X86_64.Avx2.mask_eq, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l hl => ?_, fun x h1 h2 l => ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp only [VOp.exec, State.lane_setV256, State.lane_setV128, State.ymm_eq, RegUpd.gpr_setReg,
        VG.Proof.Argon2.X86_64.Avx2.lane_setReg, hd, ↓reduceIte, reduceCtorEq, VBinOp.sse, XBinOp.eval, qword]
    · exact VG.Proof.Argon2.X86_64.Avx2.perm44_0 lo hi
    · exact VG.Proof.Argon2.X86_64.Avx2.perm44_1 lo hi
  · simp only [VOp.exec, State.lane_setV256, State.lane_setV128, VG.Proof.Argon2.X86_64.Avx2.lane_setReg, h1, h2, ite_false]
  · simp only [VOp.exec_mem, RegUpd.mem_setReg]
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [VOp.exec_rd, RegUpd.rd_setReg]
  · simp only [VOp.exec_wr, RegUpd.wr_setReg]
  · simp only [VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, RegUpd.mxcsr_setReg]

theorem masks_ok (s : State) :
    WP isa (.block masks) s fun t => VG.Proof.Argon2.X86_64.Avx2.Masks t ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold masks
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx2.mask_ok (d := .xmm14) (by decide) rot24Lo rot24Hi s).mono ?_
  rintro t ⟨l1, -, m1, g1, r1, w1, x1⟩
  refine (VG.Proof.Argon2.X86_64.Avx2.mask_ok (d := .xmm15) (by decide) rot16Lo rot16Hi t).mono ?_
  rintro u ⟨l2, o2, m2, g2, r2, w2, x2⟩
  refine ⟨fun l hl => ⟨?_, ?_⟩, m2.trans m1, fun r hr => (g2 r hr).trans (g1 r hr), r2.trans r1,
    w2.trans w1, x2.trans x1⟩
  · rw [o2 _ (by decide) (by decide), l1 l hl]; decide
  · rw [l2 l hl]; decide

/-! ## The rows and the columns -/

theorem fold_ok {p : Addr} (index : Fin 8 → Fin 16 → Fin 128) (code : Fin 8 → Prog isa)
    (hcode : ∀ i (s : State), Scratch s p → VG.Proof.Argon2.X86_64.Avx2.Masks s → WP isa (code i) s (VG.Proof.Argon2.X86_64.Avx2.Permuted (index i) p s))
    (is : List (Fin 8)) (s : State) (hs : Scratch s p) (hm : VG.Proof.Argon2.X86_64.Avx2.Masks s) :
    WP isa (is.foldr (fun i rest => .seq (code i) rest) (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Avx2.VKeep s t ∧ VG.Proof.Argon2.X86_64.Avx2.Masks t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, VKeep.refl s, hm⟩
  | cons i is ih =>
    apply WP.seq
    refine (hcode i s hs hm).mono ?_
    rintro t ⟨hw, hf, hk, hmt⟩
    refine (ih t (hs.of_vkeep hk) hmt).mono ?_
    rintro u ⟨hu, hf', hk', hm'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk', hm'⟩
    simpa only [List.foldl_cons, hw] using hu

theorem rows_eq : rows = (List.finRange 8).foldr (fun i rest => .seq (row i.val) rest) (.block []) :=
  rfl

theorem cols_eq : cols = (List.finRange 8).foldr (fun i rest => .seq (col i.val) rest) (.block []) :=
  rfl

/-- Both halves of scratch, initialized. -/
theorem initialized_all {m : Mem} {p : Addr} {r : Block} (h : VG.Proof.Argon2.X86_64.Avx2.Initialized m p r 32) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext; intro i hi
    have := (h ⟨i, hi⟩ (by simp only; omega)).1
    rw [← blockAt_get m p ⟨i, hi⟩] at this
    exact this
  · apply Vector.ext; intro i hi
    have := (h ⟨i, hi⟩ (by simp only; omega)).2
    rw [← working_get m p ⟨i, hi⟩] at this
    exact this

theorem vzeroupper_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun t => t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    VOp.exec_mem, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr,
    and_self]

/-- G between the MXCSR prologue and epilogue. -/
theorem body_ok {s : State} {p x y out : Addr} (hs : Scratch s p) (hin : Inputs s x y p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa body s fun t => blockAt t.mem out = Spec.Argon2.compress (blockAt s.mem x) (blockAt s.mem y) ∧
      Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold body
  apply WP.seq
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx2.masks_ok s).mono ?_
  rintro s0 ⟨hm0, hmem0, hg0, hr0, hw0, hx0⟩
  have hs0 : Scratch s0 p := ⟨(hg0 .rcx (by decide)).trans hs.reg, hw0 ▸ hs.wr⟩
  have hin0 : Inputs s0 x y p := ⟨(hg0 .rdi (by decide)).trans hin.xreg,
    (hg0 .rsi (by decide)).trans hin.yreg, by rw [hr0, hw0]; exact hin.xread,
    by rw [hr0, hw0]; exact hin.yread, hin.xsep, hin.ysep⟩
  refine (VG.Proof.Argon2.X86_64.Avx2.init_prefix 32 (by decide) hs0 hin0).mono ?_
  rintro s1 ⟨hi1, hf1, hk1, hm1⟩
  obtain ⟨horig, hwork⟩ := VG.Proof.Argon2.X86_64.Avx2.initialized_all hi1
  have hs1 := hs0.of_vkeep hk1
  apply WP.seq
  rw [VG.Proof.Argon2.X86_64.Avx2.rows_eq]
  refine (VG.Proof.Argon2.X86_64.Avx2.fold_ok rowIndex (fun i => row i.val) (fun i s hs hm => VG.Proof.Argon2.X86_64.Avx2.row_ok i.isLt hs hm)
    (List.finRange 8) s1 hs1 (hm1 hm0)).mono ?_
  rintro s2 ⟨hrow, hf2, hk2, hm2⟩
  apply WP.seq
  rw [VG.Proof.Argon2.X86_64.Avx2.cols_eq]
  refine (VG.Proof.Argon2.X86_64.Avx2.fold_ok colIndex (fun i => col i.val) (fun i s hs hm => VG.Proof.Argon2.X86_64.Avx2.col_ok i.isLt hs hm)
    (List.finRange 8) s2 (hs1.of_vkeep hk2) hm2).mono ?_
  rintro s3 ⟨hcol, hf3, hk3, -⟩
  have hk13 := hk1.trans (hk2.trans hk3)
  rw [WP.block_append_iff]
  refine (VG.Proof.Argon2.X86_64.Avx2.finish_prefix 32 (by decide) ((hs1.of_vkeep hk2).of_vkeep hk3)
    (by rw [hk13.gpr, hg0 .rdx (by decide)]; exact ho)
    (by rw [hk13.wr, hw0]; exact hw) hd).mono ?_
  rintro s4 ⟨hfin, hf4, hk4, -⟩
  refine (VG.Proof.Argon2.X86_64.Avx2.vzeroupper_ok s4).mono ?_
  rintro t ⟨hmt, hgt, hrt, hwt, hxt⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · apply Vector.ext; intro i hi
    have e := hfin ⟨i, hi⟩ (by simp only; omega)
    have ho3 := original_preserved (hf2.trans hf3)
    rw [horig] at ho3
    show (blockAt t.mem out)[(⟨i, hi⟩ : Fin 128)] =
      (compress (blockAt s.mem x) (blockAt s.mem y))[(⟨i, hi⟩ : Fin 128)]
    rw [blockAt_get, hmt, e, hcol, hrow, hwork, ho3, hmem0]
    rfl
  · rw [hmt]
    have f1 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s0.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f4 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s3.mem s4.mem :=
      hf4.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    rw [← hmem0]
    exact ((f1.trans (round_frame hf2)).trans (round_frame hf3)).trans f4
  · rw [hgt, hk4.gpr, hk13.gpr, hg0 r hr]
  · rw [hrt, hk4.rd, hk13.rd, hr0]
  · rw [hwt, hk4.wr, hk13.wr, hw0]
  · rw [hxt, hk4.mxcsr, hk13.mxcsr, hx0]

/-! ## MXCSR -/

/-- The eight bytes of scratch through which MXCSR is saved and loaded. -/
abbrev mxR (p : Addr) : Region := ⟨off p 2048, 8⟩

theorem mx_write {s : State} {p : Addr} (hs : Scratch s p) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) :
    InRegions s.wr (off p d) 4 :=
  hs.write (by omega)

theorem mx_read {s : State} {p : Addr} (hs : Scratch s p) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) :
    InRegions (s.rd ++ s.wr) (off p d) 4 :=
  hs.read (by omega)

theorem mx_contains (p : Addr) {d : Nat} (hd : 2048 ≤ d ∧ d ≤ 2052) : (VG.Proof.Argon2.X86_64.Avx2.mxR p).Contains (off p d) 4 :=
  Offset.contains p (by omega) (by omega) (by omega)

theorem save_ok {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block [.stmxcsr (VG.Impl.Argon2.X86_64.at_ .rcx mxcsrOff), .mov32 .r11 (.mem (VG.Impl.Argon2.X86_64.at_ .rcx mxcsrOff)),
      .alu32 .and .r11 (.imm 0xFFFF)]) s fun t =>
      t.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧ Frame [VG.Proof.Argon2.X86_64.Avx2.mxR p] s.mem t.mem := by
  apply WP.of_runBlock
  have hr := VG.Proof.Argon2.X86_64.Avx2.mx_read hs (d := 2048) (by decide)
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, VG.Proof.Argon2.X86_64.ea_at, hs.reg,
    VG.Proof.Argon2.X86_64.Avx2.mx_write hs (d := 2048) (by decide), ite_true, readSrc32, State.load32, hr, Option.map_some,
    Mem.readW_writeW_self32, execAlu32, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mxcsr_setReg,
    Option.some.injEq, exists_eq_left', ite_true, RegUpd.setWidth_setWidth_32]
  refine ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.mx_contains p (by decide))⟩


theorem set_ok {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (VG.Impl.Argon2.X86_64.at_ .rcx (mxcsrOff + 4)) .rax,
      .ldmxcsr (VG.Impl.Argon2.X86_64.at_ .rcx (mxcsrOff + 4)), .lfence]) s fun t =>
      t.mxcsr = 0x1FBF ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [VG.Proof.Argon2.X86_64.Avx2.mxR p] s.mem t.mem := by
  have hr := VG.Proof.Argon2.X86_64.Avx2.mx_read hs (d := 2052) (by decide)
  have hz : BitVec.extractLsb' 16 16 (8127 : BitVec 32) = 0 := by decide
  apply WP.of_runBlock
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, VG.Proof.Argon2.X86_64.ea_at,
    readSrc32, State.setReg32, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, hs.reg, Option.map_some, Option.bind_some, State.load32,
    Mem.readW_writeW_self32, VG.Proof.Argon2.X86_64.Avx2.mx_write hs (d := 2052) (by decide), hr, RegUpd.setWidth_setWidth_32,
    reduceCtorEq, ↓reduceIte, Nat.reduceAdd, hz, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.mx_contains p (by decide))⟩


theorem restore_ok {s : State} {p : Addr} (hs : Scratch s p)
    (hz : BitVec.extractLsb' 16 16 ((s.gpr .r11).setWidth 32) = 0) :
    WP isa (.block [.store32 (VG.Impl.Argon2.X86_64.at_ .rcx mxcsrOff) .r11, .ldmxcsr (VG.Impl.Argon2.X86_64.at_ .rcx mxcsrOff)]) s fun t =>
      t.mxcsr = (s.gpr .r11).setWidth 32 ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [VG.Proof.Argon2.X86_64.Avx2.mxR p] s.mem t.mem := by
  have hr := VG.Proof.Argon2.X86_64.Avx2.mx_read hs (d := 2048) (by decide)
  apply WP.of_runBlock
  simp only [mxcsrOff, runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, VG.Proof.Argon2.X86_64.ea_at,
    hs.reg, State.load32, Mem.readW_writeW_self32, VG.Proof.Argon2.X86_64.Avx2.mx_write hs (d := 2048) (by decide), hr,
    ↓reduceIte, Option.bind_some, hz, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Argon2.X86_64.Avx2.mx_contains p (by decide))⟩

theorem mxR_sub (p : Addr) : Region.Sub (VG.Proof.Argon2.X86_64.Avx2.mxR p) ⟨p, 4096⟩ := Offset.sub_base p (by decide)

/-- A block outside scratch is unchanged by writes to `mxR`. -/
theorem blockAt_mx {m m' : Mem} {p q : Addr} (hf : Frame [VG.Proof.Argon2.X86_64.Avx2.mxR p] m m')
    (hd : (⟨q, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) : blockAt m' q = blockAt m q := by
  have d1 : (⟨q, 1024⟩ : Region).Disjoint ⟨off p 2048, 8⟩ := hd.sub_right (VG.Proof.Argon2.X86_64.Avx2.mxR_sub p)
  apply Vector.ext
  intro i hi
  have he : m'.readW (off q (8 * i)) 64 = m.readW (off q (8 * i)) 64 :=
    hf.readW (r := ⟨q, 1024⟩) (Offset.contains_base q (by omega) (by omega))
      (fun r hr => (List.mem_singleton.mp hr) ▸ d1) (by decide)
  rw [← blockAt_get m' q ⟨i, hi⟩, ← blockAt_get m q ⟨i, hi⟩] at he
  exact he

theorem ldmxcsr_ok (v : BitVec 32) :
    BitVec.extractLsb' 16 16 (BitVec.setWidth 32 (BitVec.setWidth 64 (v &&& 0xFFFF))) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp


/-! ## G -/

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.Avx2.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  unfold Impl.Argon2.X86_64.Avx2.compress
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx2.save_ok scr).mono ?_
  rintro s1 ⟨h11, hg1, hr1, hw1, -, hf1⟩
  have scr1 : Scratch s1 (s.gpr .rcx) := ⟨hg1 .rcx (by decide), hw1 ▸ scr.wr⟩
  apply WP.seq
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx2.set_ok scr1).mono ?_
  rintro s2 ⟨-, hg2, hr2, hw2, hf2⟩
  have hg12 : ∀ r, r ≠ .rax → r ≠ .r11 → s2.gpr r = s.gpr r :=
    fun r h0 h11 => (hg2 r h0).trans (hg1 r h11)
  have scr2 : Scratch s2 (s.gpr .rcx) := ⟨hg12 .rcx (by decide) (by decide), hw2 ▸ scr1.wr⟩
  have hf12 := hf1.trans hf2
  have inputs : Inputs s2 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨hg12 .rdi (by decide) (by decide), hg12 .rsi (by decide) (by decide),
      by rw [hr2, hw2, hr1, hw1]; simp [hrd], by rw [hr2, hw2, hr1, hw1]; simp [hrd], hx, hy⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.Avx2.body_ok scr2 inputs (out := s.gpr .rdx) (hg12 .rdx (by decide) (by decide))
    (by rw [hw2, hw1, hwr]; simp) hout.symm).mono ?_
  rintro s3 ⟨hpost, hf3, hg3, hr3, hw3, -⟩
  refine WP.of_runBlock ⟨s3, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec], ?_⟩
  have scr3 : Scratch s3 (s.gpr .rcx) := ⟨(hg3 .rcx (by decide)).trans scr2.reg, hw3 ▸ scr2.wr⟩
  have h113 : s3.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [hg3 .r11 (by decide), hg2 .r11 (by decide), h11]
  refine (VG.Proof.Argon2.X86_64.Avx2.restore_ok scr3 (by rw [h113]; exact VG.Proof.Argon2.X86_64.Avx2.ldmxcsr_ok _)).mono ?_
  rintro t ⟨-, hgt, -, -, hft⟩
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · change blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    rw [VG.Proof.Argon2.X86_64.Avx2.blockAt_mx hft hout, hpost, VG.Proof.Argon2.X86_64.Avx2.blockAt_mx hf12 hx, VG.Proof.Argon2.X86_64.Avx2.blockAt_mx hf12 hy]
  · have h0 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 : r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hgt, hg3 r h0, hg12 r h0 h1]
  · have hmx : ∀ {m m' : Mem}, Frame [VG.Proof.Argon2.X86_64.Avx2.mxR (s.gpr .rcx)] m m' →
        Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] m m' := fun h =>
      h.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨_, by simp, VG.Proof.Argon2.X86_64.Avx2.mxR_sub _⟩
    rw [hwr]
    exact ((hmx hf12).trans hf3).trans (hmx hft)

theorem compress_ctl : ctlOk Impl.Argon2.X86_64.Avx2.compress = true := by lit_decide

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.Avx2.compress s tr t ∧ abiPreserved s t ∧ compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := VG.Proof.Argon2.X86_64.Avx2.compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_ctl VG.Proof.Argon2.X86_64.Avx2.compress_ctl he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.Avx2.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ hs ht hp => initial_agree hs ht hp)
    (by taint_decide)

/-- `vg_argon2_compress_avx2` meets the contract of `vg_argon2_compress`. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.Avx2.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Argon2.X86_64.Avx2.compress_correct VG.Proof.Argon2.X86_64.Avx2.compress_ct compress_implies

end VG.Proof.Argon2.X86_64.Avx2

end

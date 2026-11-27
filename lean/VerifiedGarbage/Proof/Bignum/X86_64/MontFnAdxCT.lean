module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Bignum.X86_64.MontFnAdx`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_mont_mul_adx`: correctness

The head (`enter`, `slotsIn`) saves the callee-saved registers in
`xmm8`–`xmm13`, header words 16–21 in `xmm3`–`xmm5` and 28–31 in `xmm6` and
`xmm7`, and writes the bases of `o`, `a` and `b` into the slots of `xO`, `xA`
and `xB` (`Ops`); the body runs the tiled ADX code for those slots, which
changes words 28–31 too (`AdxTiledSquare.rawSquareBare_ok` or
`AdxTiledProduct.rawProductBare_ok`, then `AdxTiledProduct.redcFinish_ok`)
or, for `w` not a multiple of 8, `montMul` (`mmTail_ok`); the tail writes the
header words back, so that only `aAcc`, `aTmp` and `o` change, and restores
the callee-saved registers (`unsaves_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The head's memory: the bases of `o`, `a` and `b` in the slots of `xO`,
`xA` and `xB`. -/
def headMem (m : Mem) (B : Addr) (w o a b : Nat) : Mem :=
  ((m.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA)) (off B (slot w a))).writeW
    (off B (8 * sArr xB)) (off B (slot w b))

theorem setWidth_ofNat32 {o : Nat} (h : o < 2 ^ 32) : ((BitVec.ofNat 32 o).setWidth 64) = BitVec.ofNat 64 o :=
  ofNat32_64 h

theorem arr_off64 (B : Addr) {j : Nat} (hj : j < 2 ^ 32) :
    off (B + BitVec.ofNat 64 j * 8#64) (8 * sArr 0) = off B (8 * sArr j) := by
  rw [← setWidth_ofNat32 hj]; exact arr_off B hj

/-- `zext`: the indices in all of `rdx`, `rcx` and `r8`. -/
theorem zextIdx_ok {s : State} {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o) (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a)
    (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block zext) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 a ∧ t.gpr .r8 = BitVec.ofNat 64 b ∧
      t.mem = s.mem ∧ t.xmm = s.xmm ∧ Keep [.rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rdx, .rcx, .r8] (c := .block zext)
    (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 a ∧ t.gpr .r8 = BitVec.ofNat 64 b ∧
      t.mem = s.mem ∧ t.xmm = s.xmm) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold zext
  xrun [hdx, hcx, h8, setWidth_ofNat32 (show o < 2 ^ 32 by omega_arith), setWidth_ofNat32 (show a < 2 ^ 32 by omega_arith),
    setWidth_ofNat32 (show b < 2 ^ 32 by omega_arith), setReg_xmm]

/-- `saves` and `slotsIn`, with the indices zero-extended. -/
theorem adxRest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : s.gpr .rdx = BitVec.ofNat 64 o)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 a) (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    WP isa (.block (saves ++ slotsIn)) s fun t =>
      t.mem = headMem s.mem B w o a b ∧ Keep [.rax] s t ∧
      Saved s t ∧ t.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      t.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ t.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128 ∧
      t.xmm .xmm6 = s.mem.readW (off B (8 * sFn 12)) 128 ∧ t.xmm .xmm7 = s.mem.readW (off B (8 * sFn 14)) 128 := by
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hl16 : ∀ i < 31, InRegions (s.rd ++ s.wr) (off B (8 * i)) 16 := fun i hi =>
    let ⟨r, hm, hc⟩ := hs.region (d := 8 * i) (n := 16) (by have := hdr_lt_slot w 8 (show i + 1 < 32 by omega_arith); omega_arith)
      (by decide)
    ⟨r, List.mem_append_right _ hm, hc⟩
  refine WP.mono (WP.keep [.rax] (c := .block (saves ++ slotsIn))
    (Q := fun t => t.mem = headMem s.mem B w o a b ∧
      Saved s t ∧ t.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      t.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ t.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128 ∧
      t.xmm .xmm6 = s.mem.readW (off B (8 * sFn 12)) 128 ∧ t.xmm .xmm7 = s.mem.readW (off B (8 * sFn 14)) 128) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, k, h.2⟩
  unfold saves slotsIn Saved
  simp only [List.cons_append, List.nil_append]
  xrun [XOp.exec, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm, setReg_xmm, XBinOp.eval, qword_movq,
    State.ea, State.load128, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off64 B (show o < 2 ^ 32 by omega_arith),
    arr_off64 B (show a < 2 ^ 32 by omega_arith), arr_off64 B (show b < 2 ^ 32 by omega_arith),
    hl (sArr o) (by unfold sArr; omega_arith), hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
    hw (sArr xO) (by decide), hw (sArr xA) (by decide), hw (sArr xB) (by decide),
    hl16 (sFn 0) (by decide), hl16 (sFn 2) (by decide), hl16 (sFn 4) (by decide), hl16 (sFn 12) (by decide),
    hl16 (sFn 14) (by decide), hH.harr o ho]
  have hn := hs.nowrap
  obtain o₁ := writeW_outside s.mem B (d := 8 * sArr xO) (off B (slot w o)) (by unfold sArr xO; omega_arith)
  obtain o₂ := writeW_outside (s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega_arith)
  obtain ra : (s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))).readW (off B (8 * sArr a)) 64 =
      off B (slot w a) :=
    (o₁.word (by unfold sArr xO; omega_arith) (by unfold sArr; omega_arith)).trans (hH.harr a ha)
  obtain rb : ((s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
      (off B (slot w a))).readW (off B (8 * sArr b)) 64 = off B (slot w b) :=
    ((o₂.word (by unfold sArr xA; omega_arith) (by unfold sArr; omega_arith)).trans
      (o₁.word (by unfold sArr xO; omega_arith) (by unfold sArr; omega_arith))).trans (hH.harr b hb)
  rw [ra, rb]; rfl

/-! ## The size test -/

/-- What `alignTest` tests: the tiles apply. -/
def AlignOk (w : Nat) : Prop := w % 8 = 0 ∧ 8 ≤ w ∧ w < 2 ^ 30 + 8

instance (w : Nat) : Decidable (AlignOk w) := inferInstanceAs (Decidable (_ ∧ _))

theorem rotr3_toNat (x : BitVec 64) : (x.rotateRight 3).toNat = x.toNat / 8 + x.toNat % 8 * 2 ^ 61 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reduceSub]
  have hx := x.isLt
  rw [Nat.shiftLeft_eq, show x.toNat * 2 ^ 61 % 2 ^ 64 = (x.toNat % 8) <<< 61 by rw [Nat.shiftLeft_eq]; omega_arith,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega_arith), Nat.shiftLeft_eq]
  omega_arith

theorem alignTest_beq (w : Nat) (hw : w < 2 ^ 64) :
    ((BitVec.ofNat 64 w - 8).rotateRight 3 >>> 27 == 0) = decide (AlignOk w) := by
  obtain h : ((BitVec.ofNat 64 w - 8).rotateRight 3 >>> 27).toNat =
      ((2 ^ 64 - 8 + w) % 2 ^ 64 / 8 + (2 ^ 64 - 8 + w) % 2 ^ 64 % 8 * 2 ^ 61) / 2 ^ 27 := by
    rw [BitVec.toNat_ushiftRight, rotr3_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (8 : BitVec 64).toNat = 8 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  generalize hv : (2 ^ 64 - 8 + w) % 2 ^ 64 = v at h
  obtain h1 : v % 8 = w % 8 := by omega_arith
  obtain h3 : 8 ≤ w → v = w - 8 := by omega_arith
  obtain h4 : w < 8 → v = 2 ^ 64 - 8 + w := by omega_arith
  unfold AlignOk
  by_cases h0 : w % 8 = 0 ∧ 8 ≤ w ∧ w < 2 ^ 30 + 8
  · simp only [h0, and_self, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; have := congrArg BitVec.toNat he; rw [h, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega_arith

/-- `alignTest`: ZF set when the tiles apply. -/
theorem alignTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block alignTest) s fun t => t.zf = some (decide (AlignOk w)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (AlignOk w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold alignTest
  xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_arith),
    hH.hw, alignTest_beq w (by unfold slot hdrBytes at hZ; omega_arith)]

/-- `basesR`, with the indices zero-extended. -/
theorem basesR_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : s.gpr .rdx = BitVec.ofNat 64 o)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 a) (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    WP isa (.block basesR) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem ∧
      Keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] s t := by
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] (c := .block basesR)
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩
  unfold basesR
  xrun [State.ea, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off64 B (show o < 2 ^ 32 by omega_arith),
    arr_off64 B (show a < 2 ^ 32 by omega_arith), arr_off64 B (show b < 2 ^ 32 by omega_arith),
    hl (sArr o) (by unfold sArr; omega_arith), hl (sArr a) (by unfold sArr; omega_arith), hl (sArr b) (by unfold sArr; omega_arith),
    hl (sArr aN) (by decide), hl (sArr aAcc) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr aN (by decide),
    hH.harr aAcc (by decide), hH.harr aTmp (by decide), hH.hw, hH.hminv]

/-- `cmp rcx, r8`: ZF set when the indices are equal. -/
theorem cmpIdx_ok {s : State} {a b : Nat} (ha : a < 8) (hb : b < 8) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    WP isa (.block [.alu .cmp .rcx (.reg .r8)]) s fun t =>
      t.zf = some (decide (a = b)) ∧ t.mem = s.mem ∧ t.gpr .rcx = s.gpr .rcx ∧ Keep [.rcx] s t := by
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.zf = some (decide (a = b)) ∧ t.mem = s.mem ∧
    t.gpr .rcx = s.gpr .rcx) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hcx, h8, ofNat_sub_beq (show a < 2 ^ 64 by omega_arith) (show b < 2 ^ 64 by omega_arith)]

/-- The operands' slots as the head leaves them. -/
abbrev adxOps (o a b : Nat) : List (Nat × Nat) := [(xO, o), (xA, a), (xB, b)]

theorem mem_adxOps_o (o a b : Nat) : (xO, o) ∈ adxOps o a b := .head _
theorem mem_adxOps_a (o a b : Nat) : (xA, a) ∈ adxOps o a b := .tail _ (.head _)
theorem mem_adxOps_b (o a b : Nat) : (xB, b) ∈ adxOps o a b := .tail _ (.tail _ (.head _))

/-- `adxBody`: what `montMul_ok` says, for the arrays whose bases are in the
slots of `xO`, `xA` and `xB` and whose indices are in `rdx`, `rcx` and `r8`. -/
theorem adxBody_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hv : Ops s.mem B w (adxOps o a b))
    (hdx : s.gpr .rdx = BitVec.ofNat 64 o) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa adxBody s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t := by
  unfold adxBody
  refine WP.seq (WP.mono (alignTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH hv ⊢
  obtain post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s₁.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, ⟨_, Outside.refl _ _ _ _, h3⟩, (k₁.trans k).mono (by decide)⟩
  by_cases h8w : AlignOk w
  · refine WP.ite true (by simp [eval, hz, h8w]) (fun _ => ?_) (by simp)
    obtain ⟨h8w, h8w', -⟩ := h8w
    unfold tiled
    obtain hcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 a := (k₁.gpr (by decide)).trans hcx
    obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 b := (k₁.gpr (by decide)).trans h8
    refine WP.seq (WP.mono (cmpIdx_ok ha hb hcx₁ h8₁) fun s₂ ⟨hz₂, hm₂, _, k₂⟩ => ?_)
    obtain hs₂ := hs₁.congr k₂.2.2
    obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
    rw [← hm₂] at hinv hB hH hv ⊢
    obtain hwN : w = 8 * (w / 8) := by omega_arith
    obtain hraw : WP isa (.ite .e (AdxTiledSquare.rawSquareBare xA) (AdxTiledProduct.rawProductBare xA xB)) s₂
        fun s₃ => ∃ m, Outside B (8 * sFn 12) 32 s₂.mem m ∧
          wv s₃.mem B (slot w aAcc + 16) (2 * w) = wv s₂.mem B (slot w a) w * wv s₂.mem B (slot w b) w ∧
          Outside B (slot w aAcc) (16 * w + 32) m s₃.mem ∧ Keep mmRegs s₂ s₃ := by
      by_cases hab : a = b
      · subst b
        exact WP.ite true (by simp [eval, hz₂]) (fun _ =>
          AdxTiledSquare.rawSquareBare_ok hs₂ hdi₂ hH hZ hwN (by omega_arith) hw' hv (mem_adxOps_a o a a) ha ha1 ha2)
          (by simp)
      · exact WP.ite false (by simp [eval, hz₂, hab]) (by simp) (fun _ =>
          AdxTiledProduct.rawProductBare_ok hs₂ hdi₂ hH hv (mem_adxOps_a o a b) (mem_adxOps_b o a b) hZ hw' hwN
            (by omega_arith) ha hb ha1 ha2 hb1 hb2)
    refine WP.seq (WP.mono hraw fun s₃ ⟨m, om, hv₃, ho₃, k₃⟩ => ?_)
    have hn := hs.nowrap
    obtain sl : ∀ j < 8, 8 * sFn 12 + 32 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ Z := fun j hj =>
      ⟨by unfold slot sFn hdrBytes; omega_arith, Nat.le_trans (slot_le hj) hZ⟩
    obtain vm : ∀ j < 8, wv m B (slot w j) w = wv s₂.mem B (slot w j) w := fun j hj =>
      om.wv (Or.inr (sl j hj).1) (by have := (sl j hj).2; omega_arith)
    obtain hinvm : ((word m B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [om.word (Or.inr (sl aN (by decide)).1) (by have := (sl aN (by decide)).2; omega_arith)]; exact hinv
    refine WP.mono (AdxTiledProduct.redcFinish_ok (s := {s₂ with mem := m}) (hs₂.congr rfl) hdi₂
      (hH.of_outside_fn om (by unfold sFn; omega_arith)) hZ hwN (by omega_arith) hw'
      (hv.of_outside om (Nat.le_refl _)) (mem_adxOps_o o a b) ho ho1 ho2 hinvm
      (by dsimp only; rw [vm aN (by decide)]; exact AdxTiledProduct.mul_lt_mont (wv_lt _ _ _ _) hB) hv₃ ho₃ k₃)
      fun t ⟨h1, h2, h3, k⟩ => ?_
    dsimp only at h1 h2 h3
    rw [vm aN (by decide)] at h1 h2
    exact ⟨h1, h2, ⟨m, om, h3⟩, ((k₁.trans k₂).trans k).mono (by decide)⟩
  · refine WP.ite false (by simp [eval, hz, h8w]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (basesR_ok hs₁ hdi₁ hH hZ ho ha hb ((k₁.gpr (by decide)).trans hdx)
      ((k₁.gpr (by decide)).trans hcx) ((k₁.gpr (by decide)).trans h8))
      fun s₂ ⟨hbx, h11, h9, h10, h8₂, h12, h15, hsi₂, hm₂, k₂⟩ => ?_)
    rw [← hm₂] at hinv hB
    refine WP.mono (mmTail_ok (hs₁.congr k₂.2.2) hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
      (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
      h8₂ h12 h15 hsi₂ hinv hB) fun t ⟨h1, h2, h3, k⟩ => ?_
    rw [hm₂] at h1 h2 h3
    exact post t ⟨h1, h2, h3, (k₂.trans k).mono (by decide)⟩

/-! ## The head's memory -/

theorem headMem_outside (m : Mem) (B : Addr) (w o a b : Nat) :
    Outside B (8 * sArr xO) 24 m (headMem m B w o a b) := by
  obtain o₁ := writeW_outside m B (d := 8 * sArr xO) (off B (slot w o)) (by unfold sArr xO; omega_arith)
  obtain o₂ := writeW_outside (m.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega_arith)
  obtain o₃ := writeW_outside ((m.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
    (off B (slot w a))) B (d := 8 * sArr xB) (off B (slot w b)) (by unfold sArr xB; omega_arith)
  exact ((o₁.mono (by decide) (by decide)).trans (o₂.mono (by decide) (by decide))).trans
    (o₃.mono (by decide) (by decide))

theorem headMem_hdr {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) (o a b : Nat) :
    Hdr (headMem m B w o a b) B w minv :=
  ((hH.store (i := sArr xO) (by decide) (by decide) _).store (i := sArr xA) (by decide) (by decide) _).store
    (i := sArr xB) (by decide) (by decide) _

theorem headMem_ops (m : Mem) (B : Addr) (w o a b : Nat) : Ops (headMem m B w o a b) B w (adxOps o a b) := by
  obtain o₂ := writeW_outside ((m.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
    (off B (slot w a))) B (d := 8 * sArr xB) (off B (slot w b)) (by unfold sArr xB; omega_arith)
  obtain o₁ := writeW_outside (m.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega_arith)
  intro p hp
  simp only [adxOps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨show xO < 20 by decide, ?_⟩
    unfold OpAt headMem
    rw [o₂.word (by unfold sArr xO xB; omega_arith) (by unfold sArr xO; omega_arith),
      o₁.word (by unfold sArr xO xA; omega_arith) (by unfold sArr xO; omega_arith), word_writeW_self]
  · refine ⟨show xA < 20 by decide, ?_⟩
    unfold OpAt headMem
    rw [o₂.word (by unfold sArr xA xB; omega_arith) (by unfold sArr xA; omega_arith), word_writeW_self]
  · exact ⟨show xB < 20 by decide, word_writeW_self _ _ _ _⟩

/-- Writing back 16 bytes read before restores them. -/
theorem write_restore (m m₀ : Mem) (B : Addr) {d : Nat} (hd : d + 16 < 2 ^ 64) {x : Addr} (hx : d ≤ ofs B x)
    (hx' : ofs B x < d + 16) : (m.writeW (off B d) (m₀.readW (off B d) 128)) x = m₀ x := by
  obtain e : (x - off B d).toNat = ofs B x - d := by
    unfold ofs off at *; rw [Offset.toNat_sub_add x B (by omega_arith)]; have := (x - B).isLt; omega_arith
  simp only [Mem.writeW, Mem.readW, Mem.write]
  simp only [show (x - off B d).toNat < 128 / 8 by omega_arith, ite_true]
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read m₀ _ (by omega_arith)]
  congr 1
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The three header stores of `restore`: header words 16–21 as `m₀` has
them, from `xmm3`–`xmm5`. -/
theorem restoreHdr_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {m₀ : Mem} (h3 : s.xmm .xmm3 = m₀.readW (off B (8 * sFn 0)) 128)
    (h4 : s.xmm .xmm4 = m₀.readW (off B (8 * sFn 2)) 128) (h5 : s.xmm .xmm5 = m₀.readW (off B (8 * sFn 4)) 128) :
    WP isa (.block [.movdquStore (hdr (sFn 0)) .xmm3, .movdquStore (hdr (sFn 2)) .xmm4,
        .movdquStore (hdr (sFn 4)) .xmm5]) s fun t =>
      Outside B (8 * sFn 0) 48 s.mem t.mem ∧
      (∀ x, 8 * sFn 0 ≤ ofs B x → ofs B x < 8 * sFn 0 + 48 → t.mem x = m₀ x) ∧ t.xmm = s.xmm ∧ Keep [] s t := by
  have hn := hs.nowrap
  obtain hw16 : ∀ i < 31, InRegions s.wr (off B (8 * i)) 16 := fun i hi =>
    let ⟨r, hm, hc⟩ := hs.region (d := 8 * i) (n := 16) (by omega_arith) (by decide)
    ⟨r, hm, hc⟩
  let m₂ := ((s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2)) (s.xmm .xmm4)).writeW
    (off B (8 * sFn 4)) (s.xmm .xmm5)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = m₂ ∧ t.xmm = s.xmm) ?_ rfl) fun t ⟨⟨hm, hx⟩, k⟩ =>
    ⟨?_, ?_, hx, k⟩
  · xrun [State.ea, State.store128, hdr, hdi, hdrOff, hw16 (sFn 0) (by decide), hw16 (sFn 2) (by decide),
      hw16 (sFn 4) (by decide)]
    rfl
  · rw [hm]
    obtain w₃ := writeW_outsideN s.mem B (d := 8 * sFn 0) (s.xmm .xmm3) (by unfold sFn; omega_arith) (by decide)
    obtain w₄ := writeW_outsideN (s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)) B (d := 8 * sFn 2) (s.xmm .xmm4)
      (by unfold sFn; omega_arith) (by decide)
    obtain w₅ := writeW_outsideN ((s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2))
      (s.xmm .xmm4)) B (d := 8 * sFn 4) (s.xmm .xmm5) (by unfold sFn; omega_arith) (by decide)
    exact ((w₃.mono (by decide) (by decide)).trans (w₄.mono (by decide) (by decide))).trans
      (w₅.mono (by decide) (by decide))
  · intro x hx hx'
    rw [hm]
    dsimp only [m₂]
    obtain w₄ := writeW_outsideN (s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)) B (d := 8 * sFn 2) (s.xmm .xmm4)
      (by unfold sFn; omega_arith) (by decide)
    obtain w₅ := writeW_outsideN ((s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2))
      (s.xmm .xmm4)) B (d := 8 * sFn 4) (s.xmm .xmm5) (by unfold sFn; omega_arith) (by decide)
    unfold sFn at hx hx'
    by_cases c₅ : 8 * sFn 4 ≤ ofs B x
    · rw [h5]; exact write_restore _ _ B (by unfold sFn; omega_arith) c₅ (by unfold sFn at *; omega_arith)
    rw [w₅ x (Or.inl (by omega_arith))]
    by_cases c₄ : 8 * sFn 2 ≤ ofs B x
    · rw [h4]; exact write_restore _ _ B (by unfold sFn; omega_arith) c₄ (by unfold sFn at *; omega_arith)
    rw [w₄ x (Or.inl (by omega_arith)), h3]
    exact write_restore _ _ B (by unfold sFn; omega_arith) (by unfold sFn; omega_arith) (by unfold sFn at *; omega_arith)

/-- The two header stores of `restore` after them: header words 28–31, which
the tiles borrow, as `m₀` has them, from `xmm6` and `xmm7`. -/
theorem restoreBor_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {m₀ : Mem} (h6 : s.xmm .xmm6 = m₀.readW (off B (8 * sFn 12)) 128)
    (h7 : s.xmm .xmm7 = m₀.readW (off B (8 * sFn 14)) 128) :
    WP isa (.block [.movdquStore (hdr (sFn 12)) .xmm6, .movdquStore (hdr (sFn 14)) .xmm7]) s fun t =>
      Outside B (8 * sFn 12) 32 s.mem t.mem ∧
      (∀ x, 8 * sFn 12 ≤ ofs B x → ofs B x < 8 * sFn 12 + 32 → t.mem x = m₀ x) ∧ Keep [] s t := by
  have hn := hs.nowrap
  obtain hw16 : ∀ i < 31, InRegions s.wr (off B (8 * i)) 16 := fun i hi =>
    let ⟨r, hm, hc⟩ := hs.region (d := 8 * i) (n := 16) (by omega_arith) (by decide)
    ⟨r, hm, hc⟩
  let m₂ := (s.mem.writeW (off B (8 * sFn 12)) (s.xmm .xmm6)).writeW (off B (8 * sFn 14)) (s.xmm .xmm7)
  obtain w₆ := writeW_outsideN s.mem B (d := 8 * sFn 12) (s.xmm .xmm6) (by unfold sFn; omega_arith) (by decide)
  obtain w₇ := writeW_outsideN (s.mem.writeW (off B (8 * sFn 12)) (s.xmm .xmm6)) B (d := 8 * sFn 14) (s.xmm .xmm7)
    (by unfold sFn; omega_arith) (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = m₂) ?_ rfl) fun t ⟨hm, k⟩ => ⟨?_, ?_, k⟩
  · xrun [State.ea, State.store128, hdr, hdi, hdrOff, hw16 (sFn 12) (by decide), hw16 (sFn 14) (by decide)]
    rfl
  · rw [hm]
    exact (w₆.mono (by decide) (by decide)).trans (w₇.mono (by decide) (by decide))
  · intro x hx hx'
    rw [hm]
    dsimp only [m₂]
    unfold sFn at hx hx'
    by_cases c₇ : 8 * sFn 14 ≤ ofs B x
    · rw [h7]; exact write_restore _ _ B (by unfold sFn; omega_arith) c₇ (by unfold sFn at *; omega_arith)
    rw [w₇ x (Or.inl (by omega_arith)), h6]
    exact write_restore _ _ B (by unfold sFn; omega_arith) (by unfold sFn; omega_arith) (by unfold sFn at *; omega_arith)

/-- `restore`: the callee-saved registers of `s₀` from `xmm8`–`xmm13`, and
header words 16–21 and 28–31 as `m₀` has them, from `xmm3`–`xmm7`. -/
theorem restore_ok {s₀ s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {m₀ : Mem} (h3 : s.xmm .xmm3 = m₀.readW (off B (8 * sFn 0)) 128)
    (h4 : s.xmm .xmm4 = m₀.readW (off B (8 * sFn 2)) 128) (h5 : s.xmm .xmm5 = m₀.readW (off B (8 * sFn 4)) 128)
    (h6 : s.xmm .xmm6 = m₀.readW (off B (8 * sFn 12)) 128) (h7 : s.xmm .xmm7 = m₀.readW (off B (8 * sFn 14)) 128)
    (hsv : Saved s₀ s) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s₀.gpr r) ∧
      Frm B [(8 * sFn 0, 48), (8 * sFn 12, 32)] s.mem t.mem ∧
      (∀ x, 8 * sFn 0 ≤ ofs B x → ofs B x < 8 * sFn 0 + 48 → t.mem x = m₀ x) ∧
      (∀ x, 8 * sFn 12 ≤ ofs B x → ofs B x < 8 * sFn 12 + 32 → t.mem x = m₀ x) ∧
      Keep [.rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold restore
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (unsaves_ok hsv) fun a ⟨ra, ma, xa, ka⟩ => ?_
  refine WP.mono (restoreHdr_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hdi) hZ
    (m₀ := m₀) (by rw [xa]; exact h3) (by rw [xa]; exact h4) (by rw [xa]; exact h5)) fun b ⟨ob, ib, xb, kb⟩ => ?_
  refine WP.mono (restoreBor_ok (hs.congr (ka.trans kb).2.2) (((ka.trans kb).gpr (by decide)).trans hdi) hZ
    (m₀ := m₀) (by rw [xb, xa]; exact h6) (by rw [xb, xa]; exact h7)) fun t ⟨ot, it, kt⟩ => ?_
  refine ⟨fun r hr => ((kb.trans kt).gpr (by simp)).trans (ra r hr),
    (Frm.of_outside (by rw [← ma]; exact ob) (by simp)).trans (Frm.of_outside ot (by simp)),
    fun x hx hx' => ?_, it, ((ka.trans kb).trans kt).mono (by simp)⟩
  rw [ot x (Or.inl (by unfold sFn at *; omega_arith))]; exact ib x hx hx'

/-- `enter` and `slotsIn`. -/
theorem adxHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block (enter ++ slotsIn)) s fun s₁ =>
      s₁.mem = headMem s.mem B w o a b ∧ s₁.gpr .rdx = BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 a ∧ s₁.gpr .r8 = BitVec.ofNat 64 b ∧
      Keep [.rdx, .rcx, .r8, .rax] s s₁ ∧
      Saved s s₁ ∧ s₁.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      s₁.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ s₁.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128 ∧
      s₁.xmm .xmm6 = s.mem.readW (off B (8 * sFn 12)) 128 ∧ s₁.xmm .xmm7 = s.mem.readW (off B (8 * sFn 14)) 128 := by
  rw [show enter ++ slotsIn = zext ++ (saves ++ slotsIn) from by simp [enter], WP.block_append_iff]
  refine WP.mono (zextIdx_ok ho ha hb hdx hcx h8) fun s₀ ⟨hdx₀, hcx₀, h8₀, hm₀, _, k₀⟩ => ?_
  refine WP.mono (adxRest_ok (hs.congr k₀.2.2) ((k₀.gpr (by decide)).trans hdi) (hm₀ ▸ hH) hZ ho ha hb hdx₀
    hcx₀ h8₀) fun s₁ ⟨hm₁, k₁, sv, x3, x4, x5, x6, x7⟩ => ?_
  rw [hm₀] at hm₁ x3 x4 x5 x6 x7
  exact ⟨hm₁, (k₁.gpr (by decide)).trans hdx₀, (k₁.gpr (by decide)).trans hcx₀,
    (k₁.gpr (by decide)).trans h8₀, (k₀.trans k₁).mono (by decide), sv.of_keep k₀ (by decide), x3, x4, x5, x6, x7⟩

/-- `vg_rsa_mont_mul_adx`'s code: what `mulBase_ok` says of `vg_rsa_mont_mul`'s. -/
theorem mulAdx_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa mulAdx s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  obtain h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  have hxO : 8 * sArr xO = 8 * sFn 0 := rfl
  obtain sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  obtain s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  obtain hZ32 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 0 (show 31 < 32 by decide); have := sl 0 (by decide); omega_arith
  unfold mulAdx
  refine WP.seq (WP.mono (adxHead_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun s₁ ⟨hm₁, hdx₁, hcx₁, h8₁, k₁, sv, x3, x4, x5, x6, x7⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  obtain ho₁ : Outside B (8 * sArr xO) 24 s.mem s₁.mem := hm₁ ▸ headMem_outside s.mem B w o a b
  obtain vj : ∀ j < 8, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj =>
    ho₁.wv (by have := s0 j; omega_arith) (by have := sl j hj; omega_arith)
  obtain hinv₁ : ((word s₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho₁.word (by have := s0 aN; omega_arith) (by have := sl aN (by decide); omega_arith)]; exact hinv
  obtain hB₁ : wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w := by
    rw [vj b hb, vj aN (by decide)]; exact hB
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (adxBody_ok hs₁ hdi₁ (hm₁ ▸ headMem_hdr hH o a b) hZ hw hw' ho
    ha hb ho1 ho2 ha1 ha2 hb1 hb2 (hm₁ ▸ headMem_ops s.mem B w o a b) hdx₁ hcx₁ h8₁ hinv₁ hB₁))
    fun s₂ ⟨⟨hlt, heq, ⟨mb, omb, har⟩, k₂⟩, hx₂, _⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (restore_ok hs₂ hdi₂ hZ32 (m₀ := s.mem) (by rw [hx₂, x3]) (by rw [hx₂, x4]) (by rw [hx₂, x5])
    (by rw [hx₂, x6]) (by rw [hx₂, x7]) (sv.of_xmm hx₂))
    fun t ⟨rs, o₃, in₃, inb₃, k₃⟩ => ?_
  obtain hvo : wv t.mem B (slot w o) w = wv s₂.mem B (slot w o) w :=
    o₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> have := s0 o <;> unfold sFn slot hdrBytes at * <;> omega_arith)
      (by have := sl o ho; omega_arith)
  rw [vj aN (by decide)] at hlt
  rw [vj aN (by decide), vj a ha, vj b hb] at heq
  refine ⟨by rw [hvo]; exact hlt, by rw [hvo]; exact heq, fun x hx => ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide), ?_⟩
  · by_cases hr : 8 * sFn 0 ≤ ofs B x ∧ ofs B x < 8 * sFn 0 + 48
    · exact in₃ x hr.1 hr.2
    by_cases hb : 8 * sFn 12 ≤ ofs B x ∧ ofs B x < 8 * sFn 12 + 32
    · exact inb₃ x hb.1 hb.2
    obtain hb' : ofs B x < 8 * sFn 12 ∨ 8 * sFn 12 + 32 ≤ ofs B x := by omega_arith
    rw [o₃ x (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> simp only [] <;> omega_arith), har x hx, omb x hb',
      ho₁ x (by rw [hxO]; unfold sFn at *; omega_arith)]
  · exact rs

end VG.Proof.Bignum.X86_64

end

end

/-!
# `vg_rsa_mont_mul_adx`: constant time

After `zext`, for public indices (`AdxIn`): the head is checked by the taint
analysis from `rdi` and the indices; the size test and the choice of tiles
are taken alike in both runs because `w` and the indices are public; the
tiles are constant time for the slots the head wrote (`Ops`), and the
baseline's rounds from the bases; the tail addresses only from `rdi`, which
no instruction of the body writes.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The public data of a call: the working space, its size, `w` and the indices. -/
structure CallData where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  a : Nat
  b : Nat

/-- Indices of operands: arrays, not the function's own. -/
def Opnds (o a b : Nat) : Prop :=
  o < 8 ∧ a < 8 ∧ b < 8 ∧ o ≠ aAcc ∧ o ≠ aTmp ∧ a ≠ aAcc ∧ a ≠ aTmp ∧ b ≠ aAcc ∧ b ≠ aTmp

/-- After `zext`: the working space and its header, and the indices in
`rdx`, `rcx` and `r8`. -/
def AdxIn (d : CallData) (s : State) : Prop :=
  Scr s d.B d.Z ∧ s.gpr .rdi = d.B ∧ (∃ mi, Hdr s.mem d.B d.w mi) ∧ slot d.w 8 ≤ d.Z ∧ Opnds d.o d.a d.b ∧
    s.gpr .rdx = BitVec.ofNat 64 d.o ∧ s.gpr .rcx = BitVec.ofNat 64 d.a ∧ s.gpr .r8 = BitVec.ofNat 64 d.b

/-- After the head: also the operands' slots. -/
def AdxMid (d : CallData) (s : State) : Prop := AdxIn d s ∧ Ops s.mem d.B d.w (adxOps d.o d.a d.b)

theorem pins_adxIn : Pins AdxIn [.rdi, .rdx, .rcx, .r8] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, a₁, -, -, -, b₁, c₁, d₁⟩ := h₁
  obtain ⟨-, a₂, -, -, -, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

theorem pins_adxMid : Pins AdxMid [.rdi, .rdx, .rcx, .r8] :=
  fun d s₁ s₂ h₁ h₂ => pins_adxIn d s₁ s₂ h₁.1 h₂.1

theorem AdxIn.of_keep {d : CallData} {s t : State} (h : AdxIn d s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hcx' : t.gpr .rcx = s.gpr .rcx) (hr : Reg.rdi ∉ rs ∧ Reg.rdx ∉ rs ∧ Reg.r8 ∉ rs) :
    AdxIn d t := by
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, op, hdx, hcx, h8⟩ := h
  exact ⟨hs.congr k.2.2, (k.gpr hr.1).trans hdi, ⟨mi, hm ▸ hH⟩, hZ, op, (k.gpr hr.2.1).trans hdx,
    hcx'.trans hcx, (k.gpr hr.2.2).trans h8⟩

/-- The tiled code, for a layout the size test admits. -/
def adxLayout (d : CallData) (hZ : slot d.w 8 ≤ d.Z) (h : AlignOk d.w) : AdxTiledProduct.Layout :=
  ⟨d.B, d.Z, d.w, d.w / 8, hZ, by unfold AlignOk at h; omega_using [h], by unfold AlignOk at h; omega_using [h],
    by unfold AlignOk at h; omega_using [h]⟩

theorem goodV_of_mid {d : CallData} {s : State} (h : AdxMid d s) (hZ : slot d.w 8 ≤ d.Z) (hA : AlignOk d.w) :
    AdxTiledProduct.GoodV (adxOps d.o d.a d.b) (adxLayout d hZ hA) s := by
  obtain ⟨⟨hs, hdi, ⟨mi, hH⟩, -⟩, hv⟩ := h
  exact ⟨⟨mi, hs, hdi, hH⟩, hv⟩

/-- The public data of a call the tiles take. -/
abbrev TiledData := {d : CallData // slot d.w 8 ≤ d.Z ∧ AlignOk d.w}

/-- Between the tiles and the reduction: the layout and the operands' slots. -/
def TiledMid (x : TiledData) (s : State) : Prop :=
  AdxTiledProduct.GoodV (adxOps x.1.o x.1.a x.1.b) (adxLayout x.1 x.2.1 x.2.2) s

/-- The tiles. -/
theorem tiled_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some true) tiled fun _ _ => True := by
  unfold tiled
  refine RelCT.seq (two_piece (Ψ := fun d s => (AdxMid d s ∧ AlignOk d.w) ∧ s.zf = some (decide (d.a = d.b)))
    [.rcx, .r8] (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by taint_decide) ?_) ?_
  · rintro d s ⟨⟨hm, hz⟩, he⟩
    have hA : AlignOk d.w := by simpa only [eval, hz, Option.some.injEq, decide_eq_true_eq] using he
    have ha := hm.1.2.2.2.2.1.2.1
    have hb := hm.1.2.2.2.2.1.2.2.1
    have hcx := hm.1.2.2.2.2.2.2.1
    have h8 := hm.1.2.2.2.2.2.2.2
    exact WP.mono (cmpIdx_ok ha hb hcx h8) fun t ⟨hz', hm', hc', k⟩ =>
      ⟨⟨⟨AdxIn.of_keep hm.1 hm' k hc' (by decide), hm' ▸ hm.2⟩, hA⟩, hz'⟩
  refine RelCT.seq (R := Two TiledMid)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    (AdxTiledProduct.redcFinish_ct (P := fun x : TiledData => adxOps x.1.o x.1.a x.1.b)
      (L := fun x => adxLayout x.1 x.2.1 x.2.2) (O := fun x => x.1.o) (fun x => mem_adxOps_o _ _ _)
      (by taint_decide))
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, z₁⟩, e₁⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hab : d.a = d.b := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, -, -, -, ha1, ha2, -⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledSquare.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) ha ha1 ha2
          (by taint_decide) (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledSquare.rawBare_fw (mem_adxOps_a _ _ _) ha ha1 ha2 (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, -⟩, -⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, hb, -, -, ha1, ha2, hb1, hb2⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledProduct.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb
          ha1 ha2 hb1 hb2 (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledProduct.rawBare_fw (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb ha1 ha2 hb1 hb2
        (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩

/-- `montMul`, from the bases `basesR` loads. -/
theorem fallback_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some false)
    (.seq (.block basesR) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))) fun _ _ => True := by
  refine RelCT.seq (two_piece (Ψ := fun d => BasesL aN aAcc aTmp d.o d.a d.b ⟨d.B, d.Z, d.w⟩) [.rdi, .rdx, .rcx, .r8]
    (fun d s₁ s₂ h₁ h₂ => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) ?_)
    (two_taint _ (fun d => pins_bases aN aAcc aTmp d.o d.a d.b ⟨d.B, d.Z, d.w⟩) (by taint_decide))
  rintro d s ⟨⟨⟨⟨hs, hdi, ⟨mi, hH⟩, hZ, ⟨ho, ha, hb, -⟩, hdx, hcx, h8⟩, -⟩, -⟩, -⟩
  exact WP.mono (basesR_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun t ⟨u1, u2, u3, u4, u5, u6, _, u8, _⟩ =>
    ⟨u1, u2, u3, u4, u5, u6, u8⟩

theorem adxBody_ct : RelCT isa (Two AdxMid) adxBody fun _ _ => True := by
  unfold adxBody
  refine RelCT.seq (two_piece (Ψ := fun d s => AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) [.rdi]
    (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])) (by taint_decide) ?_)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) tiled_ct fallback_ct)
  rintro d s ⟨hm, hv⟩
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, -⟩ := id hm
  exact WP.mono (alignTest_ok hs hdi hH hZ) fun t ⟨hz, hm', k⟩ =>
    ⟨⟨AdxIn.of_keep hm hm' k (k.gpr (by decide)) (by decide), hm' ▸ hv⟩, hz⟩

/-- A relation after code that never writes `rdi`. -/
theorem RelCT.keepRdi {α : Type} {Φ : α → State → Prop} {c : Prog isa} {f : α → Addr}
    (h : RelCT isa (Two Φ) c fun _ _ => True) (hc : (instrs c).all (fun i => !Taint.clobbers i .rdi) = true)
    (hΦ : ∀ a s, Φ a s → s.gpr .rdi = f a) : RelCT isa (Two Φ) c (Two fun a s => s.gpr .rdi = f a) := by
  have hc' : ∀ i ∈ instrs c, Taint.clobbers i .rdi = false := fun i hi => by
    simpa using List.all_eq_true.mp hc i hi
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, h₁, h₂⟩ e₁ e₂
  exact ⟨(h _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂).1, a, (Exec.gpr hc' e₁).trans (hΦ a _ h₁),
    (Exec.gpr hc' e₂).trans (hΦ a _ h₂)⟩

/-- `vg_rsa_mont_mul_adx` after the head. -/
theorem adxTail_ct : RelCT isa (Two AdxMid) (.seq adxBody (.block restore)) fun _ _ => True :=
  RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBody_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
    fun _ _ h => h.1.2.1)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

/-- After the head, from `enter ++ slotsIn`. -/
theorem AdxMid.of_head {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat} (op : Opnds o a b)
    (hm : t.mem = headMem s.mem B w o a b) (hdx : t.gpr .rdx = BitVec.ofNat 64 o)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 a) (h8 : t.gpr .r8 = BitVec.ofNat 64 b)
    (k : Keep [.rdx, .rcx, .r8, .rax] s t) : AdxMid ⟨B, Z, w, o, a, b⟩ t :=
  ⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ⟨minv, hm ▸ headMem_hdr hH _ _ _⟩, hZ, op, hdx, hcx, h8⟩,
    hm ▸ headMem_ops _ _ _ _ _ _⟩

end VG.Proof.Bignum.X86_64

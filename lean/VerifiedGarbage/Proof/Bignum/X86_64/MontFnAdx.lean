import VerifiedGarbage.Impl.Bignum.X86_64.MontFnAdx
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend

/-!
# `vg_rsa_mont_mul_adx`: correctness

The head (`enter`, `slotsIn`) saves the callee-saved registers and header
words 16–19 in `xmm0`–`xmm4` and writes the bases of `o`, `a` and `b` into
the slots of `xO`, `xA` and `xB` (`Ops`); the body runs the tiled ADX code
for those slots (`AdxTiledSquare.montSquare_ok`, `AdxTiledProduct.montMul_ok`)
or, for `w` not a multiple of 8, `montMul` (`mmTail_ok`); the tail writes the
header words back, so that only `aAcc`, `aTmp` and `o` change, and restores
the callee-saved registers (`fnLeave_ok`).
-/

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
  xrun [hdx, hcx, h8, setWidth_ofNat32 (show o < 2 ^ 32 by omega), setWidth_ofNat32 (show a < 2 ^ 32 by omega),
    setWidth_ofNat32 (show b < 2 ^ 32 by omega), setReg_xmm]

/-- `saves` and `slotsIn`, with the indices zero-extended. -/
theorem adxRest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : s.gpr .rdx = BitVec.ofNat 64 o)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 a) (h8 : s.gpr .r8 = BitVec.ofNat 64 b) :
    WP isa (.block (saves ++ slotsIn)) s fun t =>
      t.mem = headMem s.mem B w o a b ∧ Keep [.rax] s t ∧
      t.xmm .xmm0 = s.gpr .rbp ++ s.gpr .rbx ∧ t.xmm .xmm1 = s.gpr .r13 ++ s.gpr .r12 ∧
      t.xmm .xmm2 = s.gpr .r15 ++ s.gpr .r14 ∧ t.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      t.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ t.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128 := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega)
  have hl16 : ∀ i < 31, InRegions (s.rd ++ s.wr) (off B (8 * i)) 16 := fun i hi =>
    let ⟨r, hm, hc⟩ := hs.region (d := 8 * i) (n := 16) (by have := hdr_lt_slot w 8 (show i + 1 < 32 by omega); omega)
      (by decide)
    ⟨r, List.mem_append_right _ hm, hc⟩
  refine WP.mono (WP.keep [.rax] (c := .block (saves ++ slotsIn))
    (Q := fun t => t.mem = headMem s.mem B w o a b ∧
      t.xmm .xmm0 = s.gpr .rbp ++ s.gpr .rbx ∧ t.xmm .xmm1 = s.gpr .r13 ++ s.gpr .r12 ∧
      t.xmm .xmm2 = s.gpr .r15 ++ s.gpr .r14 ∧ t.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      t.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ t.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, k, h.2⟩
  unfold saves slotsIn
  simp only [List.cons_append, List.nil_append]
  xrun [XOp.exec, setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, setXmm_xmm, setReg_xmm, XBinOp.eval, qword_movq,
    State.ea, State.load128, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off64 B (show o < 2 ^ 32 by omega),
    arr_off64 B (show a < 2 ^ 32 by omega), arr_off64 B (show b < 2 ^ 32 by omega),
    hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega), hl (sArr b) (by unfold sArr; omega),
    hw (sArr xO) (by decide), hw (sArr xA) (by decide), hw (sArr xB) (by decide),
    hl16 (sFn 0) (by decide), hl16 (sFn 2) (by decide), hl16 (sFn 4) (by decide), hH.harr o ho]
  have hn := hs.nowrap
  have o₁ := writeW_outside s.mem B (d := 8 * sArr xO) (off B (slot w o)) (by unfold sArr xO; omega)
  have o₂ := writeW_outside (s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega)
  have ra : (s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))).readW (off B (8 * sArr a)) 64 =
      off B (slot w a) :=
    (o₁.word (by unfold sArr xO; omega) (by unfold sArr; omega)).trans (hH.harr a ha)
  have rb : ((s.mem.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
      (off B (slot w a))).readW (off B (8 * sArr b)) 64 = off B (slot w b) :=
    ((o₂.word (by unfold sArr xA; omega) (by unfold sArr; omega)).trans
      (o₁.word (by unfold sArr xO; omega) (by unfold sArr; omega))).trans (hH.harr b hb)
  rw [ra, rb]; rfl

/-! ## The size test -/

/-- What `alignTest` tests: the tiles apply. -/
def AlignOk (w : Nat) : Prop := w % 8 = 0 ∧ 8 ≤ w ∧ w < 2 ^ 30 + 8

instance (w : Nat) : Decidable (AlignOk w) := inferInstanceAs (Decidable (_ ∧ _))

theorem rotr3_toNat (x : BitVec 64) : (x.rotateRight 3).toNat = x.toNat / 8 + x.toNat % 8 * 2 ^ 61 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reduceSub]
  have hx := x.isLt
  rw [Nat.shiftLeft_eq, show x.toNat * 2 ^ 61 % 2 ^ 64 = (x.toNat % 8) <<< 61 by rw [Nat.shiftLeft_eq]; omega,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem alignTest_beq (w : Nat) (hw : w < 2 ^ 64) :
    ((BitVec.ofNat 64 w - 8).rotateRight 3 >>> 27 == 0) = decide (AlignOk w) := by
  have h : ((BitVec.ofNat 64 w - 8).rotateRight 3 >>> 27).toNat =
      ((2 ^ 64 - 8 + w) % 2 ^ 64 / 8 + (2 ^ 64 - 8 + w) % 2 ^ 64 % 8 * 2 ^ 61) / 2 ^ 27 := by
    rw [BitVec.toNat_ushiftRight, rotr3_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (8 : BitVec 64).toNat = 8 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  generalize hv : (2 ^ 64 - 8 + w) % 2 ^ 64 = v at h
  have h1 : v % 8 = w % 8 := by omega
  have h3 : 8 ≤ w → v = w - 8 := by omega
  have h4 : w < 8 → v = 2 ^ 64 - 8 + w := by omega
  unfold AlignOk
  by_cases h0 : w % 8 = 0 ∧ 8 ≤ w ∧ w < 2 ^ 30 + 8
  · simp only [h0, and_self, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; have := congrArg BitVec.toNat he; rw [h, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega

/-- `alignTest`: ZF set when the tiles apply. -/
theorem alignTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block alignTest) s fun t => t.zf = some (decide (AlignOk w)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (AlignOk w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold alignTest
  xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    hH.hw, alignTest_beq w (by unfold slot hdrBytes at hZ; omega)]

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
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] (c := .block basesR)
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w aTmp) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩
  unfold basesR
  xrun [State.ea, arrAt, hdr, hdi, hdx, hcx, h8, hdrOff, arr_off64 B (show o < 2 ^ 32 by omega),
    arr_off64 B (show a < 2 ^ 32 by omega), arr_off64 B (show b < 2 ^ 32 by omega),
    hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega), hl (sArr b) (by unfold sArr; omega),
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
  xrun [hcx, h8, ofNat_sub_beq (show a < 2 ^ 64 by omega) (show b < 2 ^ 64 by omega)]

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
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold adxBody
  refine WP.seq (WP.mono (alignTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH hv ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8w : AlignOk w
  · refine WP.ite true (by simp [eval, hz, h8w]) (fun _ => ?_) (by simp)
    obtain ⟨h8w, h8w', -⟩ := h8w
    unfold tiled
    have hcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 a := (k₁.gpr (by decide)).trans hcx
    have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 b := (k₁.gpr (by decide)).trans h8
    refine WP.seq (WP.mono (cmpIdx_ok ha hb hcx₁ h8₁) fun s₂ ⟨hz₂, hm₂, _, k₂⟩ => ?_)
    have hs₂ := hs₁.congr k₂.2.2
    have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
    rw [← hm₂] at hinv hB hH hv ⊢
    have post₂ : ∀ t, (wv t.mem B (slot w o) w < wv s₂.mem B (slot w aN) w ∧
        wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₂.mem B (slot w aN) w =
          wv s₂.mem B (slot w a) w * wv s₂.mem B (slot w b) w % wv s₂.mem B (slot w aN) w ∧
        Arrays B w [aAcc, aTmp, o] s₂.mem t.mem ∧ Keep mmRegs s₂ t) →
        (wv t.mem B (slot w o) w < wv s₂.mem B (slot w aN) w ∧
        wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₂.mem B (slot w aN) w =
          wv s₂.mem B (slot w a) w * wv s₂.mem B (slot w b) w % wv s₂.mem B (slot w aN) w ∧
        Arrays B w [aAcc, aTmp, o] s₂.mem t.mem ∧ Keep mmRegs s t) :=
      fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, ((k₁.trans k₂).trans k).mono (by decide)⟩
    by_cases hab : a = b
    · subst b
      refine WP.ite true (by simp [eval, hz₂]) (fun _ => WP.mono
        (AdxTiledSquare.montSquare_ok hs₂ hdi₂ hH hZ (by omega : w = 8 * (w / 8)) (by omega) hw' hv
          (mem_adxOps_o o a a) (mem_adxOps_a o a a) ho ha ho1 ho2 ha1 ha2 hinv hB) post₂) (by simp)
    · refine WP.ite false (by simp [eval, hz₂, hab]) (by simp) (fun _ => WP.mono
        (AdxTiledProduct.montMul_ok hs₂ hdi₂ hH hZ (by omega : w = 8 * (w / 8)) (by omega) hw' hv
          (mem_adxOps_o o a b) (mem_adxOps_a o a b) (mem_adxOps_b o a b) ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB)
        post₂)
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
  have o₁ := writeW_outside m B (d := 8 * sArr xO) (off B (slot w o)) (by unfold sArr xO; omega)
  have o₂ := writeW_outside (m.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega)
  have o₃ := writeW_outside ((m.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
    (off B (slot w a))) B (d := 8 * sArr xB) (off B (slot w b)) (by unfold sArr xB; omega)
  exact ((o₁.mono (by decide) (by decide)).trans (o₂.mono (by decide) (by decide))).trans
    (o₃.mono (by decide) (by decide))

theorem headMem_hdr {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) (o a b : Nat) :
    Hdr (headMem m B w o a b) B w minv :=
  ((hH.store (i := sArr xO) (by decide) (by decide) _).store (i := sArr xA) (by decide) (by decide) _).store
    (i := sArr xB) (by decide) (by decide) _

theorem headMem_ops (m : Mem) (B : Addr) (w o a b : Nat) : Ops (headMem m B w o a b) B w (adxOps o a b) := by
  have o₂ := writeW_outside ((m.writeW (off B (8 * sArr xO)) (off B (slot w o))).writeW (off B (8 * sArr xA))
    (off B (slot w a))) B (d := 8 * sArr xB) (off B (slot w b)) (by unfold sArr xB; omega)
  have o₁ := writeW_outside (m.writeW (off B (8 * sArr xO)) (off B (slot w o))) B (d := 8 * sArr xA)
    (off B (slot w a)) (by unfold sArr xA; omega)
  intro p hp
  simp only [adxOps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨show xO < 20 by decide, ?_⟩
    unfold OpAt headMem
    rw [o₂.word (by unfold sArr xO xB; omega) (by unfold sArr xO; omega),
      o₁.word (by unfold sArr xO xA; omega) (by unfold sArr xO; omega), word_writeW_self]
  · refine ⟨show xA < 20 by decide, ?_⟩
    unfold OpAt headMem
    rw [o₂.word (by unfold sArr xA xB; omega) (by unfold sArr xA; omega), word_writeW_self]
  · exact ⟨show xB < 20 by decide, word_writeW_self _ _ _ _⟩

/-- Writing back 16 bytes read before restores them. -/
theorem write_restore (m m₀ : Mem) (B : Addr) {d : Nat} (hd : d + 16 < 2 ^ 64) {x : Addr} (hx : d ≤ ofs B x)
    (hx' : ofs B x < d + 16) : (m.writeW (off B d) (m₀.readW (off B d) 128)) x = m₀ x := by
  have e : (x - off B d).toNat = ofs B x - d := by
    unfold ofs off at *; rw [Offset.toNat_sub_add x B (by omega)]; have := (x - B).isLt; omega
  simp only [Mem.writeW, Mem.readW, Mem.write]
  simp only [show (x - off B d).toNat < 128 / 8 by omega, ite_true]
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read m₀ _ (by omega)]
  congr 1
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- `restore`: the callee-saved registers from `xmm0`–`xmm2`, and header words
16–21 as `m₀` has them, from `xmm3`–`xmm5`. -/
theorem restore_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {m₀ : Mem} (h3 : s.xmm .xmm3 = m₀.readW (off B (8 * sFn 0)) 128)
    (h4 : s.xmm .xmm4 = m₀.readW (off B (8 * sFn 2)) 128) (h5 : s.xmm .xmm5 = m₀.readW (off B (8 * sFn 4)) 128) :
    WP isa (.block restore) s fun t =>
      t.gpr .rbx = (s.xmm .xmm0).extractLsb' 0 64 ∧ t.gpr .rbp = (s.xmm .xmm0).extractLsb' 64 64 ∧
      t.gpr .r12 = (s.xmm .xmm1).extractLsb' 0 64 ∧ t.gpr .r13 = (s.xmm .xmm1).extractLsb' 64 64 ∧
      t.gpr .r14 = (s.xmm .xmm2).extractLsb' 0 64 ∧ t.gpr .r15 = (s.xmm .xmm2).extractLsb' 64 64 ∧
      Outside B (8 * sFn 0) 48 s.mem t.mem ∧
      (∀ x, 8 * sFn 0 ≤ ofs B x → ofs B x < 8 * sFn 0 + 48 → t.mem x = m₀ x) ∧
      Keep [.rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hw16 : ∀ i < 31, InRegions s.wr (off B (8 * i)) 16 := fun i hi =>
    let ⟨r, hm, hc⟩ := hs.region (d := 8 * i) (n := 16) (by omega) (by decide)
    ⟨r, hm, hc⟩
  let m₁ := ((s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm0)).writeW (off B (8 * sFn 2)) (s.xmm .xmm1)).writeW
    (off B (8 * sFn 4)) (s.xmm .xmm2)
  let m₂ := ((m₁.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2)) (s.xmm .xmm4)).writeW
    (off B (8 * sFn 4)) (s.xmm .xmm5)
  have sep : ∀ {d e : Nat}, d + 8 ≤ e ∨ e + 16 ≤ d → d + 8 ≤ 2 ^ 64 → e + 16 ≤ 2 ^ 64 →
      Mem.Sep (off B d) (64 / 8) (off B e) (128 / 8) := fun h h₁ h₂ => Offset.sep B h h₁ h₂
  have r₀ : m₁.readW (off B (8 * sFn 0)) 64 = (s.xmm .xmm0).extractLsb' 0 64 := by
    simp only [m₁]
    rw [Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      word_lo128]
  have r₁ : m₁.readW (off B (8 * sFn 1)) 64 = (s.xmm .xmm0).extractLsb' 64 64 := by
    simp only [m₁]
    rw [Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      show 8 * sFn 1 = 8 * sFn 0 + 8 from rfl, word_hi128]
  have r₂ : m₁.readW (off B (8 * sFn 2)) 64 = (s.xmm .xmm1).extractLsb' 0 64 := by
    simp only [m₁]
    rw [Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      word_lo128]
  have r₃ : m₁.readW (off B (8 * sFn 3)) 64 = (s.xmm .xmm1).extractLsb' 64 64 := by
    simp only [m₁]
    rw [Mem.readW_writeW_sep (sep (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn; omega)) (by decide),
      show 8 * sFn 3 = 8 * sFn 2 + 8 from rfl, word_hi128]
  have r₄ : m₁.readW (off B (8 * sFn 4)) 64 = (s.xmm .xmm2).extractLsb' 0 64 := word_lo128 _ _ _ _
  have r₅ : m₁.readW (off B (8 * sFn 5)) 64 = (s.xmm .xmm2).extractLsb' 64 64 := by
    rw [show 8 * sFn 5 = 8 * sFn 4 + 8 from rfl]; exact word_hi128 _ _ _ _
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (c := .block restore)
    (Q := fun t => t.gpr .rbx = (s.xmm .xmm0).extractLsb' 0 64 ∧ t.gpr .rbp = (s.xmm .xmm0).extractLsb' 64 64 ∧
      t.gpr .r12 = (s.xmm .xmm1).extractLsb' 0 64 ∧ t.gpr .r13 = (s.xmm .xmm1).extractLsb' 64 64 ∧
      t.gpr .r14 = (s.xmm .xmm2).extractLsb' 0 64 ∧ t.gpr .r15 = (s.xmm .xmm2).extractLsb' 64 64 ∧
      t.mem = m₂) ?_ rfl) fun t ⟨⟨h1, h2, h3', h4', h5', h6, hm⟩, k⟩ => ⟨h1, h2, h3', h4', h5', h6, ?_, ?_, k⟩
  · unfold restore
    xrun [State.ea, State.store128, hdr, hdi, hdrOff, hw16 (sFn 0) (by decide), hw16 (sFn 2) (by decide),
      hw16 (sFn 4) (by decide), hl (sFn 0) (by decide), hl (sFn 1) (by decide), hl (sFn 2) (by decide),
      hl (sFn 3) (by decide), hl (sFn 4) (by decide), hl (sFn 5) (by decide), setReg_xmm]
    exact ⟨r₀, r₁, r₂, r₃, r₄, r₅, rfl⟩
  · rw [hm]
    have w₀ := writeW_outsideN s.mem B (d := 8 * sFn 0) (s.xmm .xmm0) (by unfold sFn; omega) (by decide)
    have w₁ := writeW_outsideN (s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm0)) B (d := 8 * sFn 2) (s.xmm .xmm1)
      (by unfold sFn; omega) (by decide)
    have w₂ := writeW_outsideN ((s.mem.writeW (off B (8 * sFn 0)) (s.xmm .xmm0)).writeW (off B (8 * sFn 2))
      (s.xmm .xmm1)) B (d := 8 * sFn 4) (s.xmm .xmm2) (by unfold sFn; omega) (by decide)
    have w₃ := writeW_outsideN m₁ B (d := 8 * sFn 0) (s.xmm .xmm3) (by unfold sFn; omega) (by decide)
    have w₄ := writeW_outsideN (m₁.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)) B (d := 8 * sFn 2) (s.xmm .xmm4)
      (by unfold sFn; omega) (by decide)
    have w₅ := writeW_outsideN ((m₁.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2))
      (s.xmm .xmm4)) B (d := 8 * sFn 4) (s.xmm .xmm5) (by unfold sFn; omega) (by decide)
    exact (((((w₀.mono (by decide) (by decide)).trans (w₁.mono (by decide) (by decide))).trans
      (w₂.mono (by decide) (by decide))).trans (w₃.mono (by decide) (by decide))).trans
      (w₄.mono (by decide) (by decide))).trans (w₅.mono (by decide) (by decide))
  · intro x hx hx'
    rw [hm]
    dsimp only [m₂]
    have w₄ := writeW_outsideN (m₁.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)) B (d := 8 * sFn 2) (s.xmm .xmm4)
      (by unfold sFn; omega) (by decide)
    have w₅ := writeW_outsideN ((m₁.writeW (off B (8 * sFn 0)) (s.xmm .xmm3)).writeW (off B (8 * sFn 2))
      (s.xmm .xmm4)) B (d := 8 * sFn 4) (s.xmm .xmm5) (by unfold sFn; omega) (by decide)
    unfold sFn at hx hx'
    by_cases c₅ : 8 * sFn 4 ≤ ofs B x
    · rw [h5]; exact write_restore _ _ B (by unfold sFn; omega) c₅ (by unfold sFn at *; omega)
    rw [w₅ x (Or.inl (by omega))]
    by_cases c₄ : 8 * sFn 2 ≤ ofs B x
    · rw [h4]; exact write_restore _ _ B (by unfold sFn; omega) c₄ (by unfold sFn at *; omega)
    rw [w₄ x (Or.inl (by omega)), h3]
    exact write_restore _ _ B (by unfold sFn; omega) (by unfold sFn; omega) (by unfold sFn at *; omega)

/-- `enter` and `slotsIn`. -/
theorem adxHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block (enter ++ slotsIn)) s fun s₁ =>
      s₁.mem = headMem s.mem B w o a b ∧ s₁.gpr .rdx = BitVec.ofNat 64 o ∧
      s₁.gpr .rcx = BitVec.ofNat 64 a ∧ s₁.gpr .r8 = BitVec.ofNat 64 b ∧
      Keep [.rdx, .rcx, .r8, .rax] s s₁ ∧
      s₁.xmm .xmm0 = s.gpr .rbp ++ s.gpr .rbx ∧ s₁.xmm .xmm1 = s.gpr .r13 ++ s.gpr .r12 ∧
      s₁.xmm .xmm2 = s.gpr .r15 ++ s.gpr .r14 ∧ s₁.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128 ∧
      s₁.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128 ∧ s₁.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128 := by
  rw [show enter ++ slotsIn = zext ++ (saves ++ slotsIn) from by simp [enter], WP.block_append_iff]
  refine WP.mono (zextIdx_ok ho ha hb hdx hcx h8) fun s₀ ⟨hdx₀, hcx₀, h8₀, hm₀, _, k₀⟩ => ?_
  refine WP.mono (adxRest_ok (hs.congr k₀.2.2) ((k₀.gpr (by decide)).trans hdi) (hm₀ ▸ hH) hZ ho ha hb hdx₀
    hcx₀ h8₀) fun s₁ ⟨hm₁, k₁, x0, x1, x2, x3, x4, x5⟩ => ?_
  rw [hm₀] at hm₁ x3 x4 x5
  refine ⟨hm₁, (k₁.gpr (by decide)).trans hdx₀, (k₁.gpr (by decide)).trans hcx₀,
    (k₁.gpr (by decide)).trans h8₀, (k₀.trans k₁).mono (by decide), ?_, ?_, ?_, x3, x4, x5⟩
  · rw [x0, k₀.gpr (by decide), k₀.gpr (by decide)]
  · rw [x1, k₀.gpr (by decide), k₀.gpr (by decide)]
  · rw [x2, k₀.gpr (by decide), k₀.gpr (by decide)]

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
  have h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega
  have hxO : 8 * sArr xO = 8 * sFn 0 := rfl
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega
  have hZ32 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 0 (show 31 < 32 by decide); have := sl 0 (by decide); omega
  unfold mulAdx
  refine WP.seq (WP.mono (adxHead_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun s₁ ⟨hm₁, hdx₁, hcx₁, h8₁, k₁, x0, x1, x2, x3, x4, x5⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  have ho₁ : Outside B (8 * sArr xO) 24 s.mem s₁.mem := hm₁ ▸ headMem_outside s.mem B w o a b
  have vj : ∀ j < 8, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj =>
    ho₁.wv (by have := s0 j; omega) (by have := sl j hj; omega)
  have hinv₁ : ((word s₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho₁.word (by have := s0 aN; omega) (by have := sl aN (by decide); omega)]; exact hinv
  have hB₁ : wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w := by
    rw [vj b hb, vj aN (by decide)]; exact hB
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (adxBody_ok hs₁ hdi₁ (hm₁ ▸ headMem_hdr hH o a b) hZ hw hw' ho
    ha hb ho1 ho2 ha1 ha2 hb1 hb2 (hm₁ ▸ headMem_ops s.mem B w o a b) hdx₁ hcx₁ h8₁ hinv₁ hB₁))
    fun s₂ ⟨⟨hlt, heq, har, k₂⟩, hx₂, _⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (restore_ok hs₂ hdi₂ hZ32 (m₀ := s.mem) (by rw [hx₂, x3]) (by rw [hx₂, x4]) (by rw [hx₂, x5]))
    fun t ⟨r1, r2, r3, r4, r5, r6, o₃, in₃, k₃⟩ => ?_
  have hvo : wv t.mem B (slot w o) w = wv s₂.mem B (slot w o) w :=
    o₃.wv (by have := s0 o; omega) (by have := sl o ho; omega)
  rw [vj aN (by decide)] at hlt
  rw [vj aN (by decide), vj a ha, vj b hb] at heq
  refine ⟨by rw [hvo]; exact hlt, by rw [hvo]; exact heq, fun x hx => ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide), ?_⟩
  · by_cases hr : 8 * sFn 0 ≤ ofs B x ∧ ofs B x < 8 * sFn 0 + 48
    · exact in₃ x hr.1 hr.2
    · have hr' : ofs B x < 8 * sFn 0 ∨ 8 * sFn 0 + 48 ≤ ofs B x := by omega
      rw [o₃ x hr', har x hx, ho₁ x (by rw [hxO]; omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [r1, hx₂, x0, fnExtract_lo]
    · rw [r2, hx₂, x0, fnExtract_hi]
    · rw [r3, hx₂, x1, fnExtract_lo]
    · rw [r4, hx₂, x1, fnExtract_hi]
    · rw [r5, hx₂, x2, fnExtract_lo]
    · rw [r6, hx₂, x2, fnExtract_hi]

end VG.Proof.Bignum.X86_64

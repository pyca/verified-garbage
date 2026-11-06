module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The blinded Miller–Rabin loop on RISC-V: a draw's witness

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/Witness.lean`), for the
draw `x` in array 4:

* `atLeast2_ok`: `a3 = 0` exactly when `x < 2`;
* `ltN_ok`: `s4` is all ones exactly when `(x | 1) < c` (`subMod64` of a
  copy of `x | 1` in array 3, `wv_or_one`, and `c` into array 6).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Proof.MillerRabin.RISCV64 (Env A shl3_w)
open VG.Proof.Bignum (slot Frm wv word off writeW_outside word_writeW_self)

/-- `x >> 1` is zero exactly when `x < 2`. -/
theorem shr1_eq_zero (x : BitVec 64) : x >>> 1 = 0#64 ↔ x.toNat < 2 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.pow_one]
  omega

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0#64 ↔ x = 0#64 ∧ y = 0#64 := by
  constructor
  · intro h
    have hx : x = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_or] at this
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this ⊢
      exact (Nat.or_eq_zero_iff.mp this).1
    subst hx
    rw [BitVec.zero_or] at h
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The registers `atLeast2` writes. -/
def a2Regs : List Reg := [.a3, .t2, .t3, .t5]

/-- `a3 = 0` exactly when the draw in array 4 is below 2. -/
theorem atLeast2_ok {s : State} {B : Addr} {Z w : Nat} (e : Env s B Z w) :
    WP isa atLeast2 s fun t =>
      ((t.gpr .a3 = 0#64 ↔ A s.mem B w 4 < 2) ∧ t.mem = s.mem) ∧ Keep a2Regs s t := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : slot w 4 = 256 + 4 * (8 * (w + 2)) := rfl
  unfold atLeast2
  refine WP.seq (WP.mono (WP.keep [.t3, .t5, .a3] (Q := fun u => u.gpr .a3 = word s.mem B (slot w 4) >>> 1 ∧
      u.gpr .t3 = off B (slot w 4 + 8) ∧ u.gpr .t5 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨u3, ut3, u5, um⟩, ku⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (e.base (rd := .t3) (by decide) 4) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_
    have v0 : v.gpr .t0 = BitVec.ofNat 64 w := (kv.gpr (by decide)).trans e.t0
    have hv : Scr v B Z := hs.congr kv.2.2
    have ew : BitVec.ofNat 64 w - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    brun [v3, v0, vm, hv.ld (d := slot w 4) (n := 8) (by omega), hv.al8 (d := slot w 4) (by omega) (by omega),
      BitVec.add_zero, ew]
  let Inv : Nat → State → Prop := fun j v =>
    (v.gpr .t3 = off B (slot w 4 + 8 * (j + 1)) ∧
      (v.gpr .a3 = 0#64 ↔ (word s.mem B (slot w 4)).toNat < 2 ∧
        ∀ i, 1 ≤ i → i ≤ j → word s.mem B (slot w 4 + 8 * i) = 0#64) ∧ v.mem = s.mem) ∧ Keep a2Regs s v
  refine WP.mono (wp_countdown (cnt := .t5) (N := w - 1) (by omega) (by omega) Inv
    (fun j hj v ⟨⟨vt3, v3, vm⟩, kv⟩ _ => ?_)
    ⟨⟨by rw [ut3, Nat.zero_add, Nat.mul_one], by rw [u3, shr1_eq_zero]; exact ⟨fun h => ⟨h, fun i h1 h2 => by omega⟩,
      fun h => h.1⟩, um⟩, ku.mono (by decide)⟩ u5) fun t ⟨⟨_, t3, tm⟩, kt⟩ => ⟨⟨?_, tm⟩, kt⟩
  · have hv : Scr v B Z := hs.congr kv.2.2
    have ha : slot w 4 + 8 * (j + 1) + 8 ≤ Z := by omega
    refine WP.mono (WP.keep [.t2, .t3, .a3, .t5] (Q := fun x =>
        x.gpr .a3 = v.gpr .a3 ||| word s.mem B (slot w 4 + 8 * (j + 1)) ∧
        x.gpr .t3 = off B (slot w 4 + 8 * (j + 2)) ∧ x.gpr .t5 = v.gpr .t5 - BitVec.ofNat 64 1 ∧ x.mem = s.mem) (by
          brun [vt3, vm, hv.ld (d := slot w 4 + 8 * (j + 1)) (n := 8) ha,
            hv.al8 (d := slot w 4 + 8 * (j + 1)) ha (by omega), BitVec.add_zero]
          rw [show slot w 4 + 8 * (j + 1) + 8 = slot w 4 + 8 * (j + 2) by omega]) (by rfl) (by rfl))
      fun x ⟨⟨x3, xt3, x5, xm⟩, kx⟩ => ?_
    refine ⟨⟨⟨xt3, ?_, xm⟩, (kv.trans kx).mono (by decide)⟩, x5⟩
    rw [x3, or_eq_zero, v3]
    constructor
    · rintro ⟨⟨h0, hi⟩, hj1⟩
      exact ⟨h0, fun i h1 h2 => by
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hi i h1 (by omega)
        · rw [show i = j + 1 by omega]; exact hj1⟩
    · rintro ⟨h0, hi⟩
      exact ⟨⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩, hi (j + 1) (by omega) (by omega)⟩
  · simp only [A, Pre.wordsVal_eq_wv]
    rw [t3, VG.Proof.RsaKeyGen.wv_lt_two_iff s.mem B (slot w 4) (show 1 ≤ w by omega)]
    exact ⟨fun ⟨h0, hi⟩ => ⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩, fun ⟨h0, hi⟩ => ⟨h0, fun i h1 h2 => hi i h1 (by omega)⟩⟩

/-- The registers `ltNMid` writes. -/
def ltNMidRegs : List Reg := [.t2, .t3, .t4, .a5, .a6]

/-- The middle of `ltN`: `x | 1` in array 3, its word `w` zeroed, and `subMod64`'s bases. -/
theorem ltNMid_ok {v : State} {B : Addr} {Z w : Nat} (ev : Env v B Z w) :
    WP isa (.block (base .t3 3 ++ ([.load .d .t2 .t3 0, .logicImm .or .t2 .t2 1, .store .d .t2 .t3 0,
        .shift .sll .d .t4 .t0 3, .add .t3 .t3 .t4, .li .t2 0, .store .d .t2 .t3 0] : List Instr) ++ base .a5 3 ++
        base .a6 6))
      v fun x => (x.gpr .a5 = off B (slot w 3) ∧ x.gpr .a6 = off B (slot w 6) ∧
        x.mem = (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)).writeW
          (off B (slot w 3 + 8 * w)) 0#64) ∧ Keep ltNMidRegs v x := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := ev.hZ
  have hw4 := ev.hw
  have hw128 := ev.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ev.base (rd := .t3) (by decide) 3) fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
  have ey : Env y B Z w := ev.keep ky (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (z : State) => (z.mem = (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)).writeW
      (off B (slot w 3 + 8 * w)) 0#64) ∧ Keep [.t2, .t3, .t4] y z) (WP.keep _ ?_ (by rfl) (by rfl))
    fun z ⟨zm, kz⟩ => ?_
  · brun [y3, ym, ey.t0, ey.hs.ld (d := slot w 3) (n := 8) (by rw [es]; omega),
      ey.hs.al8 (d := slot w 3) (by rw [es]; omega) (by rw [es]; omega),
      ey.hs.st (d := slot w 3) (n := 8) (by rw [es]; omega),
      ey.hs.st (d := slot w 3 + 8 * w) (n := 8) (by rw [es]; omega),
      ey.hs.al8 (d := slot w 3 + 8 * w) (by rw [es]; omega) (by rw [es]; omega), BitVec.add_zero, shl3_w,
      exec_li (show imm12 0 by decide)]
  · have ez : Env z B Z w := ey.keep kz (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (ez.base (rd := .a5) (by decide) 3) fun a ⟨⟨a5, am⟩, ka⟩ => ?_
    refine WP.mono ((ez.keep ka (by decide)).base (rd := .a6) (by decide) 6) fun b ⟨⟨b6, bm⟩, kb⟩ => ?_
    exact ⟨(kb.gpr (by decide)).trans a5, b6, bm.trans (am.trans zm)⟩

/-- The registers `ltN` writes. -/
def ltNRegs : List Reg := [.a0, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .a5, .a6]

/-- `s4` is all ones exactly when `(x | 1) < c`, for the draw `x` in array 4. -/
theorem ltN_ok {s : State} {B : Addr} {Z w c : Nat} (e : Env s B Z w) (hc : A s.mem B w 0 = c) :
    WP isa ltN s fun t =>
      (t.gpr .s4 = (if (A s.mem B w 4 ||| 1) < c then BitVec.allOnes 64 else 0) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep ltNRegs s t := by
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  unfold ltN
  -- The copy's bases.
  refine WP.seq (WP.mono (WP.keep [.t3, .t4] (Q := fun u => u.gpr .t3 = off B (slot w 3) ∧
      u.gpr .t4 = off B (slot w 4) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u3, u4, um⟩, ku⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (e.base (rd := .t3) (by decide) 3) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_
    refine WP.mono ((e.keep kv (by decide)).base (rd := .t4) (by decide) 4) fun x ⟨⟨x4, xm⟩, kx⟩ => ?_
    exact ⟨(kx.gpr (by decide)).trans v3, x4, xm.trans vm⟩
  have eu : Env u B Z w := e.keep ku (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.copyWithin_ok (dS := slot w 4) (dD := slot w 3) eu.hs
    u4 u3 eu.t0 (by omega) (by omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es]; omega)
    (by rw [es, es]; omega)) fun v ⟨⟨_, vcp, vo⟩, kv⟩ => ?_)
  have ev : Env v B Z w := eu.keep kv (by decide)
  -- `x | 1` in array 3, its word `w` zeroed, and `subMod64`'s bases.
  refine WP.seq (WP.mono (ltNMid_ok ev) fun x ⟨⟨x5, x6, xm⟩, kx⟩ => ?_)
  have ex : Env x B Z w := ev.keep kx (by decide)
  have h3 : slot w 3 + 8 * w + 8 ≤ 2 ^ 64 := by rw [es]; omega
  have h3' : slot w 3 + 8 ≤ 2 ^ 64 := by rw [es]; omega
  -- Array 3: `x | 1` in its first `w` words, 0 in its word `w`.
  have o1 := writeW_outside v.mem B (word v.mem B (slot w 3) ||| 1#64) h3'
  have o2 := writeW_outside (v.mem.writeW (off B (slot w 3)) (word v.mem B (slot w 3) ||| 1#64)) B 0#64
    (d := slot w 3 + 8 * w) h3
  have w0 : word x.mem B (slot w 3) = word s.mem B (slot w 4) ||| 1#64 := by
    rw [xm, o2.word (by omega) h3', word_writeW_self]
    have := vcp 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    exact congrArg (· ||| 1#64) (this.trans (by rw [um]))
  have wj : ∀ j < w, j ≠ 0 → word x.mem B (slot w 3 + 8 * j) = word s.mem B (slot w 4 + 8 * j) := fun j hj hj0 => by
    rw [xm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact (vcp j hj).trans (by rw [um])
  have hA : wv x.mem B (slot w 3) w = wv s.mem B (slot w 4) w ||| 1 :=
    VG.Proof.RsaKeyGen.wv_or_one (by omega) w0 wj
  have hAn : word x.mem B (slot w 3 + 8 * w) = 0#64 := by rw [xm, word_writeW_self]
  have hM : VG.Proof.Mont.wordsVal x.mem B (slot w 0) w = c := by
    rw [← hc]
    show VG.Proof.Mont.wordsVal x.mem B (slot w 0) w = VG.Proof.Mont.wordsVal s.mem B (slot w 0) w
    rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv, xm,
      o2.wv (by rw [es, es]; omega) (by rw [es]; omega), o1.wv (by rw [es, es]; omega) (by rw [es]; omega)]
    have := vo.wordsVal (base := B) (d := slot w 0) (k := w) (by rw [es, es]; omega) (by rw [es]; omega)
    rw [← Pre.wordsVal_eq_wv, this, um, Pre.wordsVal_eq_wv]
  refine WP.mono (subMod64_ok (dA := slot w 3) (dT := slot w 6) (dM := slot w 0) (w := w) ex.hs x5 x6 ex.a7 ex.t0
    (by omega) (by omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es]; omega) (by rw [es]; omega)
    (by rw [es]; omega) (by rw [es]; omega) (by rw [es, es]; omega) (by rw [es, es]; omega))
    fun y ⟨⟨cb, hcb, hsum, y4⟩, yo, ky⟩ => ?_
  refine ⟨⟨?_, ?_⟩, (((ku.trans kv).trans kx).trans ky).mono (by decide)⟩
  · rw [y4]
    have hAn' : (VG.Proof.Mont.word x.mem B (slot w 3 + 8 * w)).toNat = 0 := by
      show (word x.mem B (slot w 3 + 8 * w)).toNat = 0
      rw [hAn]; rfl
    rw [hAn']
    rw [Pre.wordsVal_eq_wv x.mem B (slot w 3) w, hA, hM] at hsum
    have hT := VG.Proof.Mont.wordsVal_lt y.mem B (slot w 6) w
    have hX := VG.Proof.Bignum.wv_lt s.mem B (slot w 4) w
    have hX1 : wv s.mem B (slot w 4) w ||| 1 < 2 ^ (64 * w) := Nat.or_lt_two_pow hX (by
      have := Nat.one_lt_two_pow (show 64 * w ≠ 0 by omega); omega)
    have key : (0 < cb) = (A s.mem B w 4 ||| 1 < c) := by
      simp only [A, Pre.wordsVal_eq_wv]
      apply propext
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb with h0 | h1
      · subst h0; omega
      · subst h1; omega
    simp only [key]
  · have f1 : Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem x.mem := by
      refine Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (by
          rw [← um]
          exact fun z hz => vo z (by simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at hz ⊢; omega))
        (by simp)) ?_
      rw [xm]
      exact Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o1.mono (by omega) (by omega)) (by simp))
        (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o2.mono (by omega) (by omega)) (by simp))
    exact f1.trans (Frm.of_outside (o := slot w 6) (n := 8 * (w + 2))
      (fun z hz => yo z (by simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at hz ⊢; omega)) (by simp))

end VG.Proof.MillerRabin.RISCV64.Blinded

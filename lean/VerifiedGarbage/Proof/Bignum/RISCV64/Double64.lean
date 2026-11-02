module

public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Multiword arithmetic on RISC-V: modular doublings

`double64_ok`: the accumulator := `2 x`, `w + 1` words; `doubleMod64_ok`:
`x := 2 x mod n`, by `double64`, then `subMod64` and `selectAcc64`
(`MontFinish64.lean`), in the arrays of the working space's layout.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot)

/-- A word of the doubling: `2 x + c` is the low word of `(x << 1) + c` and
`2⁶⁴` times `x`'s top bit. -/
theorem dbl64_arith (x c : BitVec 64) (hc : c.toNat ≤ 1) :
    (x <<< 1 + c).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + c.toNat ∧ (x >>> 63).toNat ≤ 1 := by
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The registers `double64` writes. -/
def dblWRegs : List Reg := [.t3, .t4, .t5, .s2, .s3, .s4]

/-- `double64`, `x` (`w` words) at `dX` (`a2`) and the accumulator at `dA`
(`a5`): the accumulator's `w + 1` words are `2 x`. -/
theorem double64_ok {s : State} {B : Addr} {Z dA dX w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dA) (h2 : s.gpr .a2 = off B dX) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hA8 : dA % 8 = 0) (hX8 : dX % 8 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z)
    (hX : dX + 8 * w ≤ Z) (dXA : dX + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dX) :
    WP isa double64 s fun s' =>
      wordsVal s'.mem B dA (w + 1) = 2 * wordsVal s.mem B dX w ∧
      Outside B dA (8 * (w + 1)) s.mem s'.mem ∧ Keep dblWRegs s s' := by
  have hnw := hs.nowrap
  unfold double64
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t4 .a2 0, .addi .t5 .t0 0, .li .s4 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dA ∧ s₁.gpr .t4 = off B dX ∧ s₁.gpr .t5 = BitVec.ofNat 64 w ∧
        s₁.gpr .s4 = 0 ∧ s₁.mem = s.mem) ∧ Keep dblWRegs s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, h2, ht0, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i4, i5, i20, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .t4 = off B (dX + 8 * i) ∧ (t.gpr .s4).toNat ≤ 1 ∧
      Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * (t.gpr .s4).toNat = 2 * wordsVal s.mem B dX i ∧
      Keep dblWRegs s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1,
      .add .s3 .s3 .s4, .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j3, j4, j20, jout, jv, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i20]; decide, by rw [← im]; exact Outside.refl _ _ _ _,
      by simp [wordsVal, i20], Keep.refl _ _⟩ i5)
    fun t ⟨t3, _, _, tout, tv, tk⟩ => ?_)
  · have hs' := hs.congr (k₁.trans jk).2.2
    have hst : WP isa (.block [.load .d .s2 .t4 0, .shift .sll .d .s3 .s2 1, .add .s3 .s3 .s4,
        .shift .srl .d .s4 .s2 63, .store .d .s3 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t
        fun t' => (t'.gpr .t3 = off B (dA + 8 * i + 8) ∧ t'.gpr .t4 = off B (dX + 8 * i + 8) ∧
          t'.gpr .s4 = word t.mem B (dX + 8 * i) >>> 63 ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i)) (word t.mem B (dX + 8 * i) <<< 1 + t.gpr .s4) ∧
          t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep dblWRegs t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [j3, j4, hs'.ld (show dX + 8 * i + 8 ≤ Z by omega), hs'.st (show dA + 8 * i + 8 ≤ Z by omega),
        hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega) (by omega),
        hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    refine WP.mono hst fun t' ⟨⟨u3, u4, u20, um, u5⟩, uk⟩ => ⟨⟨u3.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u4.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_, Keep.trans' jk uk⟩, u5⟩
    · have := (dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .s4) j20).2
      rw [u20]; exact this
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := dbl64_arith (word t.mem B (dX + 8 * i)) (t.gpr .s4) j20
      have wx : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
      rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), u20, Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B dX i]
      rw [wx] at e
      rw [wx]
      have := e.1
      grind
  · have hst : WP isa (.block [.store .d .s4 .t3 0]) t fun t' =>
        t' = { t with mem := t.mem.writeW (off B (dA + 8 * w)) (t.gpr .s4) } := by
      brun [t3, (hs.congr (k₁.trans tk).2.2).st (show dA + 8 * w + 8 ≤ Z by omega),
        (hs.congr (k₁.trans tk).2.2).al8 (show dA + 8 * w + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    refine ⟨?_, ?_, Keep.trans' k₁ ((tk.trans (Keep.mem _ _)).mono (by decide))⟩
    · show wordsVal (t.mem.writeW (off B (dA + 8 * w)) (t.gpr .s4)) B dA (w + 1) = _
      rw [fin64_wordsVal_write_top _ _ _ _ _ (by omega), tv]
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * w) _ (by omega)).mono (by omega) (by omega))

theorem slot_al8 (w j : Nat) : slot w j % 8 = 0 := by
  unfold slot hdrBytes; rw [Nat.mul_left_comm]; omega

/-- The registers `doubleMod64` writes. -/
def dblRegs : List Reg := [.a0, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `doubleMod64`, in the arrays of the working space (`n` in array 0, `x` in
array 1, the accumulator and the temporary in arrays 2 and 3): `x := 2 x mod
n`, changing only arrays 1–3. -/
theorem doubleMod64_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hx : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa doubleMod64 s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 * wordsVal s.mem B (slot w 1) w % wordsVal s.mem B (slot w 0) w ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  have al := slot_al8 w
  unfold doubleMod64
  refine WP.seq (WP.mono (double64_ok (dA := slot w 2) (dX := slot w 1) hs h5 h2 ht0 (al 2) (al 1) hw hw'
    (by omega) (by omega) (by omega)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.2.2
  have m₂ : wordsVal s₂.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w :=
    Outside.wordsVal out₂ (by omega) (by omega)
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr (by decide), h5]) (by rw [k₂.gpr (by decide), h6])
    (by rw [k₂.gpr (by decide), h7]) (by rw [k₂.gpr (by decide), ht0]) hw hw' (al 2) (al 3) (al 0)
    (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, hD, h20'⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.2.2
  have k23 := k₂.trans k₃
  have accA : wordsVal s₃.mem B (slot w 2) w = wordsVal s₂.mem B (slot w 2) w :=
    Outside.wordsVal out₃ (by omega) (by omega)
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w 1)
    (b := decide ((word s₂.mem B (slot w 2 + 8 * w)).toNat < c)) hs₃
    (by rw [k23.gpr (by decide), h5]) (by rw [k23.gpr (by decide), h6])
    (by rw [k23.gpr (by decide), h2]) (by rw [k23.gpr (by decide), ht0])
    (by rw [h20']; simp only [decide_eq_true_eq]) hw hw' (al 2) (al 3) (al 1) (by omega) (by omega) (by omega)
    (by omega) (by omega))
    fun t ⟨hv, out₄, k₄⟩ => ⟨?_, ?_, (k23.trans k₄).mono (by decide)⟩
  · rw [accA] at hv
    have hM := wordsVal_lt s.mem B (slot w 0) w
    rw [wordsVal_succ_top] at hd
    rw [hv, ← hd, ← Nat.add_zero (word s₂.mem B (slot w 2 + 8 * w)).toNat, ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; omega) hD]
    by_cases h : (word s₂.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h]
  · exact ((Outside.mono out₂ (by omega) (by omega)).trans (Outside.mono out₃ (by omega) (by omega))).trans
      (Outside.mono out₄ (by omega) (by omega))

end VG.Proof.Bignum.RISCV64

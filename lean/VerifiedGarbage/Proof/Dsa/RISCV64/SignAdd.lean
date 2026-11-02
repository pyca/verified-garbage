module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: addition modulo q

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Add.lean`). `addArr_ok`: the
accumulator's `w + 1` words := the sum of two numbers of `w` words (as
`dbl64In_ok`, `Proof/Bignum/RISCV64/ModArith.lean`, with a second source).
`addMod_ok`: `[o] := [a] + [b] mod m` in the arrays of `Env`, through arrays
2 and 3 (as `doubleBitMod64_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

theorem ult_ofNat (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if a.toNat < b.toNat then 1 else 0) := by
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left (BitVec.lt_def.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (BitVec.lt_def.mp h')), ite_eq_right h]; rfl

theorem or01 (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b).toNat = if a = 1 ∨ b = 1 then 1 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

/-- A word of the addition: `x + y + c` with the carry out of either sum. -/
theorem add64_arith (x y c : BitVec 64) (hc : c.toNat ≤ 1) :
    ((if x + y < y then (1 : BitVec 64) else 0) ||| (if x + y + c < c then (1 : BitVec 64) else 0)).toNat ≤ 1 ∧
      (x + y + c).toNat + 2 ^ 64 *
        ((if x + y < y then (1 : BitVec 64) else 0) ||| (if x + y + c < c then (1 : BitVec 64) else 0)).toNat =
        x.toNat + y.toNat + c.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [ult_ofNat, ult_ofNat, or01 _ _ (by split <;> omega) (by split <;> omega)]
  have e1 : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have e2 : (x + y + c).toNat = ((x + y).toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  rw [e2, e1]
  simp only [Nat.reducePow] at *
  split <;> split <;> split <;> omega

/-- The registers `addArr` writes. -/
def addArrRegs : List Reg := [.t3, .t4, .t2, .t5, .s4, .s2, .s3, .s0, .s1]

/-- `addArr`, `x` and `y` (`w` words) at `dX` (`a3`) and `dY` (`a4`) and the
accumulator at `dA` (`a5`): the accumulator's `w + 1` words are `x + y`. -/
theorem addArr_ok {s : State} {B : Addr} {Z dA dX dY w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dA) (h3 : s.gpr .a3 = off B dX) (h4 : s.gpr .a4 = off B dY)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hA8 : dA % 8 = 0) (hX8 : dX % 8 = 0) (hY8 : dY % 8 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 1) ≤ Z) (hX : dX + 8 * w ≤ Z) (hY : dY + 8 * w ≤ Z)
    (dXA : dX + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dX) (dYA : dY + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dY) :
    WP isa addArr s fun s' =>
      wordsVal s'.mem B dA (w + 1) = wordsVal s.mem B dX w + wordsVal s.mem B dY w ∧
      Outside B dA (8 * (w + 1)) s.mem s'.mem ∧ Keep addArrRegs s s' := by
  have hnw := hs.nowrap
  unfold addArr
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t4 .a3 0, .addi .t2 .a4 0, .addi .t5 .t0 0, .li .s4 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dA ∧ s₁.gpr .t4 = off B dX ∧ s₁.gpr .t2 = off B dY ∧
        s₁.gpr .t5 = BitVec.ofNat 64 w ∧ s₁.gpr .s4 = 0 ∧ s₁.mem = s.mem) ∧ Keep addArrRegs s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5, h3, h4, ht0, exec_li_zero, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i4, i2, i5, i20, im⟩, k₁⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dA + 8 * i) ∧ t.gpr .t4 = off B (dX + 8 * i) ∧ t.gpr .t2 = off B (dY + 8 * i) ∧
      (t.gpr .s4).toNat ≤ 1 ∧ Outside B dA (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dA i + 2 ^ (64 * i) * (t.gpr .s4).toNat = wordsVal s.mem B dX i + wordsVal s.mem B dY i ∧
      Keep addArrRegs s₁ t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .s2 .t4 0, .load .d .s3 .t2 0, .add .s2 .s2 .s3,
      .sltu .s0 .s2 .s3, .add .s2 .s2 .s4, .sltu .s1 .s2 .s4, .logic .or .s4 .s0 .s1, .store .d .s2 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t2 .t2 8] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega) (by omega) Inv
    (fun i hi t ⟨j3, j4, j2, j20, jout, jv, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, by rw [i4]; rfl, by rw [i2]; rfl, by rw [i20]; decide,
      by rw [← im]; exact Outside.refl _ _ _ _, by simp [wordsVal, i20], Keep.refl _ _⟩ i5)
    fun t ⟨t3, _, _, _, tout, tv, tk⟩ => ?_)
  · have hs' := hs.congr (k₁.trans jk).2.2
    have hst : WP isa (.block [.load .d .s2 .t4 0, .load .d .s3 .t2 0, .add .s2 .s2 .s3, .sltu .s0 .s2 .s3,
        .add .s2 .s2 .s4, .sltu .s1 .s2 .s4, .logic .or .s4 .s0 .s1, .store .d .s2 .t3 0, .addi .t3 .t3 8,
        .addi .t4 .t4 8, .addi .t2 .t2 8, .addi .t5 .t5 (-1)]) t
        fun t' => (t'.gpr .t3 = off B (dA + 8 * i + 8) ∧ t'.gpr .t4 = off B (dX + 8 * i + 8) ∧
          t'.gpr .t2 = off B (dY + 8 * i + 8) ∧
          t'.gpr .s4 = ((if word t.mem B (dX + 8 * i) + word t.mem B (dY + 8 * i) < word t.mem B (dY + 8 * i)
              then (1 : BitVec 64) else 0) |||
            (if word t.mem B (dX + 8 * i) + word t.mem B (dY + 8 * i) + t.gpr .s4 < t.gpr .s4
              then (1 : BitVec 64) else 0)) ∧
          t'.mem = t.mem.writeW (off B (dA + 8 * i))
            (word t.mem B (dX + 8 * i) + word t.mem B (dY + 8 * i) + t.gpr .s4) ∧
          t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep addArrRegs t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [j3, j4, j2, exec_sltu, hs'.ld (show dX + 8 * i + 8 ≤ Z by omega),
        hs'.ld (show dY + 8 * i + 8 ≤ Z by omega), hs'.st (show dA + 8 * i + 8 ≤ Z by omega),
        hs'.al8 (show dX + 8 * i + 8 ≤ Z by omega) (by omega), hs'.al8 (show dY + 8 * i + 8 ≤ Z by omega) (by omega),
        hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega) (by omega), BitVec.add_zero]
    refine WP.mono hst fun t' ⟨⟨u3, u4, u2, u20, um, u5⟩, uk⟩ => ⟨⟨u3.trans (by rw [Nat.mul_succ, Nat.add_assoc]),
      u4.trans (by rw [Nat.mul_succ, Nat.add_assoc]), u2.trans (by rw [Nat.mul_succ, Nat.add_assoc]), ?_, ?_, ?_,
      Keep.trans' jk uk⟩, u5⟩
    · rw [u20]; exact (add64_arith _ _ _ j20).1
    · rw [um]
      exact (jout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := dA + 8 * i) _ (by omega)).mono (by omega) (by omega))
    · have e := (add64_arith (word t.mem B (dX + 8 * i)) (word t.mem B (dY + 8 * i)) (t.gpr .s4) j20).2
      have wx : word t.mem B (dX + 8 * i) = word s.mem B (dX + 8 * i) := jout.word (by omega) (by omega)
      have wy : word t.mem B (dY + 8 * i) = word s.mem B (dY + 8 * i) := jout.word (by omega) (by omega)
      rw [um, fin64_wordsVal_write_top _ _ _ _ _ (by omega), u20, Nat.mul_succ, Nat.pow_add,
        wordsVal_succ_top s.mem B dX i, wordsVal_succ_top s.mem B dY i]
      rw [wx, wy] at e
      rw [wx, wy]
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

/-- The registers `addMod` writes. -/
def addModRegs : List Reg := [.a3, .a4, .a5, .a6, .a2, .t3, .t4, .t2, .t5, .s4, .s2, .s3, .s0, .s1, .a0]

/-- `addMod`'s change of memory: arrays 2 and 3, then array `o`. -/
def AddFrame (B : Addr) (w o : Nat) (m m' : Mem) : Prop :=
  ∃ m₁, Outside B (slot w 2) (2 * (8 * (w + 2))) m m₁ ∧ Outside B (slot w o) (8 * (w + 2)) m₁ m'

theorem slot_sep' {w j k : Nat} (hjk : j ≠ k) :
    slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := by
  rcases Nat.lt_or_gt_of_ne hjk with hl | hl
  · exact .inl (slot_lt hl)
  · exact .inr (slot_lt hl)

/-- `addMod o a b`, in the arrays of `Env` with the modulus in array 0:
`[o] := [a] + [b] mod [0]`, for `[a] + [b] < 2 [0]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {o a b : Nat}
    (ho : o < 28) (ha : a < 28) (hb : b < 28) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hb2 : b ≠ 2) (hb3 : b ≠ 3)
    (hlt : wordsVal s.mem B (slot w a) w + wordsVal s.mem B (slot w b) w < 2 * wordsVal s.mem B (slot w 0) w) :
    WP isa (addMod o a b) s fun t =>
      (wordsVal t.mem B (slot w o) w =
          (wordsVal s.mem B (slot w a) w + wordsVal s.mem B (slot w b) w) % wordsVal s.mem B (slot w 0) w ∧
        AddFrame B w o s.mem t.mem) ∧ Keep addModRegs s t := by
  have hnw := h.hs.nowrap
  have hw := h.w2
  have hw' := h.w48
  have hZ := h.hZ
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have sl := fun {j : Nat} (hj : j < 28) => slot_lt (w := w) hj
  have hO := sl ho; have hA := sl ha; have hB := sl hb
  have e0 := e 0; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e28 := e 28
  have al := slot_al8 w
  have sa2 := slot_sep' (w := w) ha2; have sb2 := slot_sep' (w := w) hb2
  have sa3 := slot_sep' (w := w) ha3; have sb3 := slot_sep' (w := w) hb3
  have so2 := slot_sep' (w := w) ho2; have so3 := slot_sep' (w := w) ho3
  unfold addMod
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .a3) (by decide) a) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1
  rw [WP.block_append_iff]
  refine WP.mono (e1.base (rd := .a4) (by decide) b) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have e2' := e1.keep k2
  rw [WP.block_append_iff]
  refine WP.mono (e2'.base (rd := .a5) (by decide) 2) fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have e3' := e2'.keep k3
  rw [WP.block_append_iff]
  refine WP.mono (e3'.base (rd := .a6) (by decide) 3) fun t₄ ⟨⟨a6, m4⟩, k4⟩ => ?_
  have e4' := e3'.keep k4
  refine WP.mono (e4'.base (rd := .a2) (by decide) o) fun t₅ ⟨⟨a2, m5⟩, k5⟩ => ?_
  have e5' := e4'.keep k5
  have hm5 : t₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have g3 : t₅.gpr .a3 = off B (slot w a) := (((k2.trans k3).trans k4).trans k5).gpr (by decide) |>.trans a3
  have g4 : t₅.gpr .a4 = off B (slot w b) := ((k3.trans k4).trans k5).gpr (by decide) |>.trans a4
  have g5 : t₅.gpr .a5 = off B (slot w 2) := (k4.trans k5).gpr (by decide) |>.trans a5
  have g6 : t₅.gpr .a6 = off B (slot w 3) := k5.gpr (by decide) |>.trans a6
  -- The sum.
  refine WP.seq (WP.mono (addArr_ok (w := w) (dA := slot w 2) (dX := slot w a) (dY := slot w b) e5'.hs
    g5 g3 g4 e5'.t0 (al 2) (al a) (al b) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  rw [hm5] at hd out₂
  have hs₂ := e5'.hs.congr k₂.2.2
  have m₂ : wordsVal s₂.mem B (slot w 0) w = wordsVal s.mem B (slot w 0) w :=
    out₂.wordsVal (by omega) (by omega)
  have k₂' := k15.trans k₂
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr (by decide), g5]) (by rw [k₂.gpr (by decide), g6])
    (by rw [k₂'.gpr (by decide), h.a7]) (by rw [k₂'.gpr (by decide), h.t0]) (by omega) (by omega)
    (al 2) (al 3) (al 0) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₃ ⟨⟨c, hc, hD, h20⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.2.2
  have k23 := k₂.trans k₃
  have accA : wordsVal s₃.mem B (slot w 2) w = wordsVal s₂.mem B (slot w 2) w :=
    out₃.wordsVal (by omega) (by omega)
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide ((word s₂.mem B (slot w 2 + 8 * w)).toNat < c)) hs₃
    (by rw [k23.gpr (by decide), g5]) (by rw [k23.gpr (by decide), g6])
    (by rw [k23.gpr (by decide)]; exact a2)
    (by rw [(k15.trans k23).gpr (by decide), h.t0])
    (by rw [h20]; simp only [decide_eq_true_eq]) (by omega) (by omega) (al 2) (al 3) (al o)
    (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, out₄, k₄⟩ => ⟨⟨?_, ?_⟩, ((k15.trans k23).trans k₄).mono (by decide)⟩
  · rw [accA] at hv
    have hM := wordsVal_lt s.mem B (slot w 0) w
    rw [wordsVal_succ_top] at hd
    rw [hv, ← hd, ← Nat.add_zero (word s₂.mem B (slot w 2 + 8 * w)).toNat, ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (wordsVal_lt _ _ _ _) hc (wordsVal_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; exact hlt) hD]
    by_cases h' : (word s₂.mem B (slot w 2 + 8 * w)).toNat < c <;> simp [h']
  · exact ⟨s₃.mem, (out₂.mono (by omega) (by omega)).trans (out₃.mono (by omega) (by omega)),
      out₄.mono (Nat.le_refl _) (by omega)⟩

/-- Arrays other than 2, 3 and `o` are kept by `addMod`. -/
theorem AddFrame.arr_eq {B : Addr} {Z w o : Nat} {m m' : Mem} (h : AddFrame B w o m m') (hZ : slot w 28 ≤ Z)
    (hnw : B.toNat + Z ≤ 2 ^ 64) {j : Nat} (hj : j < 28) (hj2 : j ≠ 2) (hj3 : j ≠ 3) (hjo : j ≠ o) :
    wordsVal m' B (slot w j) w = wordsVal m B (slot w j) w := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  have hJ := slot_lt (w := w) hj
  have s2 := slot_sep' (w := w) hj2
  have s3 := slot_sep' (w := w) hj3
  have so := slot_sep' (w := w) hjo
  have e3 : slot w 3 = slot w 2 + 8 * (w + 2) := by simp only [Lay.slot_eq]; omega
  rw [h₂.wordsVal (by omega) (by omega), h₁.wordsVal (by omega) (by omega)]

end VG.Proof.Dsa.RISCV64

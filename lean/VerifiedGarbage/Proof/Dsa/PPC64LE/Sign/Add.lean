module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# DSA signing on PPC64LE: addition modulo q

`addArr_ok`: the accumulator's `n + 1` digits := the sum of two numbers of
`n` digits (as `double_ok`, `Proof/Bignum/PPC64LE/PreDouble.lean`, with a
second source). `addMod_ok`: `[o] := [a] + [b] mod m` in the arrays of
`Env`, through arrays 2 and 3 (as `doubleBitMod_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep)

/-- A digit of the addition, on bit vectors: `D = x + y + c`, whose low 32 bits
are the digit and whose bits above are the carry. -/
theorem add_arith (x y : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    let D := x.setWidth 64 + y.setWidth 64 + c
    (D >>> 32).toNat ≤ 1 ∧ (D.setWidth 32).toNat + 2 ^ 32 * (D >>> 32).toNat = x.toNat + y.toNat + c.toNat := by
  intro D
  have hx := x.isLt
  have hy := y.isLt
  have vD : D.toNat = x.toNat + y.toNat + c.toNat := by
    simp only [D, BitVec.toNat_add, toNat_ext32]
    omega_arith
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vD]
  omega_arith

/-- The registers `addArr` writes. -/
def addArrRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17, .r20]

/-- `addArr`, `x` and `y` (`n` digits) at `dX` and `dY` and the accumulator at
`dA`: the accumulator's `n + 1` digits are `x + y`. -/
theorem addArr_ok {s : State} {B : Addr} {Z dA dX dY n : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B dA) (h5 : s.gpr .r5 = off B dX) (h16 : s.gpr .r16 = off B dY)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA : dA + 4 * (n + 1) ≤ Z) (hX : dX + 4 * n ≤ Z) (hY : dY + 4 * n ≤ Z)
    (dXA : dX + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dX) (dYA : dY + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dY) :
    WP isa addArr s fun s' =>
      val32 s'.mem B dA (n + 1) = val32 s.mem B dX n + val32 s.mem B dY n ∧
      Mont.Outside B dA (4 * (n + 1)) s.mem s'.mem ∧ Keep addArrRegs s s' := by
  have hnw := hs.nowrap
  unfold addArr
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r8 0, .addi .r15 .r5 0, .addi .r17 .r11 0, .li .r20 0]) s
      fun s₁ => (s₁.gpr .r14 = off B dA ∧ s₁.gpr .r15 = off B dX ∧ s₁.gpr .r17 = BitVec.ofNat 64 n ∧
        s₁.gpr .r20 = 0 ∧ s₁.mem = s.mem) ∧ Keep [.r14, .r15, .r17, .r20] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h8, h5, h11, BitVec.add_zero]
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i14, i15, i17, i20, im⟩, k₁⟩ => ?_
  have i16 : s₁.gpr .r16 = off B dY := (k₁.gpr .r16 (by decide)).trans h16
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (dA + 4 * i) ∧ t.gpr .r15 = off B (dX + 4 * i) ∧ t.gpr .r16 = off B (dY + 4 * i) ∧
      (t.gpr .r20).toNat ≤ 1 ∧ Mont.Outside B dA (4 * i) s.mem t.mem ∧
      val32 t.mem B dA i + 2 ^ (32 * i) * (t.gpr .r20).toNat = val32 s.mem B dX i + val32 s.mem B dY i ∧
      Keep addArrRegs s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .w .r0 .r15 0, .load .w .r3 .r16 0,
      .add .r0 .r0 .r3, .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4,
      .addi .r15 .r15 4, .addi .r16 .r16 4] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j15, j16, j20, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [i14]; rfl, by rw [i15]; rfl, by rw [i16]; rfl, by rw [i20]; decide,
      by rw [← im]; exact Mont.Outside.refl _ _ _ _, by simp [val32, i20], k₁.mono (by decide)⟩ i17)
    fun t ⟨j14, _, _, j20, jout, jeq, jk⟩ => ?_)
  · have hst := (show WP isa (.block [.load .w .r0 .r15 0, .load .w .r3 .r16 0, .add .r0 .r0 .r3,
        .add .r0 .r0 .r20, .store .w .r0 .r14 0, .lsr .d .r20 .r0 32, .addi .r14 .r14 4, .addi .r15 .r15 4,
        .addi .r16 .r16 4, .subi .r17 .r17 1]) t fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dY + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dY + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32) ∧
          Keep addArrRegs t t' from by
      refine WP.mono (WP.keep addArrRegs (Q := fun t' =>
        let D := (t.mem.readW (off B (dX + 4 * i)) 32).setWidth 64 +
          (t.mem.readW (off B (dY + 4 * i)) 32).setWidth 64 + t.gpr .r20
        t'.gpr .r14 = off B (dA + 4 * i + 4) ∧ t'.gpr .r15 = off B (dX + 4 * i + 4) ∧
          t'.gpr .r16 = off B (dY + 4 * i + 4) ∧
          t'.gpr .r20 = D >>> 32 ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (dA + 4 * i)) (D.setWidth 32)) ?_ (by decide))
        fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
      prun [j14, j15, j16, (hs.congr jk.wr).ld (show dX + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).ld (show dY + 4 * i + 4 ≤ Z by omega_arith),
        (hs.congr jk.wr).st (show dA + 4 * i + 4 ≤ Z by omega_arith)])
    refine WP.mono hst fun t' ⟨l14, l15, l16, l20, l17, lm, lk⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, (jk.trans lk).mono (by simp [addArrRegs])⟩, l17⟩
    · rw [l14, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
    · rw [l15, show dX + 4 * i + 4 = dX + 4 * (i + 1) by omega_arith]
    · rw [l16, show dY + 4 * i + 4 = dY + 4 * (i + 1) by omega_arith]
    · rw [l20]; exact (add_arith _ _ _ j20).1
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · have wx : w32 t.mem B (dX + 4 * i) = w32 s.mem B (dX + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      have wy : w32 t.mem B (dY + 4 * i) = w32 s.mem B (dY + 4 * i) := jout.w32 (by omega_arith) (by omega_arith)
      have k := (add_arith (t.mem.readW (off B (dX + 4 * i)) 32) (t.mem.readW (off B (dY + 4 * i)) 32) _ j20).2
      rw [lm, l20, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dX i, val32_succ s.mem B dY i,
        ← pow32_mul i]
      rw [← wx, ← wy]
      change _ + 2 ^ 32 * _ = w32 t.mem B (dX + 4 * i) + w32 t.mem B (dY + 4 * i) + (t.gpr .r20).toNat at k
      change _ = (_ + _ * w32 t.mem B (dX + 4 * i)) + (_ + _ * w32 t.mem B (dY + 4 * i))
      grind
  · have hfin : WP isa (.block [.store .w .r20 .r14 0]) t fun t' =>
        t'.mem = t.mem.writeW (off B (dA + 4 * n)) ((t.gpr .r20).setWidth 32) ∧ Keep [] t t' := by
      refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (off B (dA + 4 * n))
        ((t.gpr .r20).setWidth 32)) ?_ (by decide)) fun t' ⟨h, k⟩ => ⟨h, k⟩
      prun [j14, (hs.congr jk.wr).st (show dA + 4 * n + 4 ≤ Z by omega_arith)]
    refine WP.mono hfin fun t' ⟨lm, lk⟩ => ⟨?_, ?_, (jk.trans lk).mono (by simp)⟩
    · rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), ← jeq]
      congr 2
      rw [BitVec.toNat_setWidth]
      omega_arith
    · rw [lm]
      exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ B (d := dA + 4 * n) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The registers `addMod` writes. -/
def addModRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `addMod`'s change of memory: arrays 2 and 3, then array `o`. -/
def AddFrame (B : Addr) (w o : Nat) (m m' : Mem) : Prop :=
  ∃ m₁, Outside B (slot w 2) (2 * (8 * (w + 2))) m m₁ ∧ Outside B (slot w o) (8 * (w + 2)) m₁ m'

/-- `addMod o a b`, in the arrays of `Env` with the modulus in array 0:
`[o] := [a] + [b] mod [0]`, for `[a] + [b] < 2 [0]`. -/
theorem addMod_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {o a b : Nat}
    (ho : o < 28) (ha : a < 28) (hb : b < 28) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hb2 : b ≠ 2) (hb3 : b ≠ 3) (hlt : arr s.mem B w a + arr s.mem B w b < 2 * arr s.mem B w 0) :
    WP isa (addMod o a b) s fun t =>
      (arr t.mem B w o = (arr s.mem B w a + arr s.mem B w b) % arr s.mem B w 0 ∧ AddFrame B w o s.mem t.mem) ∧
        Keep addModRegs s t := by
  have hnw := h.hs.nowrap
  have hw := h.hw
  have hw' := h.hw'
  have hZ := h.hZ
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have hh : hdrBytes = 256 := rfl
  have sl := fun {j : Nat} (hj : j < 28) => slot_lt (w := w) hj
  have hO := sl ho; have hA := sl ha; have hB := sl hb
  have e0 := e 0; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have eo := e o; have ea := e a; have eb := e b; have eo1 := e (o + 1)
  have e28 := e 28
  unfold addMod
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) a) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e1.base (rd := .r16) (by decide) (by decide) b) fun t₂ ⟨⟨a16, m2⟩, k2⟩ => ?_
  have e2' := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2'.base (rd := .r8) (by decide) (by decide) 2) fun t₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  have e3' := e2'.keep k3 (by decide)
  refine WP.mono (e3'.base (rd := .r9) (by decide) (by decide) 3) fun t₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  have e4' := e3'.keep k4 (by decide)
  have hm4 : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  have g8 : t₄.gpr .r8 = off B (slot w 2) := (k4.gpr .r8 (by decide)).trans a8
  have g5 : t₄.gpr .r5 = off B (slot w a) :=
    (k4.gpr .r5 (by decide)).trans ((k3.gpr .r5 (by decide)).trans ((k2.gpr .r5 (by decide)).trans a5))
  have g16 : t₄.gpr .r16 = off B (slot w b) := (k4.gpr .r16 (by decide)).trans ((k3.gpr .r16 (by decide)).trans a16)
  have k14 := ((k1.trans k2).trans k3).trans k4
  have ma : (o + 1) * (8 * (w + 2)) = o * (8 * (w + 2)) + 8 * (w + 2) := by rw [Nat.add_mul, Nat.one_mul]
  have sep : ∀ {j k : Nat}, j ≠ k → j < 28 → k < 28 →
      slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hjk hj hk => by
    rcases Nat.lt_or_gt_of_ne hjk with hl | hl
    · exact .inl (slot_lt hl)
    · exact .inr (slot_lt hl)
  have sa2 := sep ha2 ha (by decide); have sb2 := sep hb2 hb (by decide)
  have sa3 := sep ha3 ha (by decide); have sb3 := sep hb3 hb (by decide)
  have so2 := sep ho2 ho (by decide); have so3 := sep ho3 ho (by decide)
  -- The sum.
  refine WP.seq (WP.mono (addArr_ok (n := 2 * w) (dA := slot w 2) (dX := slot w a) (dY := slot w b) e4'.hs
    g8 g5 g16 e4'.h11 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨hd, out₂, k₂⟩ => ?_)
  rw [hm4] at hd out₂
  have hs₂ := e4'.hs.congr k₂.wr
  have m₂ : val32 s₂.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    out₂.val32 (by omega_arith) (by omega_arith)
  have k₂' := k14.trans k₂
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₂
    (by rw [k₂.gpr .r8 (by decide), g8]) (by rw [k₂.gpr .r9 (by decide), a9])
    (by rw [k₂'.gpr .r10 (by decide), h.h10]) (by rw [k₂.gpr .r11 (by decide), e4'.h11])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨c, hc, hD, h20⟩, out₃, k₃⟩ => ?_)
  rw [m₂] at hD
  have hs₃ := hs₂.congr k₃.wr
  have k23 := k₂.trans k₃
  have accA : val32 s₃.mem B (slot w 2) (2 * w) = val32 s₂.mem B (slot w 2) (2 * w) :=
    out₃.val32 (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  have e₃ := e4'.keep k23 (by decide)
  refine WP.mono (e₃.base (rd := .r5) (by decide) (by decide) o) fun s₄ ⟨⟨a5', m₄⟩, k₄⟩ => ?_
  have k24 := k23.trans k₄
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide (w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c)) (hs₃.congr k₄.wr)
    (by rw [k24.gpr .r8 (by decide), g8]) (by rw [k24.gpr .r9 (by decide), a9])
    a5' (by rw [k24.gpr .r11 (by decide), e4'.h11])
    (by rw [k₄.gpr .r20 (by decide), h20]; simp only [decide_eq_true_eq])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, out₅, k₅⟩ => ⟨⟨?_, ?_⟩, (((k14.trans k23).trans k₄).trans k₅).mono (by decide)⟩
  · rw [m₄, accA] at hv
    have hM := val32_lt s.mem B (slot w 0) (2 * w)
    rw [val32_succ] at hd
    show val32 t.mem B (slot w o) (2 * w) = (val32 s.mem B (slot w a) (2 * w) + val32 s.mem B (slot w b) (2 * w)) %
      val32 s.mem B (slot w 0) (2 * w)
    rw [hv, ← hd, ← Nat.add_zero (w32 s₂.mem B (slot w 2 + 4 * (2 * w))),
      ← Nat.mul_zero (2 ^ 64),
      ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _)
        (by rw [Nat.mul_zero, Nat.add_zero, hd]; exact hlt) hD]
    by_cases hb' : w32 s₂.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [hb']
  · refine ⟨s₄.mem, ?_, out₅.mono (Nat.le_refl _) (by omega_arith)⟩
    rw [m₄]
    exact (out₂.mono (by omega_arith) (by omega_arith)).trans (out₃.mono (by omega_arith) (by omega_arith))

/-- Arrays other than 2, 3 and `o` are kept by `addMod`. -/
theorem AddFrame.arr_eq {B : Addr} {Z w o : Nat} {m m' : Mem} (h : AddFrame B w o m m') (hZ : slot w 28 ≤ Z)
    (hnw : B.toNat + Z ≤ 2 ^ 64) {j : Nat} (hj : j < 28) (hj2 : j ≠ 2) (hj3 : j ≠ 3) (hjo : j ≠ o) (ho : o < 28) :
    arr m' B w j = arr m B w j := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  have hJ := slot_lt (w := w) hj
  have sep : ∀ {k : Nat}, j ≠ k → k < 28 →
      slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j := fun hjk hk => by
    rcases Nat.lt_or_gt_of_ne hjk with hl | hl
    · exact .inl (slot_lt hl)
    · exact .inr (slot_lt hl)
  have s2 := sep hj2 (by decide)
  have s3 := sep hj3 (by decide)
  have so := sep hjo ho
  have e3 : slot w 3 = slot w 2 + 8 * (w + 2) := by simp only [slot]; omega_arith
  unfold VG.Proof.MillerRabin.PPC64LE.arr
  rw [Outside.val32 h₂ (by omega_arith) (by omega_arith), Outside.val32 h₁ (by omega_arith) (by omega_arith)]

end VG.Proof.Dsa.PPC64LE

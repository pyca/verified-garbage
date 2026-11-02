module

public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqrRows
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery squaring on RISC-V

`sqrTail_ok`: `Impl/Bignum/RISCV64/MontSqr.lean`'s `sqrTail`, the drop-in
for `MontCore.lean`'s `tail_ok` on squares: `[o] < m` and
`[o] 2^(64 w) ≡ [a]² (mod m)`, from `MontSqrRows.lean`'s phases.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum
open VG.Proof.Bignum (slot slot_sep Arrays)

theorem sqr_shl3 (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- Memory that changed only in arrays 2 and 3 (`T`) changed only in those
arrays. -/
theorem arrays23_of_outside {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h2 : 2 ∈ js) (h3 : 3 ∈ js)
    (h : VG.Proof.Bignum.Outside B (slot w 2) (16 * (w + 2)) m m') : Arrays B w js m m' := by
  intro x hx
  have a2 := hx 2 h2
  have a3 := hx 3 h3
  have e : slot w 3 = slot w 2 + 8 * (w + 2) := by
    unfold slot; rw [Nat.add_mul (2 : Nat) 1, Nat.one_mul, Nat.add_assoc]
  exact h x (by omega_arith)

/-- If `T + P e = X` for a number `T` below `P` and `X` below `P`, then `e = 0`. -/
theorem top_zero {T P e X : Nat} (h : T + P * e = X) (hX : X < P) : e = 0 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · exact he
  · exfalso; have := Nat.mul_le_mul_left P he; omega_arith

/-- The registers `sqrTail` writes and does not restore. -/
def sqrRegs : List Reg := [.a0, .a1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `sqrTail`, for arrays below `n`: `[o] < m` and `[o] 2^(64 w) ≡ [a]²
(mod m)`, with only arrays 2, 3 (`T`), `p` (the temporary) and `o`
changed. -/
theorem sqrTailN_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {n o a p : Nat} (hn : 4 ≤ n) (ho : o < n) (ha : a < n) (hp : p < n) (ho2 : o ≠ 2) (ho3 : o ≠ 3)
    (ha2 : a ≠ 2) (ha3 : a ≠ 3) (hp0 : p ≠ 0) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpo : p ≠ o)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w n ≤ Z)
    (i2 : s.gpr .a2 = off B (slot w o)) (i3 : s.gpr .a3 = off B (slot w a))
    (i5 : s.gpr .a5 = off B (slot w 2)) (i6 : s.gpr .a6 = off B (slot w p))
    (i7 : s.gpr .a7 = off B (slot w 0)) (it0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w) :
    WP isa sqrTail s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w a) w %
            wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, p, o] s.mem t.mem) ∧
      Keep sqrRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < n, slot w j + 8 * (w + 2) ≤ Z := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ n by omega_using [hj])
    rw [Nat.add_mul, Nat.one_mul] at this
    unfold slot at hZ ⊢; omega_using [this, hZ]
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨
      slot w k + 8 * (w + 2) ≤ slot w j := fun h => slot_sep h
  have e3 : slot w 3 = slot w 2 + 8 * (w + 2) := by
    unfold slot; rw [Nat.add_mul (2 : Nat) 1, Nat.one_mul, Nat.add_assoc]
  generalize hdT : slot w 2 = dT at *
  generalize hdA : slot w a = dA at *
  generalize hdM : slot w 0 = dM at *
  generalize hdP : slot w p = dP at *
  generalize hdO : slot w o = dO at *
  have s2 := sl 2 (by omega_arith)
  have s3 := sl 3 (by omega_arith)
  rw [e3] at s3
  have sA := sl a ha
  have sM := sl 0 (by omega_arith)
  have sP := sl p hp
  have sO := sl o ho
  rw [hdA] at sA; rw [hdM] at sM; rw [hdP] at sP; rw [hdO] at sO
  -- Each other array is apart from both of `T`'s.
  have apart : ∀ {j}, j < n → j ≠ 2 → j ≠ 3 → slot w j + 8 * (w + 2) ≤ dT ∨
      dT + 16 * (w + 2) ≤ slot w j := fun hj h2 h3 => by
    have := sp h2; have := sp h3; rw [hdT] at *; rw [e3] at *; omega_arith
  have pA := apart ha ha2 ha3; rw [hdA] at pA
  have pM := apart (show 0 < n by omega_arith) (by decide) (by decide); rw [hdM] at pM
  have pP := apart hp hp2 hp3; rw [hdP] at pP
  have pO := apart ho ho2 ho3; rw [hdO] at pO
  have pPM := sp hp0; rw [hdP, hdM] at pPM
  have pPO := sp hpo; rw [hdP, hdO] at pPO
  have al := slot_al w
  have aT : dT % 8 = 0 := hdT ▸ al 2
  have aA : dA % 8 = 0 := hdA ▸ al a
  have aM : dM % 8 = 0 := hdM ▸ al 0
  have aP : dP % 8 = 0 := hdP ▸ al p
  have aO : dO % 8 = 0 := hdO ▸ al o
  have hM := wordsVal_lt s.mem B dM w
  unfold sqrTail
  -- `T := 0`.
  refine WP.seq (WP.mono (zeroT_ok (dT := dT) (w := w) hs i5 it0 aT hw' (by omega_arith)) fun s₁ ⟨z1, o1, k1⟩ => ?_)
  have g1 : ∀ r ∈ [Reg.a2, .a3, .a5, .a6, .a7, .t0, .t1], s₁.gpr r = s.gpr r := fun r hr => k1.gpr (by revert r hr; decide)
  -- The cross products.
  refine WP.seq (WP.mono (cross_ok (dA := dA) (dT := dT) (w := w) (hs.congr k1.2.2) aA aT
    (by rw [g1 .a3 (by decide), i3]) (by rw [g1 .a5 (by decide), i5]) (by rw [g1 .t0 (by decide), it0]) hw2 hw'
    (by omega_arith) (by omega_arith) (by omega_arith) z1) fun s₂ ⟨⟨c2, o2⟩, k2⟩ => ?_)
  have g2 : ∀ r ∈ [Reg.a2, .a3, .a5, .a6, .a7, .t0, .t1], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k2.gpr (by revert r hr; decide), g1 r hr]
  -- The doubling and the squares.
  refine WP.seq (WP.mono (diag_ok (dA := dA) (dT := dT) (w := w) (hs.congr (k1.trans k2).2.2) aA aT
    (by rw [g2 .a3 (by decide), i3]) (by rw [g2 .a5 (by decide), i5]) (by rw [g2 .t0 (by decide), it0])
    (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨e, d3⟩, o3, k3⟩ => ?_)
  have g3 : ∀ r ∈ [Reg.a2, .a3, .a5, .a6, .a7, .t0, .t1], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k3.gpr (by revert r hr; decide), g2 r hr]
  -- `T` is `A²`.
  have o12 : Mont.Outside B dT (8 * (2 * w + 2)) s.mem s₂.mem := o1.trans o2
  have o13 : Mont.Outside B dT (8 * (2 * w + 2)) s.mem s₃.mem := o12.trans (o3.mono (by omega_arith) (by omega_arith))
  have rA1 : ∀ i, i ≤ w → crossPart s₁.mem B dA w i = crossPart s.mem B dA w i :=
    crossPart_out o1 (by omega_arith) (by omega_arith)
  have rA2 : ∀ i, i ≤ w → diagPart s₂.mem B dA i = diagPart s.mem B dA i :=
    diagPart_out o12 (by omega_arith) (by omega_arith)
  rw [rA1 _ (by omega_arith)] at c2
  rw [rA2 _ (Nat.le_refl _)] at d3
  have hsq := sq_parts s.mem B dA w
  rw [crossPart_last _ _ _ _ (by omega_arith)] at hsq
  have hA2 : wordsVal s.mem B dA w * wordsVal s.mem B dA w < 2 ^ (64 * (2 * w)) := by
    have := wordsVal_lt s.mem B dA w
    calc wordsVal s.mem B dA w * wordsVal s.mem B dA w < 2 ^ (64 * w) * 2 ^ (64 * w) := Nat.mul_lt_mul_of_lt_of_lt this this
      _ = 2 ^ (64 * (2 * w)) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have hCD : 2 * crossPart s.mem B dA w (w - 1) + diagPart s.mem B dA w = wordsVal s.mem B dA w * wordsVal s.mem B dA w := by
    rw [hsq, Nat.add_comm]
  have hC : crossPart s.mem B dA w (w - 1) < 2 ^ (64 * (2 * w)) :=
    Nat.lt_of_le_of_lt (by omega_using [hCD]) hA2
  have hW2 : wordsVal s₂.mem B dT (2 * w) = crossPart s.mem B dA w (w - 1) := by
    have e2 := fios_wordsVal_append s₂.mem B dT (2 * w) 2
    rw [c2] at e2
    have hz := top_zero e2.symm hC
    rw [hz, Nat.mul_zero, Nat.add_zero] at e2
    exact e2.symm
  rw [hW2, show 128 * w = 64 * (2 * w) by omega_arith, hCD] at d3
  have he : e = 0 := top_zero d3 hA2
  rw [he, Nat.mul_zero, Nat.add_zero] at d3
  -- The reduction.
  have m3 : wordsVal s₃.mem B dM w = wordsVal s.mem B dM w := o13.wordsVal (by omega_arith) (by omega_arith)
  have w3 : Mont.word s₃.mem B dM = Mont.word s.mem B dM := o13.word (by omega_arith) (by omega_arith)
  have k13 := (k1.trans k2).trans k3
  refine WP.seq (WP.mono (reduce_ok (dT := dT) (dM := dM) (w := w) (hs.congr k13.2.2) aT aM
    (by rw [g3 .a5 (by decide), i5]) (by rw [g3 .a7 (by decide), i7]) (by rw [g3 .t0 (by decide), it0])
    (by rw [w3, g3 .t1 (by decide)]; exact hinv) (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₄ ⟨⟨z4, U, hU, r4⟩, o4, k4⟩ => ?_)
  rw [d3, m3] at r4
  have k14 := k13.trans k4
  have hs₄ := hs.congr k14.2.2
  have g4 : ∀ r ∈ [Reg.a2, .a3, .a5, .a6, .a7, .t0, .t1], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k4.gpr (by revert r hr; decide), g3 r hr]
  -- The last carry at word `2 w`, `a5` at word `w`.
  have hpre : WP isa (.block finishPre) s₄ fun s₅ =>
      (s₅.gpr .a5 = off B (dT + 8 * w) ∧ s₅.mem = s₄.mem.writeW (off B (dT + 16 * w)) (s₄.gpr .a1)) ∧
        Keep [.a5, .t3, .t4] s₄ s₅ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold finishPre
    have e5 := g4 .a5 (by decide)
    have e0 := g4 .t0 (by decide)
    rw [i5] at e5; rw [it0] at e0
    brun [e5, e0, sqr_shl3, show dT + 8 * w + 8 * w = dT + 16 * w by omega_arith, hs₄.st (show dT + 16 * w + 8 ≤ Z by omega_arith),
      hs₄.al8 (show dT + 16 * w + 8 ≤ Z by omega_arith) (by omega_arith)]
    done
  refine WP.seq (WP.mono hpre fun s₅ ⟨⟨j5, m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have hs₅ := hs.congr k15.2.2
  have g5 : ∀ r ∈ [Reg.a2, .a6, .a7, .t0], s₅.gpr r = s.gpr r := fun r hr => by
    rw [k5.gpr (by revert r hr; decide), g4 r (by revert r hr; decide)]
  have o45 : Mont.Outside B (dT + 16 * w) 8 s₄.mem s₅.mem := by
    rw [m5]; exact writeW_outside _ _ _ (by omega_arith)
  have tl5 : wordsVal s₅.mem B (dT + 8 * w) w = wordsVal s₄.mem B (dT + 8 * w) w :=
    o45.wordsVal (by omega_arith) (by omega_arith)
  have tw5 : Mont.word s₅.mem B (dT + 8 * w + 8 * w) = s₄.gpr .a1 := by
    rw [m5, show dT + 8 * w + 8 * w = dT + 16 * w by omega_arith]; exact word_writeW_self _ _ _ _
  have m5' : wordsVal s₅.mem B dM w = wordsVal s.mem B dM w := by
    rw [o45.wordsVal (by omega_arith) (by omega_arith), o4.wordsVal (by omega_arith) (by omega_arith), m3]
  -- `T / R - m`.
  refine WP.seq (WP.mono (subMod64_ok (w := w) (dA := dT + 8 * w) (dT := dP) (dM := dM) hs₅ j5
    (by rw [g5 .a6 (by decide), i6]) (by rw [g5 .a7 (by decide), i7]) (by rw [g5 .t0 (by decide), it0])
    (by omega_arith) hw' (by omega_arith) aP aM (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith))
    fun s₆ ⟨⟨c, hc, hD, h46⟩, o6, k6⟩ => ?_)
  rw [m5', tl5] at hD
  rw [tw5] at h46
  have k16 := k15.trans k6
  have hs₆ := hs.congr k16.2.2
  have g6 : ∀ r ∈ [Reg.a2, .a5, .a6, .t0], s₆.gpr r = s₅.gpr r := fun r hr => k6.gpr (by revert r hr; decide)
  have tl6 : wordsVal s₆.mem B (dT + 8 * w) w = wordsVal s₄.mem B (dT + 8 * w) w :=
    (o6.wordsVal (by omega_arith) (by omega_arith)).trans tl5
  -- The selection.
  refine WP.seq (WP.mono (selectAcc64_ok (w := w) (dA := dT + 8 * w) (dT := dP) (dO := dO)
    (b := decide ((s₄.gpr .a1).toNat < c)) hs₆
    (by rw [g6 .a5 (by decide), j5]) (by rw [g6 .a6 (by decide), g5 .a6 (by decide), i6])
    (by rw [g6 .a2 (by decide), g5 .a2 (by decide), i2]) (by rw [g6 .t0 (by decide), g5 .t0 (by decide), it0])
    (by rw [h46]; simp only [decide_eq_true_eq]) (by omega_arith) hw' (by omega_arith) aP aO (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₇ ⟨hv, o7, k7⟩ => ?_)
  rw [tl6] at hv
  have k17 := k16.trans k7
  -- `a5` back at `T`.
  have hpost : WP isa (.block finishPost) s₇ fun s₈ =>
      (s₈.gpr .a5 = off B dT ∧ s₈.mem = s₇.mem) ∧ Keep [.a5, .t3] s₇ s₈ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold finishPost
    have e5 : s₇.gpr .a5 = off B (dT + 8 * w) := by rw [k7.gpr (by decide), g6 .a5 (by decide), j5]
    have e0 : s₇.gpr .t0 = BitVec.ofNat 64 w := by
      rw [k7.gpr (by decide), g6 .t0 (by decide), g5 .t0 (by decide), it0]
    brun [e5, e0, sqr_shl3, off_sub B (show 8 * w ≤ dT + 8 * w by omega_arith), Nat.add_sub_cancel]
  refine WP.mono hpost fun t ⟨⟨j8, m8⟩, k8⟩ => ?_
  have k18 := k17.trans k8
  -- The result.
  have hM := wordsVal_lt s.mem B dM w
  have hM0 : 0 < wordsVal s.mem B dM w := by omega_arith
  have eT := fios_wordsVal_append s₄.mem B dT w w
  rw [z4, Nat.zero_add, show w + w = 2 * w by omega_arith] at eT
  rw [eT, show 64 * (2 * w) = 64 * w + 64 * w by omega_arith, Nat.pow_add, Nat.mul_assoc, ← Nat.mul_add] at r4
  have hR := wordsVal_lt s₄.mem B (dT + 8 * w) w
  have hDR := wordsVal_lt s₆.mem B dP w
  generalize wordsVal s.mem B dM w = M at *
  generalize wordsVal s.mem B dA w = A at *
  generalize wordsVal s₄.mem B (dT + 8 * w) w = Tl at *
  generalize s₄.gpr .a1 = top at *
  generalize 2 ^ (64 * w) = R at *
  have hX : Tl + R * (top.toNat + 2 ^ 64 * 0) < 2 * M := by
    rw [Nat.mul_zero, Nat.add_zero]
    have h1 : A * A < R * M := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hB (Nat.le_of_lt hB) hM0)
      (Nat.mul_le_mul_right _ (Nat.le_of_lt hM))
    have h2 : U * M < R * M := Nat.mul_lt_mul_of_pos_right hU hM0
    have : R * (Tl + R * top.toNat) < R * (2 * M) := by
      rw [r4, Nat.two_mul, Nat.mul_add]; exact Nat.add_lt_add h1 h2
    exact Nat.lt_of_mul_lt_mul_left this
  have hres : wordsVal t.mem B dO w = (Tl + R * top.toNat) % M := by
    have e := VG.Proof.Bignum.csub_result hM hDR hc hR hX hD
    rw [Nat.mul_zero, Nat.add_zero] at e
    rw [m8, hv, ← e]; by_cases h : top.toNat < c <;> simp [h]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm _ R, r4, Nat.add_mul_mod_self_right]
  · rw [m8]
    refine Arrays.trans (m₂ := s₅.mem) (arrays23_of_outside (by simp) (by simp) ?_) ?_
    · rw [hdT]
      exact (o13.mono (Nat.le_refl _) (by omega_arith)).trans
        ((o4.mono (Nat.le_refl _) (by omega_arith)).trans (o45.mono (by omega_arith) (by omega_arith)))
    refine Arrays.trans (m₂ := s₆.mem) (Arrays.of_outside (j := p) (by simp) o6 (by omega_arith) (by omega_arith)) ?_
    exact Arrays.of_outside (j := o) (by simp) o7 (by omega_arith) (by omega_arith)
  · have k := k18.mono (rs' := sqrRegs ++ [.a5]) (by decide)
    refine ⟨fun r hr => ?_, k.2⟩
    by_cases h5 : r = .a5
    · subst h5; rw [j8, i5]
    · exact k.1 r fun h => (List.mem_append.mp h).elim hr fun h' => h5 (List.mem_singleton.mp h')

/-- `sqrTailN_ok` for arrays below 8: the drop-in for `tail_ok` on squares,
the temporary at `a6` in any array but 0, 2, 3 and `o`. -/
theorem sqrTail_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a p : Nat} (ho : o < 8) (ha : a < 8) (hp : p < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3)
    (ha2 : a ≠ 2) (ha3 : a ≠ 3) (hp0 : p ≠ 0) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpo : p ≠ o)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (i2 : s.gpr .a2 = off B (slot w o)) (i3 : s.gpr .a3 = off B (slot w a))
    (i5 : s.gpr .a5 = off B (slot w 2)) (i6 : s.gpr .a6 = off B (slot w p))
    (i7 : s.gpr .a7 = off B (slot w 0)) (it0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w) :
    WP isa sqrTail s fun t =>
      (wordsVal t.mem B (slot w o) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w o) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w a) w * wordsVal s.mem B (slot w a) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, p, o] s.mem t.mem) ∧
      Keep sqrRegs s t :=
  sqrTailN_ok hs (by decide) ho ha hp ho2 ho3 ha2 ha3 hp0 hp2 hp3 hpo hw2 hw' hZ i2 i3 i5 i6 i7 it0 hinv hB

end VG.Proof.Bignum.RISCV64

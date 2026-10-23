module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA public-key operation on PPC64LE: the power

`step_ok`: a step of the scan, as congruences: `S R ≡ a² (mod n)`,
`P R ≡ S (x R) (mod n)` and `a := P` or `S` by the top bit of `r24`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE

/-- A digit apart from every range that changed. -/
theorem Outs.w32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have := h.val32 (d := d) (k := 1) (by simpa using hd) (by omega)
  simpa [val32] using this

theorem top_bit (x : BitVec 64) :
    x >>> 63 = BitVec.ofNat 64 (if 2 ^ 63 ≤ x.toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  split <;> omega

/-- The block before the selection: the mask of `r24`'s top bit in `r20`,
`r24` shifted, and the bases of arrays 1, 4 and 5. -/
theorem selBlock_ok {t : State} {B : Addr} {w : Nat} (h10 : t.gpr .r10 = off B (slot w 0))
    (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block ([.lsr .d .r0 .r24 63, .li .r3 0, .sub .r20 .r3 .r0, .lsl .r24 .r24 1] ++
        base .r8 1 ++ base .r9 4 ++ base .r5 5)) t fun t' =>
      (t'.gpr .r20 = BitVec.ofNat 64 0 -
          BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0) ∧
        t'.gpr .r24 = t.gpr .r24 <<< 1 ∧ t'.gpr .r8 = off B (slot w 1) ∧ t'.gpr .r9 = off B (slot w 4) ∧
        t'.gpr .r5 = off B (slot w 5) ∧ t'.mem = t.mem) ∧
      Keep [.r0, .r3, .r20, .r24, .r8, .r9, .r5] t t' := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r20, .r24] (Q := fun t₁ => t₁.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0) ∧
      t₁.gpr .r24 = t.gpr .r24 <<< 1 ∧ t₁.mem = t.mem) (by prun [top_bit]; simp) (by decide))
    fun t₁ ⟨⟨a20, a24, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 1) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 4) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (base_ok (rd := .r5) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 5) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ⟨⟨?_, ?_, ?_, ?_, a5, ?_⟩, (k13.trans k4).mono⟩
  · rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), a20]
  · rw [k4.gpr .r24 (by decide), k3.gpr .r24 (by decide), k2.gpr .r24 (by decide), a24]
  · rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8]
  · rw [k4.gpr .r9 (by decide), a9]
  · rw [m4, m3, m2, m1]

/-- The arrays a step changes. -/
def stepRs (w : Nat) : List (Nat × Nat) :=
  [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 1, 8 * (w + 2)),
    (slot w 5, 8 * (w + 2))]

/-- The registers a step writes. -/
def stepRegs : List Reg := montRegs ++ [.r0, .r3, .r20, .r24, .r14, .r15, .r16, .r17]

/-- A step of the scan, `a` in array 5 and `x R mod n` in array 6, both below
`n` (array 0). -/
theorem step_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : val32 s.mem B (slot w 5) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (hX : val32 s.mem B (slot w 6) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa PublicChecked.step s fun t =>
      (∃ S P, S < val32 s.mem B (slot w 0) (2 * w) ∧ P < val32 s.mem B (slot w 0) (2 * w) ∧
        S * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w 5) (2 * w) * val32 s.mem B (slot w 5) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        P * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          S * val32 s.mem B (slot w 6) (2 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w 5) (2 * w) = if decide (2 ^ 63 ≤ (s.gpr .r24).toNat) then P else S) ∧
      Outs B (stepRs w) s.mem t.mem ∧ t.gpr .r24 = s.gpr .r24 <<< 1 ∧ Keep stepRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  unfold PublicChecked.step
  -- `S := a²` into array 4.
  refine WP.seq (WP.mono (montOp_ok (o := 4) (a := 5) (b := 5) hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ h10 h29 h11 h12 hinv hA)
    fun s₁ ⟨⟨hS, eS, o1⟩, k1⟩ => ?_)
  have ap : ∀ {j : Nat} {ks : List Nat}, (∀ k ∈ ks, k ≠ j) →
      ∀ r ∈ ks.map (fun k => (slot w k, 8 * (w + 2))), slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j ks h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact sp (Ne.symm (h k hk))
  have o1' : Outs B ([2, 3, 4].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem := o1
  have hd1 : ∀ {j}, j < 8 → j ≠ 2 → j ≠ 3 → j ≠ 4 →
      val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) := by
    intro j hj h2 h3 h4
    exact o1'.val32 (fun r hr => by have := ap (j := j) (ks := [2, 3, 4]) (by simp; omega) r hr; omega)
      (by have := sl _ hj; omega)
  have hw1 : w32 s₁.mem B (slot w 0) = w32 s.mem B (slot w 0) :=
    Outs.w32 o1' (fun r hr => by have := ap (j := 0) (ks := [2, 3, 4]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  have N1 := hd1 (j := 0) (by decide) (by decide) (by decide) (by decide)
  have X1 := hd1 (j := 6) (by decide) (by decide) (by decide) (by decide)
  -- `P := S x` into array 1.
  refine WP.seq (WP.mono (montOp_ok (o := 1) (a := 4) (b := 6) (hs.congr k1.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ
    ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11)
    (by rw [k1.gpr .r12 (by decide)]; exact h12) (by rw [hw1, k1.gpr .r12 (by decide)]; exact hinv)
    (by rw [X1, N1]; exact hX)) fun s₂ ⟨⟨hP, eP, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have o2' : Outs B ([2, 3, 1].map fun k => (slot w k, 8 * (w + 2))) s₁.mem s₂.mem := o2
  have hd2 : ∀ {j}, j < 8 → j ≠ 2 → j ≠ 3 → j ≠ 1 →
      val32 s₂.mem B (slot w j) (2 * w) = val32 s₁.mem B (slot w j) (2 * w) := by
    intro j hj h2 h3 h1
    exact o2'.val32 (fun r hr => by have := ap (j := j) (ks := [2, 3, 1]) (by simp; omega) r hr; omega)
      (by have := sl _ hj; omega)
  rw [N1] at hP
  rw [N1, X1] at eP
  -- The selection.
  refine WP.seq (WP.mono (selBlock_ok (B := B) (w := w) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29)) fun s₃ ⟨⟨a20, a24, a8, a9, a5, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 1) (dT := slot w 4) (dO := slot w 5)
    (hs.congr k13.wr) a8 a9 a5 ((k13.gpr _ (by decide)).trans h11) a20 (by omega) (by omega)
    (by have := sl 1 (by decide); omega) (by have := sl 4 (by decide); omega)
    (by have := sl 5 (by decide); omega) (by have := sp (show (5 : Nat) ≠ 1 by decide); omega)
    (by have := sp (show (5 : Nat) ≠ 4 by decide); omega)) fun t ⟨hv, out, k4⟩ => ?_
  refine ⟨⟨val32 s₁.mem B (slot w 4) (2 * w), val32 s₂.mem B (slot w 1) (2 * w), hS, hP, eS, eP, ?_⟩,
    ?_, ?_, ((k13.trans k4).mono)⟩
  · rw [hv, m3, hd2 (j := 4) (by decide) (by decide) (by decide) (by decide), k12.gpr .r24 (by decide)]
  · refine Outs.trans (Outs.mono o1 (by simp [stepRs])) (Outs.trans (Outs.mono o2 (by simp [stepRs])) ?_)
    rw [m3] at out
    exact Outs.of_outside (o := slot w 5) (n := 8 * (w + 2)) (out.mono (Nat.le_refl _) (by omega))
      (by simp [stepRs])
  · rw [k4.gpr .r24 (by decide), a24, k12.gpr .r24 (by decide)]

end VG.Proof.Bignum.PPC64LE.Pub

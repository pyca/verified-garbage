module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Shared prepared-workspace views and byte-preserving congruence -/

@[expose] public section
namespace VG.Proof.MillerRabin.Workspace
open VG
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

def LayoutLite (m : Mem) (ws : Addr) (len : Nat) : Prop :=
  Spec.Rsa.Mont.Layout m ws len ∧ 4 ≤ wOf m ws ∧ wOf m ws ≤ 128 ∧ arrAt (wOf m ws) 28 ≤ 8 * len

def PreparedLite (m : Mem) (ws : Addr) : Prop :=
  let w := wOf m ws
  let c := numAt m ws w 0
  let R := 2 ^ (64 * w)
  3 ≤ c ∧ c % 2 = 1 ∧
    ((m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64).toNat * (wordAt m ws Spec.Rsa.Mont.minvWord).toNat + 1) %
      2 ^ 64 = 0 ∧
    numAt m ws w 5 < c ∧ numAt m ws w 9 = R % c ∧ numAt m ws w 10 = c - R % c ∧
    numAt m ws w 27 = Spec.MillerRabin.exponent c ∧
    m.readW (ws + BitVec.ofNat 64 (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64)

/-! ## Memory that keeps its bytes -/

section
variable {m m' : Mem} {ws : Addr} {len : Nat}

theorem read_congr_on (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {d n : Nat} (hd : d + n ≤ 8 * len) : m'.read (ws + BitVec.ofNat 64 d) n = m.read (ws + BitVec.ofNat 64 d) n :=
  Mem.read_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

theorem readW_congr_on (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {d : Nat} (hd : d + 8 ≤ 8 * len) : m'.readW (ws + BitVec.ofNat 64 d) 64 = m.readW (ws + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW, read_congr_on h hd]

theorem layout_header_congr
    (width : wordAt m' ws Spec.Rsa.Mont.wWord = wordAt m ws Spec.Rsa.Mont.wWord)
    (pointers : ∀ j < 8, wordAt m' ws (Spec.Rsa.Mont.arrWord j) = wordAt m ws (Spec.Rsa.Mont.arrWord j))
    (hl : LayoutLite m ws len) : LayoutLite m' ws len ∧ wOf m' ws = wOf m ws := by
  have hw : wOf m' ws = wOf m ws := congrArg BitVec.toNat width
  refine ⟨⟨?_, by rw [hw]; exact hl.2.1, by rw [hw]; exact hl.2.2.1,
    by rw [hw]; exact hl.2.2.2⟩, hw⟩
  unfold LayoutLite at hl
  unfold Spec.Rsa.Mont.Layout at hl ⊢
  rw [hw]
  exact ⟨hl.1.1, hl.1.2.1, hl.1.2.2.1, fun j hj => (pointers j hj).trans (hl.1.2.2.2 j hj)⟩

theorem layout_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    (hl : LayoutLite m ws len) : LayoutLite m' ws len ∧ wOf m' ws = wOf m ws := by
  have h256 : 256 ≤ 8 * len := Nat.le_trans (Nat.le_add_right _ _) hl.2.2.2
  apply layout_header_congr ?_ ?_ hl
  · exact readW_congr_on h (d := 48) (by omega)
  · intro j hj
    exact readW_congr_on h (d := 8 * (Spec.Rsa.Mont.arrWord j))
      (by unfold Spec.Rsa.Mont.arrWord; omega)

theorem compact_layout_header_congr
    (width : wordAt m' ws Spec.Rsa.Mont.wWord = wordAt m ws Spec.Rsa.Mont.wWord)
    (pointers : ∀ j < 8, wordAt m' ws (Spec.Rsa.Mont.arrWord j) = wordAt m ws (Spec.Rsa.Mont.arrWord j))
    (stride : wordAt m' ws 28 = wordAt m ws 28)
    (hl : Spec.MillerRabin.Layout Spec.MillerRabin.compact m ws len) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact m' ws len ∧ wOf m' ws = wOf m ws := by
  rcases hl with ⟨_, mont, lower, upper, fit, step⟩
  have lite : LayoutLite m ws len := ⟨mont, lower, upper, fit⟩
  obtain ⟨L, hw⟩ := layout_header_congr width pointers lite
  refine ⟨⟨.inr rfl, L.1, L.2.1, L.2.2.1, L.2.2.2, ?_⟩, hw⟩
  change wordAt m' ws 28 = BitVec.ofNat 64 (8 * (wOf m' ws + 2))
  change wordAt m ws 28 = BitVec.ofNat 64 (8 * (wOf m ws + 2)) at step
  rw [stride, hw]
  exact step

theorem numAt_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    {w j : Nat} (hj : arrAt w j + 8 * w ≤ 8 * len) : numAt m' ws w j = numAt m ws w j := by
  unfold numAt; rw [read_congr_on h hj]

theorem prepared_congr (h : ∀ i < 8 * len, m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i))
    (hl : LayoutLite m ws len) (hp : PreparedLite m ws) : PreparedLite m' ws := by
  obtain ⟨_, hw⟩ := layout_congr h hl
  have fits := hl.2.2.2
  have w4 := hl.2.1
  generalize hW : wOf m ws = w at fits w4
  have fit : ∀ j < 28, arrAt w j + 8 * (w + 2) ≤ 8 * len := fun j hj => by
    have : j * (8 * (w + 2)) ≤ 27 * (8 * (w + 2)) := Nat.mul_le_mul_right _ (by omega)
    simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits ⊢
    generalize 8 * (w + 2) = S at this fits ⊢
    omega
  unfold PreparedLite at hp ⊢
  simp only [hw, hW] at hp ⊢
  rw [numAt_congr h (by have := fit 0 (by omega); omega), numAt_congr h (by have := fit 5 (by omega); omega),
    numAt_congr h (by have := fit 9 (by omega); omega), numAt_congr h (by have := fit 10 (by omega); omega),
    numAt_congr h (by have := fit 27 (by omega); omega),
    readW_congr_on h (d := arrAt w 27 + 8 * w) (by have := fit 27 (by omega); omega)]
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  have e1 : m'.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 = m.readW (ws + BitVec.ofNat 64 (arrAt w 0)) 64 :=
    readW_congr_on h (by have := fit 0 (by omega); simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at this ⊢; omega)
  have e2 : wordAt m' ws Spec.Rsa.Mont.minvWord = wordAt m ws Spec.Rsa.Mont.minvWord :=
    readW_congr_on h (by have := fit 0 (by omega); simp only [arrAt, Spec.Rsa.Mont.hdrBytes, Spec.Rsa.Mont.minvWord] at this ⊢; omega)
  rw [e1, e2]
  exact hp.2.2.1

theorem workspace_congr {m m' : Mem} {base : Addr} {len : Nat}
    (same : ∀ i < 8 * len, m' (base + BitVec.ofNat 64 i) = m (base + BitVec.ofNat 64 i))
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact m base len)
    (prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact m base) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact m' base len ∧
      Spec.MillerRabin.Prepared Spec.MillerRabin.compact m' base ∧ wOf m' base = wOf m base := by
  rcases layout with ⟨_, mont, lower, upper, fit, stride⟩
  change arrAt (wOf m base) 28 ≤ 8 * len at fit
  have lite : VG.Proof.MillerRabin.Workspace.LayoutLite m base len := ⟨mont, lower, upper, fit⟩
  obtain ⟨lite', width⟩ := VG.Proof.MillerRabin.Workspace.layout_congr same lite
  have prepared' : Spec.MillerRabin.Prepared Spec.MillerRabin.compact m' base :=
    VG.Proof.MillerRabin.Workspace.prepared_congr same lite prepared
  refine ⟨⟨.inr rfl, lite'.1, lite'.2.1, lite'.2.2.1, lite'.2.2.2, ?_⟩, prepared', width⟩
  change wordAt m' base 28 = BitVec.ofNat 64 (8 * (wOf m' base + 2))
  change wordAt m base 28 = BitVec.ofNat 64 (8 * (wOf m base + 2)) at stride
  have hdrFit : 256 ≤ 8 * len := Nat.le_trans (Nat.le_add_right _ _) fit
  rw [wordAt, VG.Proof.MillerRabin.Workspace.readW_congr_on same (by omega), width]
  exact stride

end

end VG.Proof.MillerRabin.Workspace

module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The precomputed values of an RSA modulus on PPC64LE: the arithmetic

`core_ok`: from the state after `setup`, loading `n`, checking it and either
computing `R² mod n` and writing both, or zeroing `pre`; only the arrays and
`pre` change.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Proof.Bignum.PPC64LE

/-- The arrays 0–3 of a working space at `S`. -/
abbrev arrR (S : Addr) (w : Nat) : Region := ⟨off S hdrBytes, 32 * (w + 2)⟩

/-- Memory that changed only at offsets `[o, o + n)` of `B` changed only in
the region from `B + d` of `L` bytes that holds them. -/
theorem frame_of_outside {B : Addr} {o n d L Z : Nat} {m m' : Mem} (h : Outside B o n m m')
    (hd : d ≤ o) (hL : o + n ≤ d + L) (hZ : d + L < Z) (hB : B.toNat + Z ≤ 2 ^ 64) :
    Frame [⟨off B d, L⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine h x ?_
  simp only [ofs]
  have e : (x - off B d).toNat = (2 ^ 64 - d + (x - B).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x B (by omega)
  rw [e] at hc
  have := (x - B).isLt
  rcases Nat.lt_or_ge (x - B).toNat d with h1 | h1
  · left; omega
  · right
    rw [show 2 ^ 64 - d + (x - B).toNat = (x - B).toNat - d + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega

theorem val32_eq_wv (m : Mem) (P : Addr) (d W : Nat) : Mont.val32 m P d (2 * W) = wv m P d W := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_wv, show 4 * (2 * W) = 8 * W by omega]

theorem frame_of_outside0 {B : Addr} {n L : Nat} {m m' : Mem} (h : Outside B 0 n m m') (hL : n ≤ L) :
    Frame [⟨B, L⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  exact h x (Or.inr (by simp only [ofs]; omega))

/-- The postcondition on `pre` and the return value. -/
def preOut (nb : List Byte) (P : Addr) (pl : Nat) (r : BitVec 64) (m : Mem) : Prop :=
  match Spec.Rsa.publicPrecompute nb with
  | some ws => r.setWidth 32 = 1 ∧ Spec.Rsa.wordsAt m P pl = ws
  | none => r.setWidth 32 = 0 ∧ Spec.Rsa.wordsAt m P pl = List.replicate pl 0

/-- The registers the arithmetic writes. -/
def coreRegs : List Reg := [.r0, .r3, .r4, .r14, .r15, .r16, .r17, .r18, .r20]

/-- From the state after `setup`: `pre` and the return value, with only the
arrays and `pre` changed. -/
theorem core_ok {s : State} {P N S : Addr} {Z k w : Nat} (hs : Scr s S Z) (hp : Scr s P (16 * w))
    (hw : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024) (hZ : slot w 8 ≤ Z)
    (h19 : s.gpr .r19 = P) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (h12 : s.gpr .r12 = N)
    (h10 : s.gpr .r10 = off S (slot w 0)) (h5 : s.gpr .r5 = off S (slot w 1))
    (h8 : s.gpr .r8 = off S (slot w 2)) (h9 : s.gpr .r9 = off S (slot w 3))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hNS : ∀ i < k, ∀ x, ofs S x < Z → off N i ≠ x) (hPS : ∀ x, ofs S x < Z → 16 * w ≤ ofs P x) :
    WP isa core s fun t =>
      (preOut (Spec.Rsa.bytesAt s.mem N k) P (2 * w) (t.gpr .r3) t.mem ∧
        Frame [arrR S w, ⟨P, 16 * w⟩] s.mem t.mem) ∧ Keep coreRegs s t := by
  have hnw := hs.nowrap
  have hnp := hp.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hw1 : 8 ≤ w := by omega
  have hw' : w < 2 ^ 31 := by omega
  unfold core
  -- `n` into array 0.
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 0) hs h10 (by rw [h12]; simp) h6 h11 (by omega)
    (by omega) hw' (by omega) (by omega) hrd hNS) fun s₁ ⟨hv₁, out₁, k₁⟩ => ?_)
  have hN₁ : ∀ i < k, s₁.mem (off N i) = s.mem (off N i) := fun i hi => out₁ _ (Or.inr (by
    have := hNS i hi (off N i)
    simp only [Mont.ofs, ofs] at this ⊢
    by_contra hc; exact this (by omega) rfl))
  -- The check.
  refine WP.seq (WP.mono (check_ok (N := N) (nb := Spec.Rsa.bytesAt s.mem N k) (k₁.gpr .r12 (by decide) |>.trans
    (by rw [h12]; simp)) (k₁.gpr .r6 (by decide) |>.trans h6) hk hk' (bytesAt_length _ _ _)
    (by rw [k₁.rd, k₁.wr]; exact hrd) fun i hi => by
      rw [hN₁ i hi]; simp [Spec.Rsa.bytesAt, off]) fun s₂ ⟨hc₂, m₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hp₂ := hp.congr k12.wr
  have fr₁ : Frame [arrR S w] s.mem s₂.mem := by
    rw [m₂]; exact frame_of_outside (d := hdrBytes) (L := 32 * (w + 2)) (Z := Z) (fun x hx => out₁ x hx)
      (by omega) (by omega) (by omega) hnw
  have g : ∀ r ∈ [Reg.r19, .r5, .r8, .r9, .r10, .r11], s₂.gpr r = s.gpr r := fun r hr =>
    k12.gpr r (by revert r hr; decide)
  refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k = true :=
      hc₂.mp (by simpa using hb)
    have hf := valid_facts hv hk
    rw [← hw] at hf
    refine WP.seq (WP.mono (r2_ok hs₂ (by rw [g .r8 (by decide), h8]) (by rw [g .r9 (by decide), h9])
      (by rw [g .r10 (by decide), h10]) (by rw [g .r5 (by decide), h5]) (by rw [g .r11 (by decide), h11])
      (by omega) hw' (by omega) (by rw [m₂, hv₁]; omega)) fun s₃ ⟨hx₃, out₃, k₃⟩ => ?_)
    have k13 := k12.trans k₃
    refine WP.seq (WP.mono (write_ok (P := P) (dN := slot w 0) (dX := slot w 1) (hs.congr k13.wr) (hp.congr k13.wr)
      (by rw [k13.gpr .r19 (by decide) |>.trans h19]; simp) (by rw [k13.gpr .r10 (by decide), h10])
      (by rw [k13.gpr .r5 (by decide), h5]) (by rw [k13.gpr .r11 (by decide), h11]) (by omega) hw'
      (by omega) (by omega) (Nat.le_refl _) hPS) fun s₄ ⟨⟨hwN, hwX, out₄⟩, k₄⟩ => ?_)
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = 1 ∧ t.mem = s₄.mem) (by prun; rfl) (by decide))
      fun t ⟨⟨t3, tm⟩, k₅⟩ => ⟨⟨?_, ?_⟩, (((k13.trans k₄).trans k₅).mono)⟩
    · have hN0 : Mont.val32 s₃.mem S (slot w 0) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) := by
        rw [out₃.val32 (by omega) (by omega), m₂, hv₁]
      have hX : Mont.val32 s₃.mem S (slot w 1) (2 * w) =
          2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) := by
        rw [hx₃, m₂, hv₁]
      rw [preOut, publicPrecompute_some (bytesAt_length _ _ _) hv, ← hw]
      refine ⟨by rw [t3]; rfl, ?_⟩
      rw [tm]
      refine wordsAt_two (fun i hi => ?_) (fun i hi => ?_)
      · rw [hwN i hi, word_eq_ofNat _ _ _ w hi, ← val32_eq_wv, hN0]
      · rw [hwX i hi, word_eq_ofNat _ _ _ w hi, ← val32_eq_wv, hX]
    · rw [tm]
      refine ((fr₁.mono (by simp)).trans ?_).trans ((frame_of_outside0 out₄ (Nat.le_refl _)).mono (by simp))
      exact (frame_of_outside (d := hdrBytes) (L := 32 * (w + 2)) (Z := Z) (fun x hx => out₃ x hx)
        (by omega) (by omega) (by omega) hnw).mono (by simp)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k = false := by
      cases h : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k)) k
      · rfl
      · exact absurd (hc₂.mpr h) (by simpa using hb)
    refine WP.seq (WP.mono (zeroPre_ok hp₂ (by rw [g .r19 (by decide), h19]; simp)
      (by rw [g .r11 (by decide), h11]) (by omega) hw' (Nat.le_refl _)) fun s₃ ⟨⟨hz, out₃⟩, k₃⟩ => ?_)
    refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = 0 ∧ t.mem = s₃.mem) (by prun; rfl) (by decide))
      fun t ⟨⟨t3, tm⟩, k₄⟩ => ⟨⟨?_, ?_⟩, (((k12.trans k₃).trans k₄).mono)⟩
    · have hn : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem N k) = none := by
        simp only [Spec.Rsa.publicPrecompute, bytesAt_length, hv, Bool.false_eq_true, ite_false]
      rw [preOut, hn]
      refine ⟨by rw [t3]; rfl, ?_⟩
      rw [tm]
      apply List.ext_getElem (by simp [Spec.Rsa.wordsAt])
      intro i h1 h2
      simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      have := hz i (by simpa [Spec.Rsa.wordsAt] using h1)
      exact this
    · rw [tm]
      exact (fr₁.mono (by simp)).trans ((frame_of_outside0 out₃ (Nat.le_refl _)).mono (by simp))

end VG.Proof.Bignum.PPC64LE.Pre

module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: after p's check

In the working space of `Domain/Body.lean`, p in array 0, x's, `y`'s and
`rand`'s addresses in the header's words 8, 10 and 11: `gkBody_ok`, x cut
from `rand` (`scalar_ok`), then `vg_ffdh_derive_public`'s body
(`Derive.dpBody_ok`), then x masked by the status being 1 (`maskX_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The octets x is cut to, from `rand`'s at `R` and the bound's. -/
def gkOct (m : Mem) (D R : Addr) (k L : Nat) : List Byte :=
  cut (Spec.Rsa.bytesAt m R k) (lead (Spec.Rsa.bytesAt m (bptr D k L) k)) (smeared (Spec.Rsa.bytesAt m (bptr D k L) k))

/-- The status of x: 2 out of range, else 1 if `1 < g^x mod p < p − 1`, else 3. -/
def gkSt (x g p b : Nat) : Nat :=
  if ¬ (0 < x ∧ x < b) then 2 else if 1 < g ^ x % p ∧ g ^ x % p < p - 1 then 1 else 3

theorem gkSt_range (x g p b : Nat) : 1 ≤ gkSt x g p b ∧ gkSt x g p b < 4 := by
  unfold gkSt; split
  · decide
  · split <;> decide

/-- The registers `gkBody` writes. -/
def gkBodyRegs : List Reg := scalarRegs ++ Derive.dpBodyRegs ++ ([.r0, .r6, .r12, .r16, .r17, .r25] : List Reg)

/-- What a change at x's `k` octets keeps: the working space. -/
theorem out_scr {X B : Addr} {Z k : Nat} {m m' : Mem} (h : Outside X 0 k m m')
    (hsep : ∀ y, ofs B y < Z → k ≤ ofs X y) : Outside B Z (2 ^ 64) m m' := fun y hy => h y (Or.inr (by
  rcases hy with hy | hy
  · have := hsep y hy; omega
  · have := (y - B).isLt; simp only [ofs] at hy; omega))

/-- `gkBody`: x cut from `rand`, then `g^x mod p` or zeros at `O` and the
status; zeros at x but for the status 1. -/
theorem gkBody_ok {s : State} {B D X O R : Addr} {Z w k L p : Nat} (h : Env s B Z w)
    (h23 : s.gpr .r23 = B) (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hwk : w = (k + 7) / 8) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hL : L = 2 * k ∨ L = 3 * k)
    (hX : s.mem.readW (off B 64) 64 = off X 0) (hXL : s.mem.readW (off B 72) 64 = BitVec.ofNat 64 k)
    (hO : s.mem.readW (off B 80) 64 = off O 0) (hR : s.mem.readW (off B 88) 64 = off R 0)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hx : Scr s X k) (hsepX : ∀ i < k, ∀ y, ofs B y < Z → off X i ≠ y) (hsepBX : ∀ y, ofs B y < Z → k ≤ ofs X y)
    (hsepRX : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) (hsepDX : ∀ i < L, ∀ y, ofs X y < k → off D i ≠ y)
    (hsepXO : ∀ i < k, ∀ y, ofs O y < k → off X i ≠ y) (hsepOX : ∀ i < k, ∀ y, ofs X y < k → off O i ≠ y)
    (ho : Scr s O k) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs B x) (hsepB : ∀ x, ofs B x < Z → k ≤ ofs O x)
    (hP : arr s.mem B w 0 = p) (hp2 : 2 ≤ p) (hodd : p % 2 = 1) (hpk : p < 256 ^ k) :
    WP isa gkBody s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (gkSt (Spec.Rsa.os2ip (gkOct s.mem D R k L))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p)) ∧
        Spec.Rsa.bytesAt t.mem O k = (if gkSt (Spec.Rsa.os2ip (gkOct s.mem D R k L))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
          Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^
            Spec.Rsa.os2ip (gkOct s.mem D R k L) % p) k else List.replicate k 0) ∧
        Spec.Rsa.bytesAt t.mem X k = (if gkSt (Spec.Rsa.os2ip (gkOct s.mem D R k L))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1 then
          gkOct s.mem D R k L else List.replicate k 0) ∧
        ∀ d, d + 8 ≤ 256 → word t.mem B d = word s.mem B d) ∧ Keep gkBodyRegs s t := by
  have hs := h.hs
  have hZ := h.hZ
  have hnw := hs.nowrap
  have e0 := Domain.slot_eq w 0; have e28 := Domain.slot_eq w 28
  unfold gkBody
  refine WP.seq (WP.mono (scalar_ok h h23 h21 h27 h28 hk hk' hL hX hR hrdD hrdR hx hsepRX)
    fun s₃ ⟨⟨xb, xout⟩, k3⟩ => ?_)
  have osc := out_scr xout hsepBX
  have hw3 : ∀ d, d + 8 ≤ 256 → word s₃.mem B d = word s.mem B d := fun d hd =>
    Outside.word osc (Or.inl (by omega)) (by omega)
  have hp3 : arr s₃.mem B w 0 = p := by
    rw [arr, Outside.val32 osc (Or.inl (by omega)) (by omega)]; exact hP
  have hbD : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs X y < k → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
    outside_bytesAt xout (by omega) hq
  have sepG : ∀ i < k, ∀ y, ofs X y < k → off (off D k) i ≠ y := fun i hi => by
    rw [off_off']; exact hsepDX _ (by omega)
  have eb : Derive.bnd s₃.mem D k L p = Derive.bnd s.mem D k L p := by
    unfold Derive.bnd
    by_cases hq : L = 3 * k
    · rw [ite_eq_left hq, ite_eq_left hq, hbD _ _ fun i hi => by rw [off_off']; exact hsepDX _ (by omega)]
    · rw [ite_eq_right hq, ite_eq_right hq]
  have e3 := h.keep k3 (by decide)
  refine WP.seq (WP.mono (Derive.dpBody_ok (X := X) (O := O) (xl := k) (x := Spec.Rsa.os2ip (gkOct s.mem D R k L)) e3 ((k3.gpr .r23 (by decide)).trans h23)
    ((k3.gpr .r21 (by decide)).trans h21) ((k3.gpr .r27 (by decide)).trans h27)
    ((k3.gpr .r28 (by decide)).trans h28) hwk hk hk' hL (by omega) (Nat.le_refl _)
    (by show word s₃.mem B 64 = _; rw [hw3 64 (by omega)]; exact hX)
    (by show word s₃.mem B 72 = _; rw [hw3 72 (by omega)]; exact hXL)
    (by show word s₃.mem B 80 = _; rw [hw3 80 (by omega)]; exact hO)
    (by rw [k3.rd, k3.wr]; exact hrdD) hsepD (fun i hi => (hx.congr k3.wr).ld (d := i) (n := 1) (by omega)) hsepX
    (ho.congr k3.wr) hsepO hsepB hp3 hp2 hodd hpk (congrArg _ xb) (congrArg _ (hbD _ _ sepG)) eb)
    fun s₄ ⟨⟨yb, st4, w4, fr4⟩, k4⟩ => ?_)
  generalize hxv : Spec.Rsa.os2ip (gkOct s.mem D R k L) = xv at yb st4 ⊢
  have hxb : Spec.Rsa.bytesAt s₄.mem X k = gkOct s.mem D R k L := by
    rw [fr4 X k hsepX hsepXO, xb]; rfl
  have k34 := k3.trans k4
  have hst : s₄.gpr .r3 = BitVec.ofNat 64 (gkSt xv (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p
      (Derive.bnd s.mem D k L p)) := by
    rw [st4]; unfold gkSt; rfl
  have hyb : Spec.Rsa.bytesAt s₄.mem O k = (if gkSt xv (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p
      (Derive.bnd s.mem D k L p) = 1 then Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^
        xv % p) k else List.replicate k 0) := by
    rw [yb]; unfold gkSt
    by_cases h1 : 0 < xv ∧ xv < Derive.bnd s.mem D k L p
    · by_cases h2 : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^ xv % p ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ^ xv % p < p - 1
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  have hX4 : s₄.mem.readW (off B 64) 64 = off X 0 := by
    show word s₄.mem B 64 = _; rw [w4 64 (by omega), hw3 64 (by omega)]; exact hX
  refine WP.mono (maskX_ok (hs.congr k34.wr) (by omega) ((k34.gpr .r23 (by decide)).trans h23)
    ((k34.gpr .r28 (by decide)).trans h28) hX4 (by omega) (by omega) (hx.congr k34.wr) hst
    (gkSt_range _ _ _ _).1 (gkSt_range _ _ _ _).2)
    fun t ⟨⟨tz, tout⟩, kt⟩ => ⟨⟨?_, ?_, ?_, fun d hd => ?_⟩, k34.trans kt⟩
  · rw [kt.gpr .r3 (by decide), hst]
  · rw [outside_bytesAt tout (by omega) hsepOX, hyb]
  · rw [tz, hxb]
  · refine (Outside.word_sep (d := d) tout hsepBX (by omega) (by omega) hnw).trans ?_
    show Mont.word _ B d = _
    rw [w4 d hd, hw3 d hd]

end VG.Proof.Ffdh.PPC64LE.GenerateKey

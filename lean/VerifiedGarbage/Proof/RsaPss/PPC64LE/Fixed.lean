module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre

/-!
# RSASSA-PSS verification on PPC64LE: `H'` for a given salt length

Untrusted: everything here is checked by Lean. `hashFixedG_ok`: `hashFixed`
writes what `finalize` writes for the `8 + hLen + salt_len` bytes of `M'` at
`oY` to `oDig`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_nil)

/-- Bytes of our part of the working space outside the ranges a `Same` covers. -/
theorem bytes_same {S : Addr} {t t' : State} {rgs : List (Nat × Nat)} (h : Same S t t' rgs) {d n : Nat}
    (hd : d + n ≤ oRsa) (hr : ∀ p ∈ rgs, d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    Spec.Sha256.bytesAt t'.mem (off S d) n = Spec.Sha256.bytesAt t.mem (off S d) n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have := h (d + i) (by omega_arith) fun p hp => by have := hr p hp; omega_arith
  simp only [view] at this
  rw [← off_off] at this
  exact this

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {D : Nat} {s : State} (F : Fits S s) {H : Hash}
  (hH : HashOK H)
include F hH

/-- `hashFixed`, for any `Base` whose `r19` is the salt's length `sl`. -/
theorem hashFixedG_ok (hD : H.D = D) {sl : Nat} (h19 : vf s .r19 = BitVec.ofNat 64 sl) {t : State}
    (h : Base S vf s t) (hsl : sl + 8 + D ≤ 2048) :
    WP isa (hashFixed H) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.FD =
        hH.fh (Spec.Sha256.bytesAt t.mem (off (S s) oY) (8 + D + sl)) := by
  have Fh := hfits hH
  have hY : oY = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hD64 := hH.hD64
  have g19 : ∀ {u : State}, Base S vf s u → u.gpr .r19 + BitVec.ofNat 64 (8 + H.D) =
      BitVec.ofNat 64 (8 + D + sl) := fun b => by
    rw [b.vs .r19 (by decide), h19, hD, BitVec.ofNat_add_ofNat]; congr 1; omega
  refine WP.seq (WP.mono (hInit_ok F hH h) fun t₁ ⟨b₁, g₁, s₁, r₁⟩ => ?_)
  refine WP.seq (wp_li (by decide) fun t₂ o₂ e₂ => wp_addi (h := by decide) fun t₃ o₃ e₃ =>
    wp_addi (h := by omega_arith) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r6] t₁ t₄ := (o₂.trans (o₃.trans o₄)).mono
  have b₄ := b₁.only F k₄
  refine WP.seq (WP.mono (hUpd_ok F hH b₄ (m := []) (by rw [k₄.mem]; exact r₁) (by rw [o₄.get .r4, o₃.get .r4, e₂]; rfl)
    (d := oY) (len := 8 + D + sl) (by rw [o₄.get .r5, e₃, o₂.get .r14, b₁.r14])
    (by rw [e₄, o₃.get .r19, o₂.get .r19, g19 b₁]) (Nat.le_refl _) (by omega_arith)) fun t₅ ⟨b₅, g₅, s₅, r₅⟩ => ?_)
  refine WP.seq (wp_addi (h := by omega_arith) fun t₆ o₆ e₆ => wp_nil ?_)
  have b₆ := b₅.only F o₆
  refine WP.mono (hFin_ok F hH b₆ (m := [] ++ Spec.Sha256.bytesAt t₄.mem (off (S s) oY) (8 + D + sl))
    (by rw [o₆.mem]; exact r₅) (by rw [e₆, g19 b₅, List.nil_append, Spec.Sha256.bytesAt]; simp)
    (by simp [Spec.Sha256.bytesAt]; omega_arith)) fun t' ⟨b', g', s', r'⟩ => ⟨b', fun r hr => ?_, ?_, ?_⟩
  · rw [g' r hr, pres_of o₆ (by decide) r hr, g₅ r hr, pres_of k₄ (by decide) r hr, g₁ r hr]
  · exact (((s₁.mono (by simp)).trans ((Same.of_mem k₄.mem _).trans (s₅.mono (by simp)))).trans
      (Same.of_mem o₆.mem _)).trans s'
  · obtain ⟨_, hSt, _, _, _, _⟩ := offs
    rw [r', List.nil_append, k₄.mem, bytes_same s₁ (by omega_arith) (by simp; omega_arith)]

end

section
variable {D : Nat} {s : State} (F : Fits Sp s) {H : Hash} (hH : HashOK H)
include F hH

theorem hashFixed_ok (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) (hsl : (s.gpr .r10).toNat + 8 + D ≤ 2048) :
    WP isa (hashFixed H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Sha256.bytesAt t'.mem (off (Sp s) oDig) H.FD =
        hH.fh (Spec.Sha256.bytesAt t.mem (off (Sp s) oY) (8 + D + (s.gpr .r10).toNat)) :=
  hashFixedG_ok F hH hD (vf := vP D) (sl := (s.gpr .r10).toNat) (by show s.gpr .r10 = _; rw [ofNat_toNat]) h hsl

end

end VG.Proof.RsaPss.PPC64LE

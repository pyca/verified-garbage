module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignChallenge
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignExpand
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignNonce

/-!
# `vg_ed25519_sign_cached` on PPC64LE, with its frame as an argument

The setup, the three phases and the restores (`signWith_wp`): `out` then
holds `R ‖ S`, RFC 8032's signature (`Proof.Ed25519.sign_pipeline`), given that
the first step leaves the seed's digest at `128(F)` and that `pk` is the seed's
public key. The first step hashes the seed (`signCached_wp`), or copies its
digest from `r4` (`signExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (bytesAt)

theorem signWith_wp (C : ShaOK) (B : BaseOk) {sn : Nat} {s : State} (hp : SignPre sn s) {digest : Prog isa}
    {seed : List Byte}
    (hd : ∀ t, SignInv s t → WP isa digest t fun t' => SignInv s t' ∧
      Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .r9, 192⟩, below s.sp 48] t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .r9 + BitVec.ofNat 64 128) 64 = Spec.Sha512.sha512 seed)
    (hpk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey seed) :
    WP isa (signWith digest) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign seed (msgB s) := by
  have F192 : Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .r9, 288⟩ := Offset.sub_base _ (by decide)
  have F0 : Region.Sub ⟨s.gpr .r9, 32⟩ ⟨s.gpr .r9, 288⟩ := Region.sub_prefix (by decide)
  unfold signWith
  refine WP.seq (WP.mono_syms (signSetup_ok hp) fun t₁ ⟨h₁, hk₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (signExpandWith_ok hp (hd t₁ h₁)) fun t₂ ⟨h₂, f₂, hs₂, hp₂⟩ sy₂ => ?_)
  have hk₂ : bytesAt t₂.mem (s.gpr .r9 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .r5) 32 := by
    rw [← hk₁]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left F192
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.bF.symm.sub_left F192
  refine WP.seq (WP.mono (signNonce_ok C B hp h₂ hp₂ (by rw [sy₂, sy₁])) fun t₃ ⟨h₃, f₃, hn₃, hr₃⟩ => ?_)
  have keep₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .r9, 288⟩ →
      (Region.Disjoint ⟨p, 32⟩ ⟨s.gpr .r9 + BitVec.ofNat 64 64, 128⟩) →
      bytesAt t₃.mem p 32 = bytesAt t₂.mem p 32 := fun hs hd =>
    bytes_keep f₃ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.cF.symm.sub_left hs
      · exact hd
      · exact hp.bF.symm.sub_left hs
      · exact (hp.oF.symm.sub_left hs).sub_right (Region.sub_prefix (by decide))
  have hk₃ := (keep₃ F192 (Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))).trans hk₂
  have hs₃ := (keep₃ F0 (Offset.base_disjoint _ (by decide) (by decide))).trans hs₂
  refine WP.seq (WP.mono (signChallenge_ok C hp h₃ hr₃ hn₃ hs₃ hk₃) fun t₄ ⟨h₄, hR, hS⟩ => ?_)
  have hFw : (⟨s.gpr .r9, 288⟩ : Region) ∈ t₄.rd ++ t₄.wr := List.mem_append_right _ (sign_Fw hp h₄)
  have hrl : ∀ p ∈ restoreList 224 signRegs, p.2 + 8 ≤ 288 := by decide
  refine restore_ok h₄ (by decide) (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ lr₅ m₅ _ => ⟨g₅, sp₅, lr₅, ?_⟩
  rw [m₅, Proof.Ed25519.signatureBytes_split, hR, hS]
  exact Proof.Ed25519.sign_pipeline _ _ _ hpk

theorem signCached_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : SignPre 32 s)
    (hpk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32)) :
    WP isa signCached s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign (bytesAt s.mem (s.gpr .r4) 32) (msgB s) :=
  signWith_wp C B hp (fun _ h => signHash_ok C hp h) hpk

/-- `vg_ed25519_sign_expanded`: the signature of every seed whose digest is at `r4` and whose
public key is at `r5`. -/
theorem signExpanded_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : SignPre 64 s) {seed : List Byte}
    (hs : bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed)
    (hpk : bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey seed) :
    WP isa signExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      bytesAt t.mem (s.gpr .r3) 64 = Spec.Ed25519.sign seed (msgB s) :=
  signWith_wp C B hp (fun _ h => WP.mono (signCopy_ok hp h) fun _ ⟨a, b, c⟩ => ⟨a, b, c.trans hs⟩) hpk

end VG.Proof.Ed25519.PPC64LE.Whole

module

import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignChallenge
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignExpand
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignNonce

/-!
# `vg_ed25519_sign_expanded` on RISCV64, with its frame as an argument

The setup, the three phases and the restores, from any first step that leaves
the seed's digest `D` at `128(F)` (`signWith_wp`): `out` then holds `R ‖ S`
(`signFrom`), which is RFC 8032's signature (`Proof.Ed25519.sign_pipeline`) for
the seed when `pk` is its public key. The first step copies the digest at
`expanded` (`signExpanded_wp`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64.Whole VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (bytesAt)

variable {sl : Nat}

/-- `R ‖ S` from the seed's digest `D`, the public key `pk` and the message. -/
def signFrom (D pk msg : List Byte) : List Byte :=
  let nonce := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (D.drop 32 ++ msg))
  let r := Spec.Ed25519.scalarBase nonce
  r ++ Spec.Ed25519.scalarMulAdd nonce (Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (r ++ pk ++ msg)))
    (Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune D))

theorem signFrom_sha512 (seed pk msg : List Byte) (hpk : pk = Spec.Ed25519.publicKey seed) :
    signFrom (Spec.Sha512.sha512 seed) pk msg = Spec.Ed25519.sign seed msg :=
  Proof.Ed25519.sign_pipeline seed pk msg hpk

theorem signWith_wp (C : ShaOK) (B : BaseOk) {first : Prog isa} {D : List Byte} {s : State} (hp : SignPre sl s)
    (hfirst : ∀ t, SignInv s t → WP isa first t fun t' => SignInv s t' ∧ Frame (expW s) t.mem t'.mem ∧
      bytesAt t'.mem (s.gpr .a6 + BitVec.ofNat 64 128) 64 = D) :
    WP isa (signWith first) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ bytesAt t.mem (s.gpr .a0) 64 = signFrom D (bytesAt s.mem (s.gpr .a2) 32) (msgB s) := by
  have F192 : Region.Sub ⟨s.gpr .a6 + BitVec.ofNat 64 192, 32⟩ ⟨s.gpr .a6, 288⟩ := Offset.sub_base _ (by decide)
  have F0 : Region.Sub ⟨s.gpr .a6, 32⟩ ⟨s.gpr .a6, 288⟩ := Region.sub_prefix (by decide)
  unfold signWith
  refine WP.seq (WP.mono_syms (signSetup_ok hp) fun t₁ ⟨h₁, hk₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (signExpandWith_ok hp (hfirst t₁ h₁)) fun t₂ ⟨h₂, f₂, hs₂, hp₂⟩ sy₂ => ?_)
  have hk₂ : bytesAt t₂.mem (s.gpr .a6 + BitVec.ofNat 64 192) 32 = bytesAt s.mem (s.gpr .a2) 32 := by
    rw [← hk₁]
    exact bytes_keep f₂ (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.cF.symm.sub_left F192
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact hp.bF.symm.sub_left F192
  refine WP.seq (WP.mono (signNonce_ok C B hp h₂ hp₂ (by rw [sy₂, sy₁])) fun t₃ ⟨h₃, f₃, hn₃, hr₃⟩ => ?_)
  have keep₃ : ∀ {p : Addr}, Region.Sub ⟨p, 32⟩ ⟨s.gpr .a6, 288⟩ →
      (Region.Disjoint ⟨p, 32⟩ ⟨s.gpr .a6 + BitVec.ofNat 64 64, 128⟩) →
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
  have hFw : (⟨s.gpr .a6, 288⟩ : Region) ∈ t₄.rd ++ t₄.wr := List.mem_append_right _ (sign_Fw hp h₄)
  have hrl : ∀ p ∈ restoreList 224 signRegs, p.2 + 8 ≤ 288 := by decide
  refine restore_ok h₄ hp.alF (h₄.regs _ (by decide)) (by decide) (by decide) (by decide) (by decide)
    (fun p hp' => in_base hFw (hrl p hp') (by have := hrl p hp'; omega))
    fun t₅ g₅ sp₅ ra₅ m₅ _ => ⟨g₅, sp₅, ra₅, ?_⟩
  rw [m₅, Proof.Ed25519.signatureBytes_split, hR, hS]
  rfl

/-- From the seed's digest at `expanded`: the signature of every seed with that digest, given
that `pk` is the public key of one. -/
theorem signExpanded_wp (C : ShaOK) (B : BaseOk) {s : State} (hp : SignPre 64 s)
    (hk : ∃ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed ∧
      bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey seed) :
    WP isa signExpanded s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      t.gpr .ra = s.gpr .ra ∧ ∀ seed : List Byte, bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
        bytesAt t.mem (s.gpr .a0) 64 = Spec.Ed25519.sign seed (msgB s) :=
  WP.mono (signWith_wp C B (D := bytesAt s.mem (s.gpr .a1) 64) hp fun _ h => signCopy_ok hp h) fun _ ⟨g, sp, ra, ho⟩ =>
    ⟨g, sp, ra, fun seed hs => by
      obtain ⟨s₀, h₀, hk₀⟩ := hk
      rw [ho, hs]
      exact signFrom_sha512 _ _ _ (hk₀.trans (Proof.Ed25519.publicKey_of_sha512_eq (h₀.symm.trans hs)))⟩

end VG.Proof.Ed25519.RISCV64.Whole

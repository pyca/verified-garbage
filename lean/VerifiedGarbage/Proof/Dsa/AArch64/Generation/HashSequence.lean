module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # All p-candidate hash contributions, with bounded public sequencing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hashPrefix_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) (k : Nat) (hk : k ≤ p.count + 1)
    {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashPrefix G p.len p.count k) s fun t =>
      HashState p Hs k t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem := by
  induction k generalizing s with
  | zero =>
    unfold Impl.Dsa.AArch64.Generation.pHashPrefix
    have he : WP isa (.block []) s (fun t => t = s) := by brun
    exact WP.mono he fun t h => by
      subst t
      exact ⟨hs, Step.refl _ _ _ _, Frame.refl _ _⟩
  | succ k ih =>
    unfold Impl.Dsa.AArch64.Generation.pHashPrefix
    refine WP.seq (WP.mono (ih (by omega) hs) fun u ⟨hu, su, hfu⟩ => ?_)
    refine WP.mono (hashStep_ok hG hHh hsize hd (by omega) hu) fun t ⟨ht, st, hft⟩ => ?_
    exact ⟨ht, su.trans st, hfu.trans hft⟩

theorem pHashes_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.AArch64.Generation.pHashes G p.len p.count) s fun t =>
      HashState p Hs (p.count + 1) t ∧ Step p.F p.S [⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame p.changed s.mem t.mem :=
  hashPrefix_ok hG hHh hsize hd _ (Nat.le_refl _) hs

end VG.Proof.Dsa.AArch64.Generation

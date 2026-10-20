module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
public import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
public import VerifiedGarbage.Proof.Dsa.AArch64.Failure
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashOne
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.Store
public import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashOne
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.RsaOaep

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

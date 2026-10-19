module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # All p-candidate hash contributions, with bounded public sequencing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashPrefix_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) (k : Nat) (hk : k ≤ p.count + 1)
    {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashPrefix G p.len p.count k) s fun t =>
      HashState p Hs k t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem := by
  induction k generalizing s with
  | zero =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    have he : WP isa (.block []) s (fun t => t = s) := by xrun
    exact WP.mono he fun t h => by
      subst t
      exact ⟨hs, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ k ih =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    refine WP.seq (WP.mono (ih (by omega) hs) fun u ⟨hu, rdu, wru, csu, hfu⟩ => ?_)
    refine WP.mono (hashStep_ok hG hHh hsize hd (by omega) hu) fun t ⟨ht, rdt, wrt, cst, hft⟩ => ?_
    exact ⟨ht, rdt.trans rdu, wrt.trans wru, fun r hr => (cst r hr).trans (csu r hr), hfu.trans hft⟩

theorem pHashes_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count) s fun t =>
      HashState p Hs (p.count + 1) t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem :=
  hashPrefix_ok hG hHh hsize hd _ (Nat.le_refl _) hs

end VG.Proof.Dsa.X86_64.Generation

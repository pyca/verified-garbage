module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorModulusCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorModulus

/-! # Compose fresh workspace initialization with generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure GeneratorFreshBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop where
  modulus : GeneratorModulusBefore len p s
  base : word s.mem p.B 272 = p.hp
  hSource : Src s p.B activeBytes p.hp p.hb
  eSource : Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.exponent) p.eb
  output : ∀ i < p.len, InRegions s.wr (off (off p.B VG.Impl.Dsa.Generation.Layout.g) i) 1

theorem generatorFresh_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorFreshBefore len p s) :
    WP isa (generatorModulus len) s (GeneratorPowerBefore p) := by
  have step := generatorModulus_ok h.modulus.1 h.modulus.2.1 p.width p.pLength
    h.modulus.2.2.1 p.pOdd
  rw [h.modulus.2.2.2] at step
  refine WP.mono step fun t ⟨mi, hg, child, _, ep, plen, gh, ff, hk⟩ => ?_
  have bounds : ∀ r ∈ [(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8),
      r.1 + r.2 ≤ activeBytes := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, initRanges] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · decide
    · decide
    · decide
    · rw [← h.modulus.2.2.2]
      rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
  have child' : ChildReady t.mem p.B pWorkspace (p.len / 8) (Spec.Dsa.decodeBE p.pb) mi := by
    rw [h.modulus.2.2.2]; exact child
  have plen' : word t.mem p.B 328 = BitVec.ofNat 64 p.len := by
    rw [h.modulus.2.2.2]; exact plen
  exact ⟨mi, hg, child', gh.trans h.base, ep, plen',
    h.hSource.congrK (InScr.of_frm ff bounds) hk,
    h.eSource.congrK (InScr.of_frm ff bounds) hk,
    fun i hi => by rw [hk.2.2]; exact h.output i hi⟩

theorem generatorPowerFresh_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorFreshBefore len)) (generatorPowerFresh Sq.mm M.mm len)
      (fun _ _ => True) := by
  unfold generatorPowerFresh
  exact RelCT.seq (two_post
    (two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.modulus) (generatorModulus_ct len hl))
    (fun _ _ h => generatorFresh_ready h)) (generatorPower_ct M Sq)

end VG.Proof.Dsa.X86_64.Generation

module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.BodyWide
import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateBodyTiming

/-! The public helper satisfies the merged preparation contract, including timing. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 numAt_eq4)

theorem publicNarrowRun {n e m size : Nat} {base : Addr} {s t : State} {tr : List Leak}
    (h : Supported n e) (E : Pow.Entry s base size) (hz : (layout n e).size≤size)
    (hv : wordsVal s.mem base (slot n 0) n=m) (hm : 1<m) (odd : m%2=1)
    (run : Exec isa (body true n e) s tr t) :
    ∃ u, Exec isa (body true n e) (narrowState n e base s) tr u := by
  obtain ⟨En,R,W⟩ := narrowResources E hz
  obtain ⟨trace,u,Run,_⟩ := body_ok h true En hv hm odd (fun eq => Bool.noConfusion eq)
  obtain ⟨rfl,_⟩ := Exec.det run (regionModel.inline Run R W).1
  exact ⟨u,Run⟩

end VG.Proof.Dsa.X86.Comb

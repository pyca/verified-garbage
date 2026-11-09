module

public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.RedTiming
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.ModPowContract

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 scratch_fits)

/-- A run of the body from a state ready for it, its return address apart
from the working space. -/
theorem run {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) {s : State} (B : BodyIn n size s)
    (ret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ws s, size⟩) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧
      wordsVal t.mem (ws s) (slot n 6) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) %
          wordsVal s.mem (ws s) (slot n 0) n ∧
      Outs (ws s) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem := by
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok B.input B.size hn hn48 rfl B.large B.odd
  have F : Frame [⟨ws s, size⟩] s.mem t.mem := by
    intro x hx
    have H := hx _ (List.mem_cons_self ..)
    refine O x (fun r hr => ?_)
    have Bd := scratch_fits B.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, V, O⟩
  exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ret) (by decide)

end VG.Proof.Dsa.X86.Red

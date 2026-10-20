module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Residue
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter candidates on x86-64: timing of the sieve and congruences -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate

/-- The workspace layout and generator are public; its candidate words need not be. -/
structure CheckPub where
  B : Addr
  w : Nat
  wr : List Region
  generator : BitVec 64

def CheckHeader (q : CheckPub) (s : State) : Prop := KW q.B q.wr ∧ HP q.B q.wr (gvs q.B q.w) s

theorem sieve_ct : RelCT isa (Two CheckHeader) sieve fun _ _ => True :=
  kt_ct CheckPub.B CheckPub.wr gS (fun q => gvs q.B q.w) [] (by decide)
    (fun q => gvs_fst q.B q.w) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem generator2_ct : RelCT isa (Two CheckHeader) generator2 fun _ _ => True :=
  kt_ct CheckPub.B CheckPub.wr gS (fun q => gvs q.B q.w) [] (by decide)
    (fun q => gvs_fst q.B q.w) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem generator5_ct : RelCT isa (Two CheckHeader) generator5 fun _ _ => True :=
  kt_ct CheckPub.B CheckPub.wr gS (fun q => gvs q.B q.w) [] (by decide)
    (fun q => gvs_fst q.B q.w) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem generatorCheck_ct : RelCT isa (Two fun q s => CheckHeader q s ∧ s.gpr .rdx = q.generator)
    generatorCheck fun _ _ => True :=
  kt_ct CheckPub.B CheckPub.wr gS (fun q => gvs q.B q.w) [.rdx] (by decide)
    (fun q => gvs_fst q.B q.w) (fun _ _ h => h.1)
    (fun q _ _ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h₁.2.trans h₂.2.symm)
    (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

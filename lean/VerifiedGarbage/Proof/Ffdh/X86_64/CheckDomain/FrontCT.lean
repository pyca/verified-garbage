module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: constant-time front end -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

private theorem rangeXm_ct : RelCT isa (Two GoodW1) (seqs (rangeTest aXm)) fun _ _ => True := by
  unfold rangeTest
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True)
      ((range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide)
        (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => ⟨(), trivial, trivial⟩)) ?_)
  exact two_taint [] (pins_nil _) (by taint_decide)

theorem front_ct :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sG sK ++ rangeTest aXm))) (Two GeneratorChecked) := by
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
    (RelCT.seq (R := Two Inner)
      (two_post (two_map CdP.d ce_setup setup_ct) ce_inner) ?_)
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [rangeTest])
    (RelCT.seq (R := Two Generator)
      (two_post (two_map CdP.gl inner_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) inner_generator) ?_)
  exact two_post (two_map CdP.ws (fun p s h => inner_good p s h.1) rangeXm_ct) generator_checked

end VG.Proof.Ffdh.X86_64.CheckDomain

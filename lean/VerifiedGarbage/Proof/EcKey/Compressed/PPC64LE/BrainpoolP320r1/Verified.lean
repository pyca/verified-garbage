module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
public import VerifiedGarbage.Spec.BrainpoolP320r1

/-!
# SEC 1 point conversion over brainpoolP320r1 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with the candidate `rhs^((p+1)/4)`, as `p ≡ 3 mod 4`), for brainpoolP320r1's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.BrainpoolP320r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

/-- The contracts with the table of constants (`Cfg.constsK`), as the proofs state them. -/
abbrev compressPC : Contract isa := (compressContract Spec.BrainpoolP320r1.curve).withTables brainpoolp320r1.constsK

abbrev decompressPC : Contract isa :=
  (decompressContract Spec.BrainpoolP320r1.curve Impl.EcKey.Compressed.rootThreeModFour).withTables brainpoolp320r1.constsK

theorem compress_ct : ConstantTime isa compressPC.pre compressPC.pub Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP320r1 :=
  VG.Taint.constantTime (A := taintSym [brainpoolp320r1.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.BrainpoolP320r1.curve.len = 40 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 40)

theorem constsK_eq : brainpoolp320r1.constsK = [(brainpoolp320r1.constSym, brainpoolp320r1.constTbl)] := rfl

/-- A state satisfying the compression's precondition with the table. -/
def compressSatC : State where
  gpr := (satState 40).gpr
  lr := (satState 40).lr
  sp := (satState 40).sp
  mem := tblSatMem brainpoolp320r1
  rd := (satState 40).rd ++ [⟨0x100000, 8 * (17 * 5)⟩]
  wr := (satState 40).wr
  syms := fun _ => 0x100000

theorem compressSatC_pre :
    (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract (abi.withConsts brainpoolp320r1.constsK) 0).pre compressSatC := by
  have hlen : Spec.BrainpoolP320r1.curve.len = 40 := rfl
  have hl := constTbl_length brainpoolp320r1
  have held := tblSatMem_held brainpoolp320r1 (by decide)
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp320r1.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : compressSatC = s
  sig_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 40 + 1⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract (abi.withConsts brainpoolp320r1.constsK) 0) :=
  Verified.of_correct (compress_correctT brainpoolp320r1 brainpoolp320r1_ok (List.mem_singleton_self _)) compress_ct
    (withTables_implies (compress_implies _ compress_sat) ⟨compressSatC, compressSatC_pre⟩)

theorem decompress_ct : ConstantTime isa decompressPC.pre decompressPC.pub
    Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP320r1 :=
  VG.Taint.constantTime (A := taintSym [brainpoolp320r1.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.BrainpoolP320r1.curve.len = 40 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 40)

/-- A state satisfying the decompression's precondition with the table. -/
def decompressSatC : State where
  gpr := (decompressSatState 40).gpr
  lr := (decompressSatState 40).lr
  sp := (decompressSatState 40).sp
  mem := tblSatMem brainpoolp320r1
  rd := (decompressSatState 40).rd ++ [⟨0x100000, 8 * (17 * 5)⟩]
  wr := (decompressSatState 40).wr
  syms := fun _ => 0x100000

theorem decompressSatC_pre :
    (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract (abi.withConsts brainpoolp320r1.constsK) 0).pre decompressSatC := by
  have hlen : Spec.BrainpoolP320r1.curve.len = 40 := rfl
  have hl := constTbl_length brainpoolp320r1
  have held := tblSatMem_held brainpoolp320r1 (by decide)
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, brainpoolp320r1.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : decompressSatC = s
  sig_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 2 * 40 + 1⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract (abi.withConsts brainpoolp320r1.constsK) 0) :=
  Verified.of_correct (decompress_correctT brainpoolp320r1 brainpoolp320r1_ok _ (candidateThree_correct brainpoolp320r1_ok (by decide +kernel))
      (List.mem_singleton_self _))
    decompress_ct (withTables_implies (decompress_implies _ _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) decompress_sat)
      ⟨decompressSatC, decompressSatC_pre⟩)

end VG.Proof.EcKey.Compressed.PPC64LE.BrainpoolP320r1

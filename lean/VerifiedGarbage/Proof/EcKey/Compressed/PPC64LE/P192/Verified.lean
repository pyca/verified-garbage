module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
meta import VerifiedGarbage.Spec.EcKey.P192
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
public import VerifiedGarbage.Spec.P192

/-!
# SEC 1 point conversion over P-192 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with the candidate `rhs^((p+1)/4)`, as `p ≡ 3 mod 4`), for P-192's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.P192

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

/-- The contracts with the table of constants (`Cfg.constsK`), as the proofs state them. -/
abbrev compressPC : Contract isa := (compressContract Spec.P192.curve).withTables p192.constsK

abbrev decompressPC : Contract isa :=
  (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).withTables p192.constsK

theorem compress_ct : ConstantTime isa compressPC.pre compressPC.pub Impl.EcKey.Compressed.PPC64LE.compressP192 :=
  VG.Taint.constantTime (A := taintSym [p192.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 24)

theorem constsK_eq : p192.constsK = [(p192.constSym, p192.constTbl)] := rfl

/-- A state satisfying the compression's precondition with the table. -/
def compressSatC : State where
  gpr := (satState 24).gpr
  lr := (satState 24).lr
  sp := (satState 24).sp
  mem := tblSatMem p192
  rd := (satState 24).rd ++ [⟨0x100000, 8 * (17 * 3)⟩]
  wr := (satState 24).wr
  syms := fun _ => 0x100000

theorem compressSatC_pre :
    (Spec.EcKey.P192.inst.compressPublicKeyContract (abi.withConsts p192.constsK) 0).pre compressSatC := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  have hl := constTbl_length p192
  have held := tblSatMem_held p192 (by decide)
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, p192.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : compressSatC = s
  sig_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 24 + 1⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressP192
      (Spec.EcKey.P192.inst.compressPublicKeyContract (abi.withConsts p192.constsK) 0) :=
  Verified.of_correct (compress_correctT p192 p192_ok (List.mem_singleton_self _)) compress_ct
    (withTables_implies (compress_implies _ compress_sat) ⟨compressSatC, compressSatC_pre⟩)

theorem decompress_ct : ConstantTime isa decompressPC.pre decompressPC.pub
    Impl.EcKey.Compressed.PPC64LE.decompressP192 :=
  VG.Taint.constantTime (A := taintSym [p192.constSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨hsp, h3, h4, h5⟩, sy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact sy _ (List.mem_singleton_self _)⟩)
    (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 24)

/-- A state satisfying the decompression's precondition with the table. -/
def decompressSatC : State where
  gpr := (decompressSatState 24).gpr
  lr := (decompressSatState 24).lr
  sp := (decompressSatState 24).sp
  mem := tblSatMem p192
  rd := (decompressSatState 24).rd ++ [⟨0x100000, 8 * (17 * 3)⟩]
  wr := (decompressSatState 24).wr
  syms := fun _ => 0x100000

theorem decompressSatC_pre :
    (Spec.EcKey.P192.inst.decompressPublicKeyContract (abi.withConsts p192.constsK) 0).pre decompressSatC := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  have hl := constTbl_length p192
  have held := tblSatMem_held p192 (by decide)
  rw [constsK_eq]
  obtain ⟨W, eW⟩ : ∃ W, p192.constTbl = W := ⟨_, rfl⟩
  rw [eW] at hl held ⊢
  generalize e : decompressSatC = s
  sig_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, ?_⟩
  · change r ∈ [⟨0x1000, 2 * 24 + 1⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressP192
      (Spec.EcKey.P192.inst.decompressPublicKeyContract (abi.withConsts p192.constsK) 0) :=
  Verified.of_correct (decompress_correctT p192 p192_ok _ (candidateThree_correct p192_ok (by decide +kernel))
      (List.mem_singleton_self _))
    decompress_ct (withTables_implies (decompress_implies _ _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) decompress_sat)
      ⟨decompressSatC, decompressSatC_pre⟩)

end VG.Proof.EcKey.Compressed.PPC64LE.P192

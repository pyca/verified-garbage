module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Spec.Dsa.Generate

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInnerCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
import VerifiedGarbage.TCB.X86_64.Target
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
/-! # Complete verification of parameter generation with existing hash and primality backends -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ConstantTime.lean`, which only this module imported.
section

/-! # The complete parameter-generation ABI satisfies its declared public leak -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

private theorem generation_post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem generation_constantTime (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 536).pre
      (Spec.Dsa.generateParametersContract abi 536).pub
      (code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) := by
  intro s t tsa tsb u v hs ht hpub ea eb
  have hsa := generationABI_of hs
  have hta := generationABI_of ht
  have hp := generation_public_related hpub
  unfold code at ea eb
  cases ea with
  | frame pa ba _ =>
    cases eb with
    | frame pb bb _ =>
      rw [generation_alloc (by decide) (by omega_using [hsa.stackLower] : 48 ≤ (s.gpr .rsp).toNat), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (by omega_using [hta.stackLower] : 48 ≤ (t.gpr .rsp).toNat), Option.some.injEq] at pb
      subst pa; subst pb
      cases ba with | seq sa restA => cases restA with | seq ia ra =>
      cases bb with | seq sb restB => cases restB with | seq ib rb =>
      have saveTrace := (entrySave_ct _ _ _ _ _ _ (by
        change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
        rw [hp.sp]) sa sb).1
      obtain ⟨ga, rda, wra, _, fa⟩ := generation_post_of_exec (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) sa
      obtain ⟨gb, rdb, wrb, _, fb⟩ := generation_post_of_exec (entrySave_ok (s := allocState 48 t) (List.mem_cons_self ..)) sb
      have inner := entryInner_ct (checkName := checkName) H M Sq T hsa hta hp ga rda wra fa gb rdb wrb fb ia ib
      have restoreTrace := (entryRestore_ct _ _ _ _ _ _ inner.2 ra rb).1
      simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
      rw [saveTrace, inner.1, restoreTrace]

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Satisfiable.lean`, which only this module imported.
section

/-! # The native parameter-generation contract admits concrete inputs -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

def generationSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 276 | .rdx => 128 | .rcx => 20
    | .r8 => 0x2000 | .rsp => 0x1000000000000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000000000009 then 0x30 else if a = 0x1000000000019 then 0x40
    else if a = 0x100000000002a then 1 else if a = 0x1000000000031 then 0x24 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x1000000000008, 48⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x10000, 73728⟩]

private theorem sat_arg_0 : stackArg generationSatState 0 = 0x3000 := by decide +kernel
private theorem sat_arg_1 : stackArg generationSatState 1 = 0 := by decide +kernel
private theorem sat_arg_2 : stackArg generationSatState 2 = 0x4000 := by decide +kernel
private theorem sat_arg_3 : stackArg generationSatState 3 = 0 := by decide +kernel
private theorem sat_arg_4 : stackArg generationSatState 4 = 0x10000 := by decide +kernel
private theorem sat_arg_5 : stackArg generationSatState 5 = 9216 := by decide +kernel

theorem generation_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 536).pre s := by
  refine ⟨generationSatState, ?_⟩
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4, sat_arg_5]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, generationSatState] at h₁ h₂; bv_omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem backend_constantTime (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    ConstantTime isa (Spec.Dsa.generateParametersContract abi 536).pre
      (Spec.Dsa.generateParametersContract abi 536).pub
      (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) :=
  generation_constantTime (checkName := checkName) (generationHashes v1 v256 h1 h256) VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v)

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target
      (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run)
      (Spec.Dsa.generateParametersContract abi 536) :=
  ⟨backend_correct (checkName := checkName) v1 v256 v h1 h256, backend_constantTime (checkName := checkName) v1 v256 v h1 h256, generation_satisfiable⟩

end VG.Proof.Dsa.X86_64.Generation

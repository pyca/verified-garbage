module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Correct
import VerifiedGarbage.Proof.Dsa.X86.Comb.PrivateTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86.Comb.ABI
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! The callable private comb helper leaks no exponent-dependent trace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem save_relCT :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold VG.Impl.Dsa.X86.Pow.save
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
    (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))

theorem private_body_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (fun s t => s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 ∧
      readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) ∧
      readSrc t (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg t 0))
      (body false n e) (fun _ _ => True) := by
  unfold body
  refine RelCT.seq save_relCT ?_
  have eq : privateInputs=workspaceTaint false := by decide
  rw [←eq]
  refine RelCT.seq (private_core_relCT h) ?_
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) rfl rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem publicArgs {n e : Nat} {s t : State} (prepare : Bool)
    (H : (contract prepare n e).pub s t) : s.gpr .esp=t.gpr .esp ∧ arg s 0=arg t 0 := by
  cases prepare
  all_goals
    sig_pub [contract,Proof.Dsa.FixedBaseComb.prepareContract,Proof.Dsa.FixedBaseComb.powerContract,
      Proof.Dsa.ModPow.sig,abi,argSlots,argVal,argBytes] at H
    sig_split H
    constructor <;> with_reducible assumption

theorem private_constantTime {n e : Nat} (supported : Supported n e) :
    ConstantTime isa (contract false n e).pre (contract false n e).pub (body false n e) := by
  intro s t tr ur sf tf hs ht hp E F
  have A := (abi_of supported false hs).1
  have B := (abi_of supported false ht).1
  obtain ⟨SP,Arg⟩ := publicArgs false hp
  exact (private_body_relCT supported _ _ _ _ _ _ ⟨SP,Arg,A.readArg,B.readArg⟩ E F).1

end VG.Proof.Dsa.X86.Comb

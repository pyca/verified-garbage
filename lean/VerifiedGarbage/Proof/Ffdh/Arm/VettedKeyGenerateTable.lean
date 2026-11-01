module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract

/-! The constant table is outside every writable key-attempt buffer and
its complete stack reservation, including callable arithmetic. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups
open VettedGroups

theorem vettedKeyGenerate_stackFit {s : State}
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    176 ≤ s.sp.toNat := by
  have old := (vettedKeyGenerate_pre pre).1
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi,
    argRegs, reduceClassify, Loc.val, State.addr] at old
  exact old.1

theorem vettedKeyGenerate_tableFacts (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s)
    {p : Inputs} {rb : List Byte} (input : KeyGenerateFnInput p rb s) :
    (s.syms tableSym).toNat + tableBytes.length ≤ 2 ^ 32 ∧
    InRegions ((entered s).rd ++ (entered s).wr) (State.addr ((entered s).syms tableSym)) tableBytes.length ∧
    Spec.Rsa.bytesAt (entered s).mem (State.addr ((entered s).syms tableSym)) tableBytes.length = tableBytes ∧
    ∀ r ∈ keyCallWrites p (entered s),
      (⟨State.addr ((entered s).syms tableSym), tableBytes.length⟩ : Region).Disjoint r := by
  have hc := (vettedKeyGenerate_pre pre).2
  have fit := hc.fit (name := tableSym) (ws := tableWords) List.mem_cons_self
  rw [tableWords_length] at fit
  have geometry := consts_singleton_regions (name := tableSym) (words := tableWords) hc
  rw [tableWords_length] at geometry
  have span : tableBytes.length = 8 * 2218 := tableBytes_length
  have stackFit := vettedKeyGenerate_stackFit pre
  have reserved : (⟨State.addr (s.syms tableSym), tableBytes.length⟩ : Region).Disjoint
      (FrameStack.belowA s.sp 176) := by
    rw [span]
    apply geometry.2.2
    rw [FrameStack.belowA, FrameStack.addr_sub' stackFit]
    simp only [abi, stackBelow]
    exact List.mem_cons_self
  have inner : (FrameStack.belowA s.sp 128).Sub (FrameStack.belowA s.sp 176) :=
    FrameStack.belowA_sub (by decide) stackFit
  have localSub : (⟨State.addr (entered s).sp, 72⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => inner a ((locals_sub_reserved s input.stackFits) a h)
  have savedSub : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => inner a ((saved_sub_reserved s input.stackFits) a h)
  have writable : ∀ r ∈ (entered s).wr,
      (⟨State.addr (s.syms tableSym), tableBytes.length⟩ : Region).Disjoint r := by
    intro r member
    change r ∈ (⟨State.addr (entered s).sp, 72⟩ : Region) ::
      ⟨State.addr (pcPushed s).sp, 56⟩ :: s.wr at member
    rcases List.mem_cons.mp member with rfl | member
    · exact reserved.sub_right localSub
    rcases List.mem_cons.mp member with rfl | member
    · exact reserved.sub_right savedSub
    · rw [span]; exact geometry.2.1 r member
  refine ⟨by rw [span]; exact fit, entered_read (consts_table_read hc), ?_, ?_⟩
  · rw [VG.Proof.Bignum.Arm.rsa_bytes_frame (entered_frame s input.stackFits)
      (by rw [span]; omega) (by
        intro r hr
        have eq := List.mem_singleton.mp hr
        subst r
        exact reserved.sub_right savedSub)]
    exact consts_table_bytes hc
  · intro r member
    simp only [keyCallWrites, keyWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with (rfl | rfl | rfl | rfl) | rfl
    · exact writable _ input.args.workspace.writable
    · exact writable _ input.args.locals.space.writable
    · obtain ⟨region, hmem, contains⟩ := input.outputs.privateBuffer.writable
      exact (writable region hmem).sub_right (by
        intro addr inside
        exact contains.byte (by
          change (addr - State.addr p.privateValue).toNat + 1 ≤ p.k at inside
          omega))
    · obtain ⟨region, hmem, contains⟩ := input.outputs.publicBuffer.writable
      exact (writable region hmem).sub_right (by
        intro addr inside
        exact contains.byte (by
          change (addr - State.addr p.publicValue).toNat + 1 ≤ p.k at inside
          omega))
    · rw [entered_sp]
      exact reserved.sub_right (FrameStack.belowA_inner (a := 48) (k := 128) (by decide) stackFit)

theorem vettedKeyGenerate_environment (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s)
    {p : Inputs} {rb : List Byte} (input : KeyGenerateFnInput p rb s) :
    VettedGroups.environment.holds p (entered s) := by
  obtain ⟨fit, read, bytes, safe⟩ := vettedKeyGenerate_tableFacts s pre input
  apply VettedGroups.tableOfBytes (entered s) ((entered s).syms tableSym) groups fit read bytes
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact safe

theorem vettedKeyGenerate_data (s : State)
    (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ (p : Inputs) (rb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.privateValue ∧
      s.gpr .r2 = p.publicValue ∧ stackArg s 0 = p.domain ∧ (stackArg s 2).toNat = p.k ∧
      (stackArg s 6).toNat = p.len ∧ stackArg s 3 = p.entropy ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (stackArg s 1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.entropy) p.k = rb ∧ KeyGenerateFnInput p rb s ∧
      VettedGroups.environment.holds p (entered s) := by
  obtain ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, input⟩ := vettedKeyGenerate_data_base s pre
  exact ⟨p, rb, base, privateValue, publicValue, domain, count, capacity, entropy,
    domainBytes, entropyBytes, input, vettedKeyGenerate_environment s pre input⟩

end VG.Proof.Ffdh.Arm

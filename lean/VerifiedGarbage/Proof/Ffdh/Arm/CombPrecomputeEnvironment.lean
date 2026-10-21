module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeInput
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! The shared public recognition table survives the precomputation frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Impl.Ffdh.Arm.VettedGroups
open VettedGroups

theorem combPrecompute_environment (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s)
    {p : Inputs} (base : stackArg s 1 = p.base) (output : s.gpr .r0 = p.output)
    (capacity : (stackArg s 2).toNat = p.len) (count : (stackArg s 0).toNat = p.k)
    (privateAlias : p.privateValue = p.output) (publicAlias : p.publicValue = p.output) :
    VettedGroups.environment.holds p (entered s) := by
  obtain ⟨plain,hc⟩ := pre_consts.mp pre
  sig_pre [Spec.Ffdh.generationPrecomputeContract,Spec.Ffdh.generationPrecomputeSig,
    abi,argRegs,reduceClassify,Loc.val,State.addr] at plain
  obtain ⟨stackFit,_,_,wr,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ctxLen,_,_⟩ := plain
  change s.wr = [⟨State.addr (s.gpr .r0),(s.gpr .r1).toNat*8⟩,
    ⟨State.addr (stackArg s 1),(stackArg s 2).toNat*8⟩] at wr
  change (s.gpr .r1).toNat = Spec.Ffdh.generationPrecomputedWords (stackArg s 0).toNat at ctxLen
  have small : p.k ≤ (s.gpr .r1).toNat*8 := by
    rw [ctxLen,count]
    have hw := p.width.2.2.2.1
    change p.k ≤ 8*p.w at hw
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords,Spec.Rsa.FixedBaseComb.entries]
    change p.k ≤ (3+(2*p.w+32*p.w))*8
    omega
  have geometry := consts_singleton_regions (name := tableSym) (words := tableWords) hc
  have span : 8*tableWords.length = tableBytes.length := by rw [tableWords_length,tableBytes_length]
  have fit := hc.fit (name := tableSym) (ws := tableWords) List.mem_cons_self
  rw [span] at fit
  have reserved : (⟨State.addr (s.syms tableSym),tableBytes.length⟩ : Region).Disjoint (FrameStack.belowA s.sp 176) := by
    rw [←span]
    apply geometry.2.2
    rw [FrameStack.belowA,FrameStack.addr_sub' stackFit]
    simp only [abi,stackBelow]
    exact List.mem_cons_self
  have localSub : (⟨State.addr (entered s).sp,72⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => FrameStack.belowA_sub (by decide) stackFit a (locals_sub_reserved s (by omega) a h)
  have savedSub : (⟨State.addr (pcPushed s).sp,56⟩ : Region).Sub (FrameStack.belowA s.sp 176) :=
    fun a h => FrameStack.belowA_sub (by decide) stackFit a (saved_sub_reserved s (by omega) a h)
  have writable (r : Region) (member : r ∈ (entered s).wr) :
      (⟨State.addr (s.syms tableSym),tableBytes.length⟩ : Region).Disjoint r := by
    change r ∈ (⟨State.addr (entered s).sp,72⟩ : Region)::⟨State.addr (pcPushed s).sp,56⟩::s.wr at member
    rcases List.mem_cons.mp member with rfl | member
    · exact reserved.sub_right localSub
    rcases List.mem_cons.mp member with rfl | member
    · exact reserved.sub_right savedSub
    · rw [←span]; exact geometry.2.1 r member
  apply VettedGroups.tableOfBytes (entered s) ((entered s).syms tableSym) groups fit (entered_read (consts_table_read hc))
  · rw [VG.Proof.Rsa.rsa_bytes_frame (entered_frame s (by omega)) (by change tableBytes.length < 2^64; rw [tableBytes_length]; decide) (by
      intro r hr
      have eq := List.mem_singleton.mp hr
      subst r
      exact reserved.sub_right savedSub)]
    exact consts_table_bytes hc
  · intro g hg
    simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    simp only [keyCallWrites,keyWrites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl
    · apply writable
      change _ ∈ _::_::s.wr
      apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
      rw [wr,base,capacity,Nat.mul_comm p.len 8]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact reserved.sub_right localSub
    · rw [privateAlias,←output]
      apply (writable ⟨State.addr (s.gpr .r0),(s.gpr .r1).toNat*8⟩ (by
        apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; rw [wr]; exact List.mem_cons_self)).sub_right
      simpa only [off,BitVec.add_zero] using (Offset.sub_base (State.addr (s.gpr .r0)) (d:=0) (n:=p.k) (by omega))
    · rw [publicAlias,←output]
      apply (writable ⟨State.addr (s.gpr .r0),(s.gpr .r1).toNat*8⟩ (by
        apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; rw [wr]; exact List.mem_cons_self)).sub_right
      simpa only [off,BitVec.add_zero] using (Offset.sub_base (State.addr (s.gpr .r0)) (d:=0) (n:=p.k) (by omega))
    · rw [entered_sp]
      exact reserved.sub_right (FrameStack.belowA_inner (a:=48) (k:=128) (by decide) stackFit)

end VG.Proof.Ffdh.Arm

module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Fn
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.DomainCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBytes
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! The existing parameter signature supplies the original frame and read-only table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts) 128

private theorem entered_read_widen {s : State} {a : Addr} {n : Nat}
    (h : InRegions ((entered (stripConsts tableConsts s)).rd ++
      (entered (stripConsts tableConsts s)).wr) a n) :
    InRegions ((entered s).rd ++ (entered s).wr) a n := by
  obtain ⟨r, member, contains⟩ := h
  refine ⟨r, ?_, contains⟩
  rcases List.mem_append.mp member with read | write
  · exact List.mem_append_left _ (List.mem_of_mem_take read)
  · exact List.mem_append_right _ write

theorem input_widen {s : State} {p : Inputs}
    (h : DomainFnInput p (stripConsts tableConsts s)) : DomainFnInput p s := by
  refine ⟨h.stackFits, ?_, h.domain, h.domainLength, h.count, h.scratch, h.saved⟩
  exact ⟨h.args.workspace.congr rfl,
    ⟨h.args.locals.space.congr rfl, h.args.locals.separate⟩,
    ⟨h.args.domain.fits, entered_read_widen h.args.domain.readable,
      h.args.domain.separate, h.args.domain.bytes⟩,
    h.args.domainStack, h.args.saved⟩

theorem table_input {s : State} (hc : ConstsOk tableConsts 128 s)
    {p : Inputs} (input : DomainFnInput p s) :
    VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s) ∧
    VettedGroups.TableSafe ((entered s).syms tableSym) groups
      [⟨State.addr (entered s).sp, 72⟩] := by
  have geometry := VettedGroups.consts_singleton_regions (name := tableSym) (words := tableWords) hc
  have fit := hc.fit (name := tableSym) (ws := tableWords) List.mem_cons_self
  rw [VettedGroups.tableWords_length] at geometry fit
  have span : tableBytes.length = 8 * 2218 := VettedGroups.tableBytes_length
  have reserved : (⟨State.addr (s.syms tableSym), tableBytes.length⟩ : Region).Disjoint
      (FrameStack.belowA s.sp 128) := by
    rw [span]
    apply geometry.2.2
    rw [FrameStack.belowA, FrameStack.addr_sub' input.stackFits]
    simp only [abi, stackBelow]
    exact List.mem_cons_self
  have bytes : Spec.Rsa.bytesAt (entered s).mem
      (State.addr ((entered s).syms tableSym)) tableBytes.length = tableBytes := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame (entered_frame s input.stackFits)
      (by rw [span]; omega) (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact reserved.sub_right (saved_sub_reserved s input.stackFits))]
    exact VettedGroups.consts_table_bytes hc
  apply VettedGroups.tableOfBytes (entered s) ((entered s).syms tableSym) groups
    (by change ((entered s).syms tableSym).toNat + tableBytes.length ≤ 2 ^ 32; rw [span]; exact fit) (entered_read (VettedGroups.consts_table_read hc)) bytes
  · intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact reserved.sub_right (locals_sub_reserved s input.stackFits)

theorem data (s : State) (pre : contract.pre s) :
    ∃ p : Inputs, s.gpr .r3 = p.base ∧ s.gpr .r0 = p.domain ∧
      (s.gpr .r2).toNat = p.k ∧ (stackArg s 0).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧ Input p s := by
  have base : (Spec.Ffdh.checkDomainContract abi 128).pre (stripConsts tableConsts s) ∧
      ConstsOk tableConsts 128 s := pre_consts.mp pre
  obtain ⟨p, scratch, domain, count, capacity, bytes, input⟩ := domain_data
    (stripConsts tableConsts s) base.1
  have wide := input_widen input
  have table := table_input base.2 wide
  exact ⟨p, scratch, domain, count, capacity, bytes, wide, table.1, table.2⟩

end VG.Proof.Ffdh.Arm.VettedValidation

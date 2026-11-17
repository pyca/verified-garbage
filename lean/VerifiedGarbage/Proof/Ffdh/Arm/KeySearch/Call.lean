module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPre
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Lost

/-! ### `Ffdh.Arm.KeySearch.CallConsts`, which this module and modules that import it used -/

section

/-! The nested attempt receives the policy's preserved public constant tables. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont

 theorem strip_call {p : KeyPublic sampling} {used : Nat} {u : State} :
    stripConsts (KeyConstants.consts sampling) (callState p used u) = plainCallState p used u := by
  cases sampling <;> rfl

 theorem call_consts {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s)
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p) (syms : u.syms = s.syms) :
    ConstsOk (KeyConstants.consts sampling) 176 (callState p used u) := by
  have pointer : KeyConstants.tablePtr sampling (callState p used u) = p.tablePtr :=
    (KeyConstants.tablePtr_of_syms (sampling := sampling) syms).trans h.tablePtr
  have regions : constRegs (KeyConstants.consts sampling) (callState p used u) =
      KeyConstants.regions sampling p.tablePtr := by
    rw [KeyConstants.regions_eq, pointer]
  have frame : Frame [rArguments p] s.mem u.mem := by rw [mem]; exact callMem_frame _ _ _ _
  have held := KeyConstants.held_after_frame h.held frame (by
    intro table member r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.input.constants_stack table member).sub_right (arguments_sub h.input.bounds.stackFits))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [regions]
    cases sampling <;> rfl
  · intro c member i hi
    have word := held c member i hi
    cases sampling with
    | full | cached => exact False.elim (List.not_mem_nil member)
    | vetted =>
      simp only [KeyConstants.consts, VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, List.mem_singleton] at member
      subst c
      change u.mem.readW (State.addr (u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym) + BitVec.ofNat 64 (8 * i)) 64 = _
      change u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym = p.tablePtr at pointer
      rw [pointer]
      exact word
  · intro table member
    rw [regions] at member
    have initial : ConstsOk (KeyConstants.consts sampling) (stackUse sampling) original := h.input.2.2
    have originalMember : table ∈ constRegs (KeyConstants.consts sampling) original := by
      rw [h.input.constant_regions]; exact member
    have facts := initial.2.2.1 table originalMember
    refine ⟨facts.1, ?_, ?_⟩
    · intro r hr
      have changes : r ∈ callChanges p := by
        change r ∈ callWr p at hr
        simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [callChanges]
      exact h.input.call_read (h.input.constants_read member) r changes
    · intro r hr
      change r ∈ stackBelow (State.addr u.sp) 176 at hr
      simp only [stackBelow, List.mem_singleton] at hr
      subst r
      rw [sp]
      have fit : 176 ≤ (callSp p).toNat := by
        have enough := h.input.bounds.stackFits
        change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at enough
        rw [callSp, FrameStack.sub_toNat' (by omega_using [enough] : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
        omega_using [enough]
      rw [← FrameStack.addr_sub' fit]
      exact (h.input.constants_stack table member).sub_right (callStack_sub h.input.bounds.stackFits)
  · intro table member
    rw [regions] at member
    have initial : ConstsOk (KeyConstants.consts sampling) (stackUse sampling) original := h.input.2.2
    have originalMember : table ∈ constRegs (KeyConstants.consts sampling) original := by
      rw [h.input.constant_regions]; exact member
    exact initial.2.2.2 table originalMember

 theorem call_pre {p : KeyPublic sampling} {used keys scalars : Nat} {original s u : State}
    (live : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p)) (syms : u.syms = s.syms) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pre (callState p used u) := by
  apply selected_attempt_pre.mpr
  rw [strip_call]
  exact ⟨call_pre_plain live room args sp mem, call_consts live mem sp syms⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CallPost`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.CallRegions`, which this module and modules that import it used -/

section

/-! The selected attempt can narrow permissions to its buffers and arguments;
its stack writes remain below the controller's saved registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

namespace KeyLive
variable {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}

theorem covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (wr : u.wr = (allocated sampling.argumentBytes s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [wr]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.write_regions]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp

theorem covers_reads (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    {u : State} (rd : u.rd = (allocated sampling.argumentBytes s).rd) (wr : u.wr = (allocated sampling.argumentBytes s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (h.covers_writes wr).right
  apply Covers.of_sub
  intro r hr
  simp only [callRd, callRdPlain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (((rfl | rfl) | context) | args) | constant
  · refine ⟨rDomain p, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change rDomain p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨rRandom p, ?_, used, h.input.tape_addr room, room⟩
    rw [rd]
    apply List.mem_append_left
    change rRandom p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨r, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change r ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (Or.inl (Or.inr context))
  · obtain rfl := args
    refine ⟨rArguments p, ?_, 0, by rw [BitVec.add_zero], by change 0 + (sampling.argumentBytes - 4) ≤ sampling.argumentBytes; omega_using []⟩
    rw [wr]
    apply List.mem_append_right
    change rArguments p ∈ ⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩ :: s.wr
    rw [h.call_sp]
    exact List.mem_cons_self
  · refine ⟨r, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change r ∈ s.rd
    rw [h.rd]
    exact h.input.constants_read constant

theorem argument_frame (_h : KeyLive p original used keys scalars s) {u : State}
    (mem : u.mem = callMem p used s.mem (callSp p)) : Frame (callChanges p) s.mem u.mem := by
  rw [mem]
  exact (callMem_frame _ _ _ _).mono (by simp [callChanges, rArguments])

theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {depth : Nat}
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p)
    (frame : Frame (callWr p ++ [FrameStack.belowA u.sp depth]) u.mem t.mem) (limit : depth ≤ 176) :
    Frame (callChanges p) s.mem t.mem := by
  apply (h.argument_frame mem).trans
  apply frame.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, by simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl <;> simp [callChanges], fun _ hi => hi⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨rCallStack p, by simp [callChanges], ?_⟩
    rw [sp]
    apply FrameStack.belowA_sub limit
    have fit := h.input.bounds.stackFits
    change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
    change 176 ≤ (p.sp - BitVec.ofNat 32 (24 + sampling.argumentBytes)).toNat
    rw [FrameStack.sub_toNat' (by omega_using [fit] : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
    omega_using [fit]


end KeyLive
end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The shared key-attempt result is exactly the controller's current
attempt status and key pair, independent of its temporary call frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyLive.call_inputs {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (mem : u.mem = callMem p used s.mem (callSp p)) :
    Spec.Rsa.bytesAt u.mem (State.addr p.dp) p.dlen = p.dom ∧
      Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) p.len =
        ((keyRand p original).drop used).take p.len := by
  have frame := h.argument_frame mem
  refine ⟨(h.input.call_domain_frame frame).trans h.domain, ?_⟩
  have slice : ((Spec.Rsa.bytesAt u.mem (State.addr p.rp) p.randLen).drop used).take p.len =
      Spec.Rsa.bytesAt u.mem (off (State.addr p.rp) used) p.len :=
    VG.Proof.MlKem.bytesAt_slice u.mem (State.addr p.rp) room
  rw [h.input.tape_addr room, ← slice, h.input.call_random_frame frame, h.random]
  rfl

theorem call_post {p : KeyPublic sampling} {original s u t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p))
    (post : (GenerationPolicy.attemptContract sampling abi 176).post (callState p used u)
      (t.withRegions (callRd p used) (callWr p))) : AttemptPost p original used t := by
  have facts := h.input.callFacts room
  have a0 := call_stackArg (j := 0) facts sp mem (by cases sampling <;> decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by cases sampling <;> decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by cases sampling <;> decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by cases sampling <;> decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by cases sampling <;> decide)
  simp only [callValue] at a0 a1 a2 a3 a4
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have bytes := h.call_inputs room mem
  cases sampling <;>
    sig_post [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract,
      Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at post
  all_goals
    rw [BitVec.setWidth_append_eq_right] at post
    simp only [args.x, args.y, a0, a1, a2, a3, a4, nativeLen, domainLen] at post
    simp only [State.addr] at bytes
    rw [bytes.1, bytes.2] at post
    first
    | exact ⟨(post h.input.bounds.domainValid).1, (post h.input.bounds.domainValid).2⟩
    | exact ⟨post.1, post.2⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Calling any verified FFDH backend from the native key-search controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem attemptRun_ok (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : AttemptRunOk backend := by
  intro p original s used keys scalars h room
  have facts := h.input.callFacts room
  have rootFit : stackUse sampling ≤ p.sp.toNat := h.input.bounds.stackFits
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at rootFit
  have outerFit : sampling.argumentBytes ≤ s.sp.toNat := by
    rw [h.sp, FrameStack.sub_toNat' (by omega_using [rootFit] : 24 ≤ p.sp.toNat)]
    omega_using [rootFit]
  have allocatedFit : (allocated sampling.argumentBytes s).sp.toNat + sampling.argumentBytes ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 sampling.argumentBytes).toNat + sampling.argumentBytes ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega_using [rootFit]
  have control : Controller p.control (allocated sampling.argumentBytes s) :=
    ⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)),
      h.pointer⟩
  have stack : Workspace (allocated sampling.argumentBytes s) (allocated sampling.argumentBytes s).sp sampling.argumentBytes :=
    ⟨allocatedFit, List.mem_cons_self⟩
  have separate : (rControl p).Disjoint ⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩ := by
    rw [h.call_sp]
    exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor
  change WP isa (.frame (.alloc sampling.argumentBytes) (.seq (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) (.call backend.keyName backend.generateKey)) (.free sampling.argumentBytes)) s _
  refine WP.allocLost (by cases sampling <;> decide) outerFit ?_
  rw [WP.seq_iff]
  refine WP.mono_syms (arguments_ok (allocated sampling.argumentBytes s) control stack separate h.headers h.cachedSlots) ?_
  rintro u ⟨⟨args, mem⟩, rest⟩ symsU
  have spU : u.sp = callSp p := rest.sp.trans h.call_sp
  have memU : u.mem = callMem p used s.mem (callSp p) := by
    rw [mem, h.call_sp]
    rfl
  apply WP.of_syms
  refine FrameStack.WP.callF backend.generateKey_verified.1 (call_pre h room args spU memU symsU)
    (h.covers_reads room rest.rd rest.wr) (h.covers_writes rest.wr)
    (by rw [spU]; exact Nat.le_trans backend.keyStack facts.stackFits) ?_
  intro t rd wr sp frame kept post symsT m₀ u₀ hfl
  change Frame [⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩] t.mem m₀ at hfl
  rw [h.call_sp] at hfl
  have argSep : ∀ r ∈ [rX p, rY p], r.Disjoint (rArguments p) := by
    intro r hr
    have hw : r ∈ original.wr ++ original.rd := by
      rw [h.input.write_regions]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    exact ((h.input.stack_separate hw).sub_left (arguments_sub h.input.bounds.stackFits)).symm
  have fitLen : p.len ≤ 2 ^ 64 := by have := h.input.bounds.maxLength; omega_using [this]
  have xeq : Spec.Rsa.bytesAt m₀ (State.addr p.xp) p.len = Spec.Rsa.bytesAt t.mem (State.addr p.xp) p.len :=
    bytesAt_frame (r := rX p) hfl (by simpa using argSep _ (by simp)) fitLen
  have yeq : Spec.Rsa.bytesAt m₀ (State.addr p.yp) p.len = Spec.Rsa.bytesAt t.mem (State.addr p.yp) p.len :=
    bytesAt_frame (r := rY p) hfl (by simpa using argSep _ (by simp)) fitLen
  refine ⟨h.restore ?_ ?_ ?_ ?_ (symsT.trans symsU) ((h.attempt_frame memU spU frame backend.keyStack).trans
    (hfl.sub fun r hr => ⟨rArguments p, by simp only [List.mem_singleton] at hr; subst hr; simp [callChanges],
      by simp only [List.mem_singleton] at hr; subst hr; exact fun _ hc => hc⟩)), ?_⟩
  · exact rd.trans rest.rd
  · change t.wr.tail = s.wr
    rw [wr, rest.wr]
    rfl
  · change t.sp + BitVec.ofNat 32 sampling.argumentBytes = s.sp
    rw [sp, rest.sp]
    exact BitVec.sub_add_cancel _ _
  · intro r hr
    change t.gpr r = s.gpr r
    rw [kept r (by revert r hr; decide) (by revert r hr; decide)]
    exact rest.gpr r (by revert r hr; decide)
  · have result := call_post h room args spU memU (selected_attempt_post.mp post)
    have out := result.output
    rw [← xeq, ← yeq] at out
    exact ⟨result.status, out⟩

end VG.Proof.Ffdh.Arm.KeySearch

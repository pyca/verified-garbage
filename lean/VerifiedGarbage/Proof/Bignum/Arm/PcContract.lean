module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.PcInput

import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.PcBody
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
import VerifiedGarbage.Proof.Bignum.Arm.ExportState
import VerifiedGarbage.Proof.Bignum.Arm.PcPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PcFailCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
/-! # Public precomputation satisfies the shared RSA contract under AAPCS -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PcFn.lean`, which only this module imported.
section

/-! # Callable ARMv7 RSA precomputation preserves AAPCS and implements the shared result -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem pcFn_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcFnInput base dst src len k s)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : WP isa (PcFn.codeWith kernel.code) s fun t => abiPreserved s t ∧
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (State.addr src) k) with
      | some words => t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) = words
      | none => t.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) =
          List.replicate (2 * Spec.Rsa.modulusWords k) 0) := by
  unfold PcFn.codeWith
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (pc_entry_ready s h) ?_
  rintro u ⟨ready, frameU, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (pcBody_ok (kernel := kernel) u ready.workspace ready.stack ready.minLength ready.maxLength ready.space
    ready.sourceFits ready.readable ready.sourceSeparate ready.outputFits ready.writable ready.outputSeparate
    ready.ptr ready.source ready.count) ?_
  rintro v ⟨result, frameV, restV⟩
  have bytes := rsa_bytes_frame frameU (by have := h.maxLength; omega : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackInput.symm)
  rw [bytes] at result
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply savedU.frame (lo := 0) (hi := 56) (by decide) frameV
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [restU.sp]
    simp only [BitVec.add_zero, Nat.sub_zero]
    change (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region).Disjoint r
    rcases hr with rfl | rfl
    · simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace
    · simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackOutput
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by decide)
    · exact restored (.r5, 20) (by decide)
    · exact restored (.r6, 24) (by decide)
    · exact restored (.r7, 28) (by decide)
    · exact restored (.r8, 32) (by decide)
    · exact restored (.r9, 36) (by decide)
    · exact restored (.r10, 40) (by decide)
    · exact restored (.r11, 44) (by decide)
    · exact restored (.lr, 52) (by decide)
  · rw [popped_sp, restT.sp, spV]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PcComputed.lean`, which only this module imported.
section

/-! # The arithmetic result is ready for serialization to the caller's buffer -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (wOf Layout)

structure PcComputed (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop where
  buffers : PcBuffers base dst src len k s
  stack : PcStack base dst src len k s
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = Spec.Rsa.modulusWords k
  ptr : s.gpr .r0 = base

theorem pcComputed_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcPrepared base dst src len k s)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : WP isa kernel.code s (PcComputed base dst src len k) := by
  have countFit := (pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space).2.2.2.2
  refine WP.mono (kernel.correct s h.input.workspace h.input.layout h.input.width h.input.positive
    h.input.fits h.input.sourceFits h.input.readable h.input.separate h.input.ptr h.input.source h.input.count
    h.input.stackRead h.input.stackSep h.input.saved h.input.large h.input.odd countFit) ?_
  rintro t ⟨ready, _, _, frame, rest⟩
  exact ⟨h.buffers.congr rest, h.stack.after_workspace frame rest, ready.layout, ready.width, ready.ptr⟩

theorem pcExport_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcComputed base dst src len k s) :
    WP isa (.block [.ldrSp .r4 4]) s (ExportState base dst len (Spec.Rsa.modulusWords k) (16 * Spec.Rsa.modulusWords k)) := by
  refine WP.mono (pcOutput_ok s h.stack) ?_
  rintro t ⟨output, mem, rest⟩
  refine ⟨h.buffers.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr,
    output, by omega, h.buffers.outputFits, ?_, h.buffers.outputSeparate⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.wr]; exact h.buffers.writable

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PcValidCT.lean`, which only this module imported.
section

/-! # Successful public precomputation has no secret-dependent trace -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcValid_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte} (hk : k ≤ 1024)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : RelCT isa (fun s t =>
      (PcValidInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcValidInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (PcFn.validWith kernel.code) (fun _ _ => True) := by
  have countFit : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
    simp only [Spec.Rsa.modulusWords]; omega
  have prepared := (relCT_keep_sp ((pcPrepare_ct (base := base) (dst := dst) (src := src) (len := len) (k := k)).mono
    (P' := fun (s t : State) =>
      (PcValidInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcValidInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => True.intro)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨pcPrepare_public_ready s h.1.1 h.1.2, pcPrepare_public_ready t h.2.1.1 h.2.1.2⟩)
  have arithmetic := (relCT_keep_sp ((kernel.ct (nb := nb) countFit).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧
      (PcPrepared base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcPrepared base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb))
    (fun _ _ h => ⟨⟨h.2.1.1.input, h.2.1.2⟩, ⟨h.2.2.1.input, h.2.2.2⟩, h.1⟩)
    (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨pcComputed_ready s h.2.1.1 (kernel := kernel),
      pcComputed_ready t h.2.2.1 (kernel := kernel)⟩)
  have output := ((loadStack_ct .r4 4).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PcComputed base dst src len k s ∧ PcComputed base dst src len k t)
    (fun _ _ h => h.1) (fun _ _ _ => True.intro)).wp
    (fun s t h => ⟨pcExport_ready s h.2.1, pcExport_ready t h.2.2⟩)
  have tail := arithmetic.seq ((output.mono (fun _ _ h => h) (fun _ _ h => h.2)).seq precomputeOut_ct)
  have all := prepared.seq tail
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | seq a1 b1 =>
    cases b1 with
    | seq b1 c1 =>
      cases c1 with
      | seq c1 d1 =>
        cases e2 with
        | seq a2 b2 =>
          cases b2 with
          | seq b2 c2 =>
            cases c2 with
            | seq c2 d2 =>
              obtain ⟨trace, post⟩ := all _ _ _ _ _ _ h
                (.seq (.seq a1 (.seq b1 c1)) d1) (.seq (.seq a2 (.seq b2 c2)) d2)
              exact ⟨by simpa only [List.append_assoc] using trace, post⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PcBodyCT.lean`, which only this module imported.
section

/-! # Public modulus validation selects two proved timing-safe branches -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PcChecked (base dst src : BitVec 32) (len k : Nat) (nb : List Byte) (s : State) : Prop where
  input : PcBodyInput base dst src len k s
  bytes : Spec.Rsa.bytesAt s.mem (State.addr src) k = nb
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k

theorem pcChecked_ready (s : State) {base dst src : BitVec 32} {len k : Nat} {nb : List Byte}
    (h : PcBodyInput base dst src len k s) (bytes : Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) :
    WP isa (.block modulusCheck) s (PcChecked base dst src len k nb) := by
  refine WP.mono (modulusCheck_ok s h.minLength h.maxLength h.sourceFits h.readable h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨⟨h.toPcBuffers.congr rest, h.stack.after_workspace frame rest,
    (rest.gpr .r0 (by simp)).trans h.ptr, (rest.gpr .r4 (by simp)).trans h.source,
    (rest.gpr .r6 (by simp)).trans h.count⟩, by rw [mem]; exact bytes, by rw [bytes] at flag; exact flag⟩

theorem pcBody_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte} (hk : k ≤ 1024)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : RelCT isa (fun s t =>
      (PcBodyInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcBodyInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (PcFn.bodyWith kernel.code) (fun _ _ => True) := by
  let P := fun (s t : State) =>
    (PcBodyInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
    (PcBodyInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp
  have check : RelCT isa P (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.source.trans h.2.1.1.source.symm, h.1.1.count.trans h.2.1.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨pcChecked_ready s h.1.1 h.1.2, pcChecked_ready t h.2.1.1 h.2.1.2⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag]
  · apply (pcValid_ct (nb := nb) (kernel := kernel) (base := base) (dst := dst) (src := src) (len := len) hk).mono ?_ (fun _ _ h => h)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := h.1.2.1.flag.symm.trans flag
    exact ⟨⟨⟨h.1.2.1.input, by rw [h.1.2.1.bytes]; exact good⟩, h.1.2.1.bytes⟩,
      ⟨⟨h.1.2.2.input, by rw [h.1.2.2.bytes]; exact good⟩, h.1.2.2.bytes⟩, h.1.1⟩
  · apply (pcFail_ct (base := base) (dst := dst) (src := src) (len := len) hk).mono ?_ (fun _ _ h => h)
    intro s t h
    exact ⟨h.1.2.1.input.stack, h.1.2.2.input.stack,
      h.1.2.1.input.count, h.1.2.2.input.count, h.1.1⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PcFnCT.lean`, which only this module imported.
section

/-! # The callable RSA precomputation leaks only its public arguments and modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcFn_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte}
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : RelCT isa (fun s t =>
      (PcFnInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcFnInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      (PcFn.codeWith kernel.code) (fun _ _ => True) := by
  unfold PcFn.codeWith
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨⟨hs, bs⟩, ⟨ht, bt⟩, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := pcEntry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, frame1, _, _⟩ := pc_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, frame2, _, _⟩ := pc_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have bytes1 := (rsa_bytes_frame (src := State.addr src) (k := k) frame1
        (by have := hs.maxLength; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hs.stackInput.symm)).trans bs
      have bytes2 := (rsa_bytes_frame (src := State.addr src) (k := k) frame2
        (by have := ht.maxLength; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ht.stackInput.symm)).trans bt
      have body := relCT_keep_sp
        (pcBody_ct (kernel := kernel) (base := base) (dst := dst) (src := src) (len := len) (nb := nb) hs.maxLength)
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨⟨ready1, bytes1⟩, ⟨ready2, bytes2⟩, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pc_contract_pre (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 56).pre s) :
    PcFnInput (stackArg s 0) (s.gpr .r0) (s.gpr .r2) (stackArg s 1).toNat (s.gpr .r3).toNat s := by
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, outWs, _, srcWs, _, stackOut, stackSrc,
    stackWs, stackArgs, outFit, srcFit, wsFit, valid, outLen, space⟩ := h
  have outBytes : (s.gpr .r1).toNat * 8 = 16 * Spec.Rsa.modulusWords (s.gpr .r3).toNat := by
    rw [outLen]; simp only [Spec.Rsa.precomputedWords]; omega
  rw [outBytes] at wr outWs stackOut outFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨⟨⟨?_, ?_⟩, valid.1, valid.2, space, srcFit, ?_, ?_, outFit, ?_, ?_⟩,
    rfl, rfl, ?_, stackFit, argFit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using wsFit
  · rw [wr]; simp [State.addr, Nat.mul_comm]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_cons_self), Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using srcWs
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using outWs.symm
  · simp
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp), Region.contains_self _ _⟩
  · simp only [stackArg, argAddr]
  · rw [frame]; simpa only [State.addr, Nat.mul_comm] using stackWs
  · rw [frame]; exact stackSrc
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

theorem pc_contract_correct (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 56).pre s)
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : ∃ tr t, Exec isa (PcFn.codeWith kernel.code) s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputeContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := pcFn_ok (kernel := kernel) s (pc_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have outLen : (s.gpr .r1).toNat = 2 * Spec.Rsa.modulusWords (s.gpr .r3).toNat := by
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [outLen, BitVec.setWidth_append_eq_right]
  exact post

theorem pc_contract_ct
    (kernel : PublicPrecomputeKernel := baselinePublicPrecomputeKernel) : ConstantTime isa (Spec.Rsa.publicPrecomputeContract abi 56).pre
    (Spec.Rsa.publicPrecomputeContract abi 56).pub (PcFn.codeWith kernel.code) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := pc_contract_pre s hs
  have it := pc_contract_pre t ht
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p2, ← p3, ← p4, ← p5] at it
  rw [← p2, ← p3] at byteEq
  exact (pcFn_ct (kernel := kernel) s t tr1 tr2 u v ⟨⟨is, rfl⟩, ⟨it, byteEq.symm⟩, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm

module

public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PublicInput

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Arm.PublicResult
import VerifiedGarbage.Proof.Bignum.Arm.ExportMasked
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.PublicImport
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccept
import VerifiedGarbage.Proof.Bignum.Arm.PublicControls
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Bignum.Arm.PublicWritten
import VerifiedGarbage.Proof.Bignum.Arm.PublicFail
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
import VerifiedGarbage.Proof.Bignum.Arm.PublicSaved
import VerifiedGarbage.Proof.Bignum.Arm.PublicEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.PublicEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Rsa.Contract
/-! # Checked public RSA satisfies its shared contract under AAPCS -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicFinish.lean`, which only this module imported.
section

/-! # Public RSA output serialization and branchless rejection -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicFinish_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicResult base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.finish s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)) k
         else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat ∧
      Frame [⟨State.addr dst, k⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PublicFn.finish, WP.seq_iff]
  refine WP.mono (publicOutputArgs_ok s h.stack) ?_
  rintro u ⟨index, output, count, memU, restU⟩
  have ready := h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  have dims := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  refine WP.mono (exportMasked_ok u ready.workspace ready.layout ready.width (by decide : 6 < 8)
    (by have := h.buffers.minLength; omega) dims.2.2.2.1 (by rw [memU]; exact h.valueFit)
    h.buffers.outputFit (by rw [restU.wr]; exact h.buffers.write) h.buffers.outputSeparate
    ready.ptr index output count (by rw [restU.sp]; have := h.stack.nowrap; omega)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.stack.read (by decide) (by decide))
    (by rw [restU.sp]; exact (h.buffers.stackOutput.sub_right (Offset.sub_base _ (by decide))).symm)
    (by rw [memU, restU.sp]; exact h.flag)) ?_
  rintro t ⟨bytes, status, frame, restT⟩
  rw [memU, h.value] at bytes
  rw [memU] at frame
  exact ⟨by simpa only [decide_eq_true_eq] using bytes, status, frame,
    (restU.mono (by decide)).trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicApply.lean`, which only this module imported.
section

/-! # The complete checked-input RSA arithmetic path, from bytes to masked output -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicApply_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.applyInput s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) k =
        (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
          Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip nb)) k
         else List.replicate k 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.applyInput, WP.seq_iff]
  refine WP.mono (publicImport_ok s h) ?_
  rintro u ⟨operand, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (publicAccept_ok u operand) ?_
  rintro v ⟨accepted, frameV, restV⟩
  rw [restU.sp] at frameV
  rw [WP.seq_iff]
  refine WP.mono (publicControls_ok v accepted) ?_
  rintro z ⟨controlled, phase, frameZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (publicExponentiate_ok z controlled phase) ?_
  rintro q ⟨result, frameQ, restQ⟩
  refine WP.mono (publicFinish_ok q result) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  exact ⟨bytes, status,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans
      ((frameZ.mono (by simp)).trans ((frameQ.mono (by simp)).trans (frameT.mono (by simp))))),
    restU.trans (restV.trans (restZ.trans (restQ.trans restT)))⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicValid.lean`, which only this module imported.
section

/-! # The public RSA path for a validated public key satisfies the shared result contract -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicValid_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicValidInput base dst np ep xp len k eLen nb eb xb s)
    (exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true) :
    WP isa PublicFn.valid s fun t =>
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.valid, WP.seq_iff]
  refine WP.mono (publicPrepare_ok s h) ?_
  rintro u ⟨prepared, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (publicPrecompute_ok u prepared) ?_
  rintro v ⟨arithmetic, frameV, restV⟩
  refine WP.mono (publicApply_ok v arithmetic) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [restV.sp, restU.sp] at frameT
  exact ⟨publicOutput_written h.buffers.modulus.length h.valid exponent bytes status,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicModulus.lean`, which only this module imported.
section

/-! # Validate the public modulus and implement both outcomes of the checked RSA contract -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicModulus_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s)
    (exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true) :
    WP isa PublicFn.modulus s fun t =>
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.modulus, WP.seq_iff]
  refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
  rintro u ⟨source, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  rw [WP.seq_iff]
  refine WP.mono (modulusCheck_ok u hu.buffers.minLength hu.buffers.maxLength hu.buffers.modulus.fits
    hu.buffers.modulus.read source count) ?_
  rintro v ⟨flag, memV, restV⟩
  rw [hu.buffers.modulus.bytes] at flag
  have hv := hu.of_mem memV restV ((restV.gpr .r0 (by decide)).trans hu.ptr)
  have rest : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (restV.mono (by decide))
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) (by change some v.z = _; rw [flag]) ?_ ?_
  · intro valid
    have input : PublicValidInput base dst np ep xp len k eLen nb eb xb v :=
      ⟨hv, valid, (restV.gpr .r4 (by decide)).trans source, (restV.gpr .r6 (by decide)).trans count⟩
    refine WP.mono (publicValid_ok v input exponent) ?_
    rintro t ⟨result, frame, restT⟩
    rw [memV, memU, rest.sp] at frame
    exact ⟨result, frame, rest.trans restT⟩
  · intro invalid
    refine WP.mono (publicFail_ok v hv) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    have failed : Spec.Rsa.publicOpChecked nb eb xb = none := by
      simp only [Spec.Rsa.publicOpChecked, exponent, ite_true, Spec.Rsa.publicOp,
        h.buffers.modulus.length, invalid, Bool.false_eq_true, ite_false]
    rw [failed]
    rw [memV, memU] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), rest.trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicBody.lean`, which only this module imported.
section

/-! # Complete ARMv7 checked public RSA body, including invalid-key failures -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicBody_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.body s fun t =>
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.body, WP.seq_iff]
  refine WP.mono (publicExponentArgs_ok s h.stack) ?_
  rintro u ⟨pointer, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ptr)
  have length := hu.buffers.exponent.length
  rw [WP.seq_iff]
  refine WP.mono (exponentCheck_ok u
    (by rw [length]; exact hu.buffers.exponentPositive)
    (by rw [length]; have := hu.buffers.exponentFits; have := hu.buffers.maxLength; omega)
    (by rw [length]; exact hu.buffers.exponent.fits)
    (by rw [length]; exact hu.buffers.exponent.read) hu.buffers.exponent.byte pointer
    (by rw [length]; exact count)) ?_
  rintro v ⟨status, memV, restV⟩
  have hv := hu.of_mem memV restV ((restV.gpr .r0 (by decide)).trans hu.ptr)
  rw [WP.seq_iff]
  refine WP.mono (exponentFlag_ok v status) ?_
  rintro z ⟨zero, memZ, restZ⟩
  have hz := hv.of_mem memZ restZ ((restZ.gpr .r0 (by decide)).trans hv.ptr)
  have rest : Rest roundClobbers s z := (restU.mono (by decide)).trans
    ((restV.mono (by decide)).trans (restZ.mono (by decide)))
  have mem : z.mem = s.mem := memZ.trans (memV.trans memU)
  refine WP.ite (!Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) (by change some z.z = _; rw [zero]) ?_ ?_
  · intro invalid
    have invalidE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = false := by simpa using invalid
    refine WP.mono (publicFail_ok z hz) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    have failed : Spec.Rsa.publicOpChecked nb eb xb = none := by simp [Spec.Rsa.publicOpChecked, invalidE]
    rw [failed]
    rw [mem] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), rest.trans restT⟩
  · intro valid
    have validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true := by simpa using valid
    refine WP.mono (publicModulus_ok z hz validE) ?_
    rintro t ⟨result, frame, restT⟩
    rw [mem, rest.sp] at frame
    exact ⟨result, frame, rest.trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicFn.lean`, which only this module imported.
section

/-! # Callable ARMv7 checked public RSA preserves AAPCS and implements the shared result -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem publicFn_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicFnInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.code s fun t => abiPreserved s t ∧
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) := by
  unfold PublicFn.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (public_entry_ready s h) ?_
  rintro u ⟨ready, _, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (publicBody_ok u ready) ?_
  rintro v ⟨result, frameV, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply public_callee_saved savedU frameV
    · rw [restU.sp]; exact h.stackWorkspace
    · rw [restU.sp]; exact h.stackOutput
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

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PublicFnCT.lean`, which only this module imported.
section

/-! # The callable checked public RSA operation leaks only public arguments, modulus, and exponent -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicFn_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicFnInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicFnInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.code (fun _ _ => True) := by
  unfold PublicFn.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
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
      obtain ⟨trace, sp'⟩ := publicEntry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, _, _, _⟩ := public_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, _, _, _⟩ := public_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have body := relCT_keep_sp
        (publicBody_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
          (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2))
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem public_contract_pre (s : State) (h : (Proof.Rsa.publicCheckedContract abi 56).pre s) :
    PublicFnInput (stackArg s 4) (s.gpr .r0) (s.gpr .r2) (stackArg s 0) (stackArg s 2)
      (stackArg s 5).toNat (s.gpr .r3).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (s.gpr .r3).toNat) s := by
  sig_pre [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  have argAddr : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr] at h
  obtain ⟨stackFit, argFit, rd, wr, _, _, _, outWs, _, nWs, eWs, xWs, wsArgs,
    stackOut, stackN, stackE, stackX, stackWs, stackArgs, outFit, nFit, eFit, xFit, wsFit,
    valid, outLen, inputLen, ePositive, eLen, space⟩ := h
  rw [outLen] at wr outWs stackOut outFit
  rw [inputLen] at rd xWs stackX xFit
  have frame : FrameStack.belowA s.sp 56 = ⟨State.addr s.sp - BitVec.ofNat 64 56, 56⟩ := by
    unfold FrameStack.belowA
    rw [FrameStack.addr_sub' stackFit]
  refine ⟨⟨?_, ?_⟩, valid.1, valid.2, space, ePositive, eLen,
    ⟨nFit, ?_, rfl⟩, ⟨eFit, ?_, rfl⟩, ⟨xFit, ?_, rfl⟩, outFit, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, ?_, stackFit, argFit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using wsFit
  · rw [wr]; simp [State.addr, Nat.mul_comm]
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · exact ⟨_, by rw [wr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  · simpa only [State.addr, Nat.mul_comm] using nWs
  · simpa only [State.addr, Nat.mul_comm] using eWs
  · simpa only [State.addr, Nat.mul_comm] using xWs
  · simpa only [State.addr, Nat.mul_comm] using outWs.symm
  · simp
  · exact ⟨_, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  · unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 4 < 2 ^ 32)]
  · simp only [stackArg, argAddr]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 1 < 2 ^ 32)]
  · unfold stackArg stackArgAddr
    rw [addr_add (by omega : s.sp.toNat + 4 * 2 < 2 ^ 32)]
  · rw [frame]; simpa only [State.addr, Nat.mul_comm] using stackWs
  · simpa only [State.addr, Nat.mul_comm] using wsArgs.symm
  · rw [frame]; exact stackN
  · rw [frame]; exact stackE
  · rw [frame]; exact stackX
  · rw [frame]; exact stackOut
  · rw [frame]; exact stackArgs

theorem public_contract_correct (s : State) (h : (Proof.Rsa.publicCheckedContract abi 56).pre s) :
    ∃ tr t, Exec isa PublicFn.code s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.publicCheckedContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := publicFn_ok s (public_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem public_contract_ct : ConstantTime isa (Proof.Rsa.publicCheckedContract abi 56).pre
    (Proof.Rsa.publicCheckedContract abi 56).pub PublicFn.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := public_contract_pre s hs
  have it := public_contract_pre t ht
  sig_pub [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, _, p8, p9⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p2, ← p3, ← p4, ← p5, ← p6, ← p8, ← p9] at it
  rw [← p2, ← p3, ← p4, ← p5] at byteEq
  obtain ⟨nEq, eEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  simp only [State.addr] at it
  rw [← nEq, ← eEq] at it
  exact (publicFn_ct s t tr1 tr2 u v ⟨is, it, sp⟩ e1 e2).1

end VG.Proof.Bignum.Arm

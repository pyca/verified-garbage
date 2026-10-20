module

import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw

/-! # Finish a key-generation attempt using shared arithmetic calls -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sampleCallTail_ok {power : Prog isa} (law : SamplePowerLaw power) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {xb eb : List Byte}
    (h : SampleContext p l slots s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (scalarSize : xb.length = p.k)
    (significant : Octets p.base l.start p.len eb s) (significantSize : eb.length = l.width)
    (significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (outputs : KeyOutputs p s) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  have fits : Spec.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.KeyGenerate.tail, WP.seq_iff]
  refine WP.mono (law.correct s h calls stable h56 h32 ready modulus odd r2 significant significantSize) ?_
  rintro u ⟨contextU, readyU, powerU, modU, _, _, frameU, restU⟩
  rw [significantValue] at powerU
  change numAt u.mem (State.addr p.base) p.w 6 = keyPower p xb at powerU
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, flag, arraysV, frameV, restV⟩
  have contextV := contextU.after_workspace frameV restV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  have powerV := (arraysV 6 (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans powerU
  have flagV : v.gpr .r11 = if keyAccepted p xb then 1 else 0 := by
    rw [powerU, modU] at flag
    simpa only [keyAccepted, decide_eq_true_eq] using flag
  rw [WP.seq_iff]
  refine WP.mono (saveResult_ok v contextV.locals) ?_
  rintro w ⟨⟨_, resultW, frameW⟩, restW⟩
  have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
  have contextW := contextV.after_local (by decide : 64 + 4 ≤ 72) frameW restW ptrW
    (fun d hd => (stableSlots_at stable hd).1) saved
  have readyW := readyV.after_external frameW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    exact contextV.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))) (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [off, BitVec.add_zero] using
      Offset.disjoint (State.addr v.sp) (d := 0) (n := 4) (e := 64) (k := 4) (by left; decide) (by decide) (by decide)) restW ptrW
  have powerW := (readyW.2.number fits (by decide : 6 < 8)).trans powerV
  have powerFits : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [powerW, keyPower, VG.Proof.Bignum.powMod_eq]
    have large := ready.modulus
    rw [modulus] at large
    exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound
  rw [WP.seq_iff]
  refine WP.mono (exportResult_ok w contextW h4 h32 readyW.1
    (by rw [outputY]; exact ((outputs.publicBuffer.after restU).after restV).after restW)
    (by rw [outputY]; exact outputs.publicWorkspace.symm) powerFits) ?_
  rintro z ⟨publicZ, frameZ, restZ⟩
  rw [powerW, outputY] at publicZ
  rw [outputY] at frameZ
  have outW := ((outputs.after restU).after restV).after restW
  have contextZ := contextW.toArgumentMemory.after_output frameZ restZ outW.publicDomain outW.publicStack
    (fun d hd => (stableSlots_at stable hd).1)
  have resultZ : z.mem.readW (off (State.addr z.sp) 64) 32 = if keyAccepted p xb then 1 else 0 := by
    rw [restZ.sp, frameZ.readW (r := ⟨off (State.addr w.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outW.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide), restW.sp, resultW, flagV]
  refine WP.mono (keyFinish_ok z (keyAccepted p xb) contextZ (fun d hd => (stableSlots_at stable hd).1)
    h32 h36 h40 (outW.after restZ) resultZ) ?_
  rintro t ⟨status, privateT, publicT, frameT, _⟩
  have privateU := scalar.after_call frameU restU (by simpa only [scalarSize] using calls.privateValue)
  have privateW := (privateU.after_workspace frameV restV).after_frame frameW restW (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    simpa only [scalarSize, restV.sp, restU.sp] using
      outputs.privateStack.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72)))
  have privateZ := privateW.after_frame frameZ restZ (by simpa only [scalarSize, List.mem_singleton, forall_eq] using outputs.separate)
  have privateBytesZ := privateZ.bytes
  rw [scalarSize] at privateBytesZ
  rw [privateBytesZ] at privateT
  rw [publicZ] at publicT
  refine ⟨status, privateT, publicT, ?_⟩
  have fullU : Frame (keyCallWrites p s) s.mem u.mem := frameU.mono (by simp [keyCallWrites, keyWrites])
  have fullV : Frame (keyCallWrites p s) u.mem v.mem := frameV.mono (by simp [keyCallWrites, keyWrites])
  have fullW : Frame (keyCallWrites p s) v.mem w.mem := frameW.sub (by
    intro r hr; rw [List.mem_singleton] at hr; subst r
    refine ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], ?_⟩
    rw [restV.sp, restU.sp]
    exact Offset.sub_base _ (by decide))
  exact (((fullU.trans fullV).trans fullW).trans (frameZ.mono (by simp [keyCallWrites, keyWrites]))).trans
    (frameT.mono (by simp [keyCallWrites, keyWrites]))

end VG.Proof.Ffdh.Arm

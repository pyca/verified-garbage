module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw

import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
/-! # The shared Montgomery backend supplies key generation's exponentiation law -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyCallTail.lean`, which only this module imported.
section

/-! # Finish a key-generation attempt using shared arithmetic calls -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem keyCallTail_ok {power : Prog isa} (law : KeyPowerLaw power) (s : State) {p : Inputs} {slots : List Nat} {xb eb : List Byte}
    (h : Context p slots s) (calls : KeyCallMemory p s) (stable : stableSlots slots = true)
    (h4 : 4 ∈ slots) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (scalar : Octets p.base p.privateValue p.len xb s) (scalarSize : xb.length = p.k)
    (significant : Octets p.base p.scalarStart p.len eb s) (significantSize : eb.length = p.scalarWidth)
    (significantValue : Spec.Rsa.os2ip eb = Spec.Rsa.os2ip xb)
    (outputs : KeyOutputs p s) (outputY : p.output = p.publicValue) :
    WP isa (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) s fun t =>
      t.gpr .r0 = (if keyAccepted p xb then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if keyAccepted p xb then xb else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if keyAccepted p xb then Spec.Rsa.i2osp (keyPower p xb) p.k else List.replicate p.k 0) ∧
      Frame (keyCallWrites p s) s.mem t.mem := by
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.KeyGenerate.tail, WP.seq_iff]
  refine WP.mono (law.correct s h calls stable h56 h16 h20 h32 ready modulus odd r2 significant significantSize) ?_
  rintro u ⟨contextU, readyU, powerU, modU, _, _, frameU, restU⟩
  rw [significantValue] at powerU
  change numAt u.mem (State.addr p.base) p.w 6 = keyPower p xb at powerU
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, flag, arraysV, frameV, restV⟩
  have contextV := contextU.after_workspace frameV restV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  have powerV := (arraysV 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerU
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyCallTailCT.lean`, which only this module imported.
section

/-! # Key-generation finish timing with shared exponentiation -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

theorem keyCallPower_next {power : Prog isa} (law : KeyPowerLaw power) (s : State)
    {p : Inputs} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (size : eb.length = p.scalarWidth) (odd : p.P % 2 = 1)
    (h : KeyPowerInput p slots eb s ∧ KeyCallMemory p s) :
    WP isa power s (KeyRangeInput p slots) := by
  refine WP.mono (law.correct s h.1.context h.2 stable h56 h16 h20 h32 h.1.ready h.1.modulus odd
    h.1.r2 h.1.exponent size) ?_
  rintro t ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.1.outputs.after rest, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  have large := h.1.ready.modulus
  rw [h.1.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem keyCallTail_ct {power : Prog isa} (law : KeyPowerLaw power)
    {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = p.scalarWidth) (size2 : eb2.length = p.scalarWidth)
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => (KeyPowerInput p slots eb1 s ∧ KeyCallMemory p s) ∧
      (KeyPowerInput p slots eb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) (fun _ _ => True) := by
  have range := (inRange_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.tail
  exact relCT_chain (law.ct stable h56 h16 h20 h32 size1 size2 odd)
    (keyCallPower_next law · stable h16 h20 h32 h56 size1 odd)
    (keyCallPower_next law · stable h16 h20 h32 h56 size2 odd)
    (relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY))

theorem keyCallTail_law {power : Prog isa} (law : KeyPowerLaw power) :
    KeyTailLaw (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) where
  correct := keyCallTail_ok law
  ct := keyCallTail_ct law

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyPowerAtCT.lean`, which only this module imported.
section

/-! # Key-generation power pointer setup and shared phase timing -/

section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem powerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb1 eb2 : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fallback : Fallback p.base p.len p.w P regions)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb1.length) (fits : eb1.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb1.length) (length : eb1.length = eb2.length)
    (odd : M % 2 = 1) :
    RelCT isa (fun s t => ArgsInput p slots bs es M P regions bb eb1 s ∧
      ArgsInput p slots bs es M P regions bb eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyPower.powerAt A.phase fallback.code bs es ec) (fun _ _ => True) := by
  have tableFit : arrAt p.w 3 + 32 ≤ 8 * p.len := by
    have f := p.width.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at *
    omega
  have positiveW : 0 < 2 * p.w := by have := p.width.1; omega
  unfold VG.Impl.Ffdh.Arm.KeyPower.powerAt
  exact relCT_chain
    ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => WP.mono (args_input s A stable hb he hc hk baseLength positive fits count odd h) fun _ k => k.1)
    (fun s h => WP.mono (args_input s A stable hb he hc hk baseLength
      (by rw [← length]; exact positive) (by rw [← length]; exact fits)
      (by rw [← length]; exact count) odd h) fun _ k => k.1)
    (power_ct A ct fallback tableFit positiveW positive length)

end VG.Proof.Ffdh.Arm.KeyPower
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyGenerate
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

def arithmetic (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :=
  TwoExp.sharedMontgomery base sp len w b.name b.mul
    (fun _ _ _ ho ha hb s h => b.correct s h ho ha hb) b.stackOk

theorem timing (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :
    TwoExp.MontgomeryTiming (arithmetic b base sp len w) :=
  TwoExp.sharedMontgomeryTiming base sp len w b.name b.mul
    (fun _ _ _ ho ha hb s h => b.correct s h ho ha hb) b.stackOk
    (fun _ _ _ ho ha hb => b.rawCT ho ha hb)

def fallback {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fits : arrAt w 16 ≤ 8 * len) : KeyPower.Fallback base len w P regions where
  code := VG.Impl.Bignum.Arm.SharedWindow.phase A.op
  correct := by
    intro s ep M x eb h
    exact sharedWindowExpPhase_ok A s h.phase h.persistent fits h.separate
  ct := by
    intro ep M1 M2 x eb1 eb2 positive length s t tr1 tr2 u v h e1 e2
    exact SharedWindow.phase_ct A ct fits positive length h.1.separate s t tr1 tr2 u v
      ⟨⟨h.1.phase, h.1.persistent⟩, ⟨h.2.1.phase, h.2.1.persistent⟩, h.2.2⟩ e1 e2

private theorem powerLaw (b : MontBackend) : KeyPowerLaw
    (VG.Impl.Ffdh.Arm.KeyPower.powerAt
      (VG.Impl.Ffdh.Arm.KeyPower.twoPhase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (VG.Impl.Bignum.Arm.SharedWindow.phase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) 56 16 20) := by
  constructor
  · intro s p slots eb context calls stable h56 h16 h20 h32 ready modulus odd r2 significant size
    let A := arithmetic b p.base s.sp p.len p.w
    let F := fallback A (timing b p.base s.sp p.len p.w) p.width.2.2.1
    have input : KeyPower.ArgsInput p slots 56 16 p.P (TwoExp.CallReady p.base s.sp p.len)
        [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] ((p.dom.drop p.k).take p.k) eb s := by
      refine ⟨⟨context, ready, modulus, r2, context.gBytes, significant⟩, ⟨calls.stack, rfl⟩, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact significant.separate
      · change Region.Disjoint ⟨State.addr p.scalarStart, eb.length⟩ _
        rw [size]; exact calls.significant_below
    refine WP.mono (KeyPower.powerAt_ok s A F stable h56 h16 h20 h32 p.gLength
      (by rw [size]; exact p.scalarWidthBounds.1)
      (by rw [size]; have := p.scalarWidthBounds; have := p.maxLength; omega)
      (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size]) odd input calls) ?_
    rintro t ⟨ctx, rd, value, m, rr, one, _, frame, rest⟩
    exact ⟨ctx, rd, value, m, rr, one, frame, rest⟩
  · intro p slots eb1 eb2 stable h56 h16 h20 h32 size1 size2 odd s t tr1 tr2 u v h e1 e2
    let A := arithmetic b p.base s.sp p.len p.w
    let F := fallback A (timing b p.base s.sp p.len p.w) p.width.2.2.1
    have mkInput (z : State) (eb : List Byte) (hz : KeyPowerInput p slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = p.scalarWidth) :
        KeyPower.ArgsInput p slots 56 16 p.P (TwoExp.CallReady p.base s.sp p.len)
          [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] ((p.dom.drop p.k).take p.k) eb z := by
      refine ⟨hz.toPowerAtInput, ⟨calls.stack, sp⟩, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz.exponent.separate
      · change Region.Disjoint ⟨State.addr p.scalarStart, eb.length⟩ _
        rw [size, ← sp]; exact calls.significant_below
    exact KeyPower.powerAt_ct A (timing b p.base s.sp p.len p.w) F stable h56 h16 h20 h32 p.gLength
      (by rw [size1]; exact p.scalarWidthBounds.1)
      (by rw [size1]; have := p.scalarWidthBounds; have := p.maxLength; omega)
      (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size1]) (size1.trans size2.symm) odd
      s t tr1 tr2 u v ⟨mkInput s eb1 h.1.1 h.1.2 rfl size1,
        mkInput t eb2 h.2.1.1 h.2.1.2 h.2.2.symm size2, h.2.2⟩ e1 e2

theorem tailLaw (b : MontBackend) : KeyTailLaw (tail b) :=
  keyCallTail_law (powerLaw b)

end VG.Proof.Ffdh.Arm.KeyGenerate

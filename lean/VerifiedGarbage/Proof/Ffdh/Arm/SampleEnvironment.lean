module

import VerifiedGarbage.Proof.Framework.Arm.Syms
public import Init.Core
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExportResult
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFinishCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-! ### `Ffdh.Arm.KeyTailLaw`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyTail`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyFinish`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeyMask`, which this module and modules that import it used -/

section

/-! Branch-free masking of either complete key encoding by its saved validity flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyMaskArgs_ok (s : State) {p : Inputs} {slots : List Nat} {flag : BitVec 32} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag) :
    WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64,
      .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) s fun t =>
      (t.gpr .r0 = p.slotValue slot ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧
        t.gpr .r2 = 0 - flag ∧ t.mem = s.mem) ∧ Rest [.r0, .r2, .r3, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have k32 : p.slotValue 32 = BitVec.ofNat 32 p.k := rfl
  refine withRest_all [.r0, .r2, .r3, .lr] ?_ (by rfl) (by rfl)
  ffrun [(by omega_using [fit] : slot < 4096), addr slot fit, addr 32 (by decide), addr 64 (by decide),
    h.locals.read fit, h.locals.read (d := 32) (by decide), h.locals.read (d := 64) (by decide),
    h.saved slot hs, h.saved 32 hk, result, k32]

theorem keyMask_ok (s : State) {p : Inputs} {slots : List Nat} {flag : BitVec 32} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = flag)
    (output : OutputBuffer (p.slotValue slot) p.k s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (p.slotValue slot)) p.k =
        (Spec.Rsa.bytesAt s.mem (State.addr (p.slotValue slot)) p.k).map (· &&& (0 - flag).setWidth 8) ∧
      Frame [⟨State.addr (p.slotValue slot), p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput, WP.seq_iff]
  refine WP.mono (keyMaskArgs_ok s slot h fit hs hk result) ?_
  rintro u ⟨⟨ptr, count, mask, mem⟩, restU⟩
  refine WP.mono (VG.Proof.Bignum.Arm.maskBuffer_ok u (by have := p.minLength; omega_using [this])
    (by have := p.maxLength; omega_using [this]) output.fits (by rw [restU.wr]; exact output.writable) ptr count) ?_
  rintro t ⟨bytes, frame, rest⟩
  rw [mask, mem] at bytes
  exact ⟨bytes, by rw [mem] at frame; exact frame, (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Finish a generated key with status 1 or 3 and mask both outputs without
branching on the secret result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyMaskAll (b : Byte) : b &&& (255#8) = b := BitVec.and_allOnes

theorem keyFinishStatus_ok (s : State) {p : Inputs} {slots : List Nat} (accepted : Bool)
    (h : ArgumentMemory p slots s)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = if accepted then 1 else 0) :
    WP isa (.block [.ldrSp .r3 64, .mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]) s fun t =>
      (t.gpr .r0 = (if accepted then 1 else 3) ∧ t.mem = s.mem) ∧ Rest [.r0, .r3] s t := by
  have addr : State.addr (s.sp + BitVec.ofNat 32 64) = off (State.addr s.sp) 64 :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [this])
  refine withRest_all [.r0, .r3] ?_ (by rfl) (by rfl)
  cases accepted <;> ffrun [addr, h.locals.read (d := 64) (by decide), result]

theorem keyFinish_ok (s : State) {p : Inputs} {slots : List Nat} (accepted : Bool)
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (outputs : KeyOutputs p s)
    (result : s.mem.readW (off (State.addr s.sp) 64) 32 = if accepted then 1 else 0) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish s fun t =>
      t.gpr .r0 = (if accepted then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.k else List.replicate p.k 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        (if accepted then Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k else List.replicate p.k 0) ∧
      Frame [⟨State.addr p.privateValue, p.k⟩, ⟨State.addr p.publicValue, p.k⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish, WP.seq_iff]
  refine WP.mono (keyMask_ok s 40 h (by decide) h40 h32 result outputs.privateBuffer) ?_
  rintro u ⟨privateU, frameU, restU⟩
  change Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem at frameU
  have contextU := h.after_output frameU restU outputs.privateDomain outputs.privateStack saved
  have resultU : u.mem.readW (off (State.addr u.sp) 64) 32 = if accepted then 1 else 0 := by
    rw [restU.sp, frameU.readW (r := ⟨off (State.addr s.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa using outputs.privateStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide)]
    exact result
  rw [WP.seq_iff]
  refine WP.mono (keyMask_ok u 36 contextU (by decide) h36 h32 resultU (outputs.publicBuffer.after restU)) ?_
  rintro v ⟨publicV, frameV, restV⟩
  change Frame [⟨State.addr p.publicValue, p.k⟩] u.mem v.mem at frameV
  have contextV := contextU.after_output frameV restV outputs.publicDomain
    (by rw [restU.sp]; exact outputs.publicStack) saved
  have resultV : v.mem.readW (off (State.addr v.sp) 64) 32 = if accepted then 1 else 0 := by
    rw [restV.sp, frameV.readW (r := ⟨off (State.addr u.sp) 64, 4⟩) (Region.contains_self _ _)
      (by simpa only [restU.sp, List.mem_singleton, forall_eq] using
        outputs.publicStack.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))) (by decide)]
    exact resultU
  refine WP.mono (keyFinishStatus_ok v accepted contextV resultV) ?_
  rintro t ⟨⟨status, memT⟩, restT⟩
  have privateT := VG.Proof.Bignum.Arm.rsa_bytes_frame (k := p.k) frameV (by have := p.maxLength; omega_using [this])
    (by simpa using outputs.separate)
  have publicU := VG.Proof.Bignum.Arm.rsa_bytes_frame (k := p.k) frameU (by have := p.maxLength; omega_using [this])
    (by simpa using outputs.separate.symm)
  change Spec.Rsa.bytesAt u.mem (State.addr p.privateValue) p.k = _ at privateU
  change Spec.Rsa.bytesAt v.mem (State.addr p.publicValue) p.k = _ at publicV
  simp only [Inputs.slotValue] at privateU publicV
  rw [publicU] at publicV
  refine ⟨status, ?_, ?_, ?_, (restU.trans restV).trans (restT.mono (by simp))⟩
  · rw [memT, privateT, privateU]
    cases accepted <;> simp [Spec.Rsa.bytesAt, List.map_map, Function.comp_def, List.map_const', keyMaskAll]
  · rw [memT, publicV]
    cases accepted <;> simp [Spec.Rsa.bytesAt, List.map_map, Function.comp_def, List.map_const', keyMaskAll]
  · rw [memT]
    exact (frameU.mono (by simp)).trans (frameV.mono (by simp))

end VG.Proof.Ffdh.Arm

end

end

/-! Generate a public value with RSA's fixed-window secret exponentiation and
finish both key encodings with a branch-free validity mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

def keyPower (p : Inputs) (xb : List Byte) : Nat := Spec.Rsa.powMod p.G (Spec.Rsa.os2ip xb) p.P

def keyAccepted (p : Inputs) (xb : List Byte) : Bool := decide (1 < keyPower p xb ∧ keyPower p xb < p.P - 1)

def keyWrites (p : Inputs) (s : State) : List Region :=
  [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr s.sp, 72⟩,
    ⟨State.addr p.privateValue, p.k⟩, ⟨State.addr p.publicValue, p.k⟩]

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyClear`, which this module and modules that import it used -/

section

/-! A rejected scalar attempt clears a full private or public output encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyClearArgs_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) s fun t =>
      (t.gpr .r0 = p.slotValue slot ∧ t.gpr .lr = BitVec.ofNat 32 p.k ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧
      Rest [.r0, .r2, .lr] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  refine withRest_all [.r0, .r2, .lr] ?_ (by rfl) (by rfl)
  ffrun [(by omega_using [fit] : slot < 4096), addr slot fit, addr 32 (by decide), h.locals.read fit, h.locals.read (d := 32) (by decide),
    h.saved slot hs, h.saved 32 hk, Inputs.slotValue]

theorem keyClear_ok (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (h : ArgumentMemory p slots s) (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (output : OutputBuffer (p.slotValue slot) p.k s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr (p.slotValue slot)) p.k = List.replicate p.k 0 ∧
      Frame [⟨State.addr (p.slotValue slot), p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput, WP.seq_iff]
  refine WP.mono (keyClearArgs_ok s slot h fit hs hk) ?_
  rintro u ⟨⟨ptr, count, zero, mem⟩, restU⟩
  refine WP.mono (zeroBuffer_ok false u (by have := p.minLength; omega_using [this]) (by have := p.maxLength; omega_using [this])
    output.fits (by rw [restU.wr]; exact output.writable) zero (src := u.gpr .r1) rfl ptr count) ?_
  rintro t ⟨bytes, _, _, frame, rest⟩
  exact ⟨bytes, by rw [mem] at frame; exact frame, (restU.mono (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.KeyTailCT`, which this module and modules that import it used -/

section

/-! Generated-public-value exponentiation, checking, export and masking have
the same trace for different secret scalars of the public significant width. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyOutputsCT.lean`, which only this module imported.
section

/-! Clearing and masking complete key encodings never branches on their contents
or the saved secret result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem keyMask_ct {p : Inputs} {slots : List Nat} (slot : Nat)
    (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    RelCT isa (fun s t => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.slotValue slot ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := (keyMaskArgs_ct slot).mono
    (P' := fun (s t : State) => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : ArgumentMemory p slots s) : WP isa
      (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) s Q :=
    WP.mono (keyMaskArgs_ok s slot h fit hs hk rfl) (fun _ h => ⟨h.1.1, h.1.2.1⟩)
  have loop : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp) VG.Impl.Bignum.Arm.maskBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.1.symm, h.1.2.trans h.2.1.2.symm⟩ e1 e2, trivial⟩
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput
  exact relCT_chain args wp wp loop

theorem keyClear_ct {p : Inputs} {slots : List Nat} (slot : Nat)
    (fit : slot + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots) :
    RelCT isa (fun s t => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = p.slotValue slot ∧ s.gpr .lr = BitVec.ofNat 32 p.k
  have args := (keyClearArgs_ct slot).mono
    (P' := fun (s t : State) => ArgumentMemory p slots s ∧ ArgumentMemory p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : ArgumentMemory p slots s) :
      WP isa (.block [.ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) s Q :=
    WP.mono (keyClearArgs_ok s slot h fit hs hk) (fun _ h => ⟨h.1.1, h.1.2.1⟩)
  have loop := keyZeros_ct.mono
    (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp) (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.trans h.2.1.1.symm
      · exact h.1.2.trans h.2.1.2.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput
  exact relCT_chain args wp wp loop

structure KeyOutputState (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : ArgumentMemory p slots s
  outputs : KeyOutputs p s

theorem keyOutput_mask (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (which : slot = 40 ∨ slot = 36) (h : KeyOutputState p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.maskOutput slot) s (KeyOutputState p slots) := by
  rcases which with rfl | rfl
  · refine WP.mono (keyMask_ok s 40 h.context (by decide) hs hk rfl h.outputs.privateBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.privateDomain h.outputs.privateStack saved, h.outputs.after rest⟩
  · refine WP.mono (keyMask_ok s 36 h.context (by decide) hs hk rfl h.outputs.publicBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved, h.outputs.after rest⟩

theorem keyOutput_clear (s : State) {p : Inputs} {slots : List Nat} (slot : Nat)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (hs : slot ∈ slots) (hk : 32 ∈ slots)
    (which : slot = 40 ∨ slot = 36) (h : KeyOutputState p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.clearOutput slot) s (KeyOutputState p slots) := by
  rcases which with rfl | rfl
  · refine WP.mono (keyClear_ok s 40 h.context (by decide) hs hk h.outputs.privateBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.privateDomain h.outputs.privateStack saved, h.outputs.after rest⟩
  · refine WP.mono (keyClear_ok s 36 h.context (by decide) hs hk h.outputs.publicBuffer) ?_
    rintro t ⟨_, frame, rest⟩
    exact ⟨h.context.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved, h.outputs.after rest⟩

theorem keyFinish_ct {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) :
    RelCT isa (fun s t => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish (fun _ _ => True) := by
  have mask40 := (keyMask_ct 40 (by decide) h40 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have mask36 := (keyMask_ct 36 (by decide) h36 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish
  exact relCT_chain mask40 (keyOutput_mask · 40 saved h40 h32 (.inl rfl)) (keyOutput_mask · 40 saved h40 h32 (.inl rfl))
    ((relCT_keep_sp mask36 (fun _ _ h => h.2.2)).seq keyFinishStatus_ct)

theorem keyFail_ct {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) :
    RelCT isa (fun s t => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar (fun _ _ => True) := by
  have clear40 := (keyClear_ct 40 (by decide) h40 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have clear36 := (keyClear_ct 36 (by decide) h36 h32).mono
    (P' := fun (s t : State) => KeyOutputState p slots s ∧ KeyOutputState p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar
  exact relCT_chain clear40 (keyOutput_clear · 40 saved h40 h32 (.inl rfl)) (keyOutput_clear · 40 saved h40 h32 (.inl rfl))
    (clear36.seq ((ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyFinishCT.lean`, which only this module imported.
section

/-! Public-value export and final key masking have a fixed trace for every
secret exponent and result flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure KeyExportInput (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  outputs : KeyOutputs p s
  valueFit : numAt s.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k)

theorem keySave_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult) s (KeyExportInput p slots) := by
  have exchange : ExchangeFinishInput p slots s :=
    ⟨h.context, h.ready, by rw [outputY]; exact h.outputs.publicBuffer,
      by rw [outputY]; exact h.outputs.publicWorkspace.symm,
      by rw [outputY]; exact h.outputs.publicStack, h.valueFit⟩
  refine WP.mono (withAllRest (exchangeSave_ready s exchange stable saved)) ?_
  rintro t ⟨result, rest⟩
  exact ⟨result.context, result.ready, h.outputs.after rest, result.valueFit⟩

theorem keyExport_next (s : State) {p : Inputs} {slots : List Nat}
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (outputY : p.output = p.publicValue) (h : KeyExportInput p slots s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult s (KeyOutputState p slots) := by
  refine WP.mono (exportResult_ok s h.context h4 h32 h.ready
    (by rw [outputY]; exact h.outputs.publicBuffer) (by rw [outputY]; exact h.outputs.publicWorkspace.symm) h.valueFit) ?_
  rintro t ⟨_, frame, rest⟩
  rw [outputY] at frame
  exact ⟨h.context.toArgumentMemory.after_output frame rest h.outputs.publicDomain h.outputs.publicStack saved,
    h.outputs.after rest⟩

theorem keyExportFinish_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
      (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
        (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish)) (fun _ _ => True) := by
  have bounds (d : Nat) (hd : d ∈ slots) := (stableSlots_at stable hd).1
  have save := (RelCT.block_append (stackAddr_ct.seq (storeLocal_ct .r11 64))).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have exportCT := (exportResult_ct h4 h32).mono
    (P' := fun (s t : State) => KeyExportInput p slots s ∧ KeyExportInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  exact relCT_chain save (keySave_next · stable saved outputY) (keySave_next · stable saved outputY)
    (relCT_chain exportCT (keyExport_next · bounds h4 h32 outputY) (keyExport_next · bounds h4 h32 outputY)
      (keyFinish_ct bounds h32 h36 h40))

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

structure KeyRangeInput (p : Inputs) (slots : List Nat) (s : State) : Prop extends KeyExportInput p slots s where
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P

theorem keyRange_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (odd : p.P % 2 = 1) (h : KeyRangeInput p slots s) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 6) s (KeyExportInput p slots) := by
  refine WP.mono (inRange_ok s h.ready (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro t ⟨ready, _, arrays, frame, rest⟩
  exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    h.outputs.after rest, by rw [arrays 6 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.valueFit⟩

end VG.Proof.Ffdh.Arm

end

end

/-! # The public-value exponentiation boundary of a key-generation attempt -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

def keyCallWrites (p : Inputs) (s : State) : List Region :=
  keyWrites p s ++ [FrameStack.belowA s.sp 48]

end VG.Proof.Ffdh.Arm

end

end

/-! Read-only public environment supplied to a scalar-sampling policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure SampleEnvironment where
  holds : Inputs → State → Prop
  publicRel : State → State → Prop
  stable : ∀ {p : Inputs} {s t : State}, holds p s →
    Frame (keyCallWrites p s) s.mem t.mem → Rest roundClobbers s t →
    t.syms = s.syms → holds p t
  public_stable : ∀ {s t u v : State}, publicRel s t →
    u.syms = s.syms → v.syms = t.syms → publicRel u v

end VG.Proof.Ffdh.Arm

module
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInitialize

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands

/-! # Public observations used to relate two complete verification calls

The reference call supplies public lengths, addresses and domain bytes. The
relation does not equate signatures, digests or scratch contents.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerifyingCall where
  input : VerifyingInput
  original : State
  pre : VerifyingPre input original

abbrev VerifyingCall.layout (c : VerifyingCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength c.pre.qLength

structure VerifyingAgrees (reference c : VerifyingCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q
  digestLength : c.input.digest.length = reference.input.digest.length
  stack : c.original.gpr .rsp = reference.original.gpr .rsp

def VerifyingStart (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ c.original = s

def VerifyingEntered (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧
    VerifyEntryPost c.original c.input.base c.input.digestPointer
      (BitVec.ofNat 64 c.input.digest.length) s

def VerifyingShaped (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ VerifyingShapePost c.input c.original c.pre.pLength c.pre.qLength s

def VerifyingReady (reference : VerifyingCall) (s : State) : Prop :=
  ∃ c : VerifyingCall, VerifyingAgrees reference c ∧ VerifyingInitialized c.input c.original c.pre.pLength c.pre.qLength s

def VerifyingCall.shape (c : VerifyingCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := c.input.digest.length
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega
  qPositive := by rw [c.input.components.qLength]; exact c.layout.widths.1
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
  digestBound := c.input.digestBound

theorem VerifyingAgrees.shape {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.shape = reference.shape := by
  unfold VerifyingCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes
  · exact h.digestLength

theorem VerifyingAgrees.accepted {reference c : VerifyingCall} (h : VerifyingAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold VerifyingInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem VerifyingEntered.context {reference : VerifyingCall} {s : State} (h : VerifyingEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.p, he.q, ?_, ?_, he.digestLen,
    source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen.trans c.pre.qLength
  · change Src s c.input.base usedBytes (c.original.gpr .rdi + c.original.gpr .rdx) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)

end VG.Proof.Dsa.X86_64

module
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInitialize
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Public observations used to relate two complete signing calls

The reference call supplies public lengths, addresses and domain bytes. The
relation does not equate private scalars, nonces, digests or scratch contents.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SigningCall where
  input : SigningInput
  original : State
  pre : SigningPre input original

abbrev SigningCall.layout (c : SigningCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength

structure SigningAgrees (reference c : SigningCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q
  digestLength : c.input.digest.length = reference.input.digest.length
  stack : c.original.sp = reference.original.sp

def SigningStart (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ c.original = s

def SigningEntered (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧
    SignEntryPost c.original c.input.base (BitVec.ofNat 64 c.input.qLen) c.input.digestPointer
      (BitVec.ofNat 64 c.input.digest.length) s

def SigningShaped (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ SigningShapePost c.input c.original c.pre.pLength s

def SigningReady (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ SigningInitialized c.input c.original c.pre.pLength s

def SigningCall.shape (c : SigningCall) : ShapePublic where
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

theorem SigningAgrees.shape {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.shape = reference.shape := by
  unfold SigningCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes
  · exact h.digestLength

theorem SigningAgrees.accepted {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold SigningInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem SigningEntered.context {reference : SigningCall} {s : State} (h : SigningEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.p, he.q, ?_, ?_, he.digestLen,
    source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen
  · change Src s c.input.base usedBytes (c.original.gpr .x2 + c.original.gpr .x4) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega)

end VG.Proof.Dsa.AArch64

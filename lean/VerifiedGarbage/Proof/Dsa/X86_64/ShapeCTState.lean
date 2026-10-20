module
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame

import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # Public state carried through DSA domain-shape validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ShapePublic where
  base : Addr
  extent : Nat
  pPointer : Addr
  qPointer : Addr
  pBytes : List Byte
  qBytes : List Byte
  digestLen : Nat
  extentBound : pWorkspace ≤ extent
  pPositive : 0 < pBytes.length
  qPositive : 0 < qBytes.length
  pBound : pBytes.length < 2 ^ 64
  qBound : qBytes.length < 2 ^ 64
  digestBound : digestLen < 2 ^ 64

structure ShapeContext (p : ShapePublic) (s : State) : Prop where
  scr : Scr s p.base p.extent
  rdi : s.gpr .rdi = p.base
  pPointer : word s.mem p.base Field.p.offset = p.pPointer
  qPointer : word s.mem p.base Field.q.offset = p.qPointer
  pLength : word s.mem p.base Field.pLen.offset = BitVec.ofNat 64 p.pBytes.length
  qLength : word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.qBytes.length
  digestLength : word s.mem p.base Field.digestLen.offset = BitVec.ofNat 64 p.digestLen
  pSource : Src s p.base p.extent p.pPointer p.pBytes
  qSource : Src s p.base p.extent p.qPointer p.qBytes

theorem ShapeContext.frame {p : ShapePublic} {s t : State} {rs : List Reg}
    (h : ShapeContext p s) (hf : Frm p.base shapeRanges s.mem t.mem)
    (hk : Keep rs s t) (hr : Reg.rdi ∉ rs) : ShapeContext p t := by
  exact ⟨h.scr.congr hk.2.2, (hk.gpr hr).trans h.rdi,
    (shape_field hf .p (by decide) (by decide)).trans h.pPointer,
    (shape_field hf .q (by decide) (by decide)).trans h.qPointer,
    (shape_field hf .pLen (by decide) (by decide)).trans h.pLength,
    (shape_field hf .qLen (by decide) (by decide)).trans h.qLength,
    (shape_field hf .digestLen (by decide) (by decide)).trans h.digestLength,
    shape_source hf hk (Nat.le_trans (by decide) p.extentBound) h.pSource,
    shape_source hf hk (Nat.le_trans (by decide) p.extentBound) h.qSource⟩

theorem ShapeContext.sameMem {p : ShapePublic} {s t : State} {rs : List Reg}
    (h : ShapeContext p s) (hm : t.mem = s.mem) (hk : Keep rs s t) (hr : Reg.rdi ∉ rs) : ShapeContext p t :=
  h.frame (by rw [hm]; exact Frm.refl _ _ _) hk hr

def ShapeScanned (bytes : ShapePublic → List Byte) (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ s.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant (bytes p)).1 ∧
    s.gpr .r9 = (VG.Proof.Dsa.significant (bytes p)).2.zeroExtend 64

theorem shapeScan_ct (fp fl : Field) (pointer : ShapePublic → Addr) (bytes : ShapePublic → List Byte)
    (hptr : ∀ p s, ShapeContext p s → word s.mem p.base fp.offset = pointer p)
    (hlen : ∀ p s, ShapeContext p s → word s.mem p.base fl.offset = BitVec.ofNat 64 (bytes p).length)
    (hsrc : ∀ p s, ShapeContext p s → Src s p.base p.extent (pointer p) (bytes p))
    (h1 : ∀ p, 0 < (bytes p).length) (h64 : ∀ p, (bytes p).length < 2 ^ 64)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))]) hint).isSome = true) :
    RelCT isa (Two ShapeContext)
      (.seq (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))]) Checks.significant)
      (Two (ShapeScanned bytes)) := by
  refine two_post (two_map (fun p : ShapePublic => (⟨p.base, p.extent, pointer p, bytes p⟩ : ScanPublic))
    (fun p s h => ⟨h.scr, h.rdi, p.extentBound, hptr p s h, hlen p s h, hsrc p s h, h1 p, h64 p⟩)
    (scanField_ct fp fl hT)) ?_
  intro p s h
  exact WP.mono (scanField_ok h.scr h.rdi p.extentBound fp fl (hptr p s h) (hlen p s h)
    (hsrc p s h) (h1 p) (h64 p)) fun t ⟨h8, h9, hm, hk⟩ =>
      ⟨h.sameMem hm hk (by decide), h8, h9⟩

end VG.Proof.Dsa.X86_64

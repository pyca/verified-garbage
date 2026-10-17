module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.SignatureTiming

/-! # Public output resources survive shape checking and dispatch -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure OutputCallReady (L : CallLayout) (out : BitVec 32) (s : State) : Prop where
  scr : Scr s L.base L.size
  pointer : pointerValue L.base s (.input .out) = out
  qLength : pointerValue L.base s (.input .qLen) = BitVec.ofNat 32 L.qLen
  fits : out.toNat + 2 * L.qLen ≤ 2 ^ 32
  write : ∀ e k, e + k ≤ 2 * L.qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 2 * L.qLen⟩

theorem OutputCallReady.keepShape {L : CallLayout} {out : BitVec 32} {s t : State} {regs : List Reg}
    (R : OutputCallReady L out s) (K : Keeps regs s t) (hd : .edi ∉ regs) (hsp : .esp ∉ regs)
    (O : Outs L.base shapeRanges s.mem t.mem) : OutputCallReady L out t :=
  ⟨R.scr.of_keeps K hd hsp, (shapeFrame_field O (by decide)).trans R.pointer,
    (shapeFrame_field O (by decide)).trans R.qLength, R.fits,
    by intro e k h; rw [K.2.2]; exact R.write e k h, R.apart⟩

theorem OutputCallReady.compare {L : CallLayout} {out : BitVec 32} {s t : State}
    (R : OutputCallReady L out s) (K : Keeps [.eax] s t) (O : t.mem = s.mem) : OutputCallReady L out t :=
  R.keepShape K (by decide) (by decide) (by rw [O]; exact Outs.refl _ _ _)

theorem OutputCallReady.signature {L : CallLayout} {out : BitVec 32} {digestLen : Nat} {s : State}
    (O : OutputCallReady L out s) (S : ShapedCall L digestLen s) : SignatureReady L out s :=
  ⟨S.ready.moduli, ⟨true, S.mask⟩, O.pointer, O.fits, O.write, O.apart⟩

theorem signingShape_compare (L : CallLayout) (digestLen : Nat) (out : BitVec 32) :
    CompareInvariant L.base L.size (fun s t =>
      (ShapedCall L digestLen s ∧ ShapedCall L digestLen t) ∧ OutputCallReady L out s ∧ OutputCallReady L out t) :=
  ⟨fun _ _ H => ⟨H.2.1.scr, H.2.2.scr⟩, fun _ _ _ _ H K1 K2 O1 O2 =>
    ⟨⟨H.1.1.compare K1 O1, H.1.2.compare K2 O2⟩, H.2.1.compare K1 O1, H.2.2.compare K2 O2⟩⟩

end VG.Proof.Dsa.X86

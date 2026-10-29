module

import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import Aesop.BuiltinRules

/-! # Passing DSA operands through the parent workspace's call header -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def pointerValue (mem : Mem) (B : Addr) : Pointer → Addr
  | .input f => word mem B f.offset
  | .local offset => off B offset
  | .signatureS => word mem B Field.signature.offset + word mem B Field.qLen.offset

def pointerFits : Pointer → Prop
  | .local offset => offset < 2 ^ 31
  | _ => True

theorem fieldAddress (B : Addr) (f : Field) : B + BitVec.ofInt 64 (f.offset : Int) = off B f.offset := by
  rw [BitVec.ofInt_natCast]

/-- Resolve caller buffers, computed scratch values and the second scalar. -/
theorem pointer_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (p : Pointer) (hp : pointerFits p) :
    WP isa (.block (Core.pointer p)) s fun t =>
      t.gpr .rax = pointerValue s.mem B p ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hl (f : Field) : InRegions (s.rd ++ s.wr) (off B f.offset) 8 :=
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = pointerValue s.mem B p ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  · cases p with
    | input f =>
      unfold Core.pointer pointerValue Core.field
      xrun [State.ea, hdi, fieldAddress, hl f]
    | «local» offset =>
      unfold Core.pointer pointerValue
      xrun [hdi, sx_ofNat hp]
    | signatureS =>
      unfold Core.pointer pointerValue Core.field
      xrun [State.ea, hdi, fieldAddress, hl Field.signature, hl Field.qLen]
  · cases p <;> rfl

/-- Passing an operand changes only its two call-header slots. The length
field remains readable after storing the pointer, since fields begin at 256. -/
theorem operand_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (a : Operand) (ha : pointerFits a.pointer)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) :
    WP isa (.block (Core.operand sp sl a)) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)).writeW
        (off B (8 * sl)) (word s.mem B a.length.offset) ∧ Keep [.rax] s t := by
  unfold Core.operand
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  have hsu := hs.congr hku.2.2
  have hdu := (hku.gpr (show Reg.rdi ∉ [Reg.rax] by decide)).trans hdi
  have hn := hs.nowrap
  have hbounds := VG.Proof.Dsa.field_bounds a.length
  have hpMin : 256 ≤ pWorkspace := by decide
  have hpMax : pWorkspace < 2 ^ 64 := by decide
  have hw : word (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)) B a.length.offset =
      word s.mem B a.length.offset := by
    rw [(writeW_outside u.mem B (pointerValue s.mem B a.pointer) (by omega)).word
      (Or.inr (by omega)) (by omega), hum]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)).writeW
      (off B (8 * sl)) (word s.mem B a.length.offset)) ?_ rfl)
    fun t ⟨htm, hkt⟩ => ⟨by rw [hum] at htm; exact htm, (hku.trans hkt).mono (by decide)⟩
  unfold Core.field
  xrun [State.ea, hdr, hdu, hdrOff, hua, fieldAddress, hw,
    hsu.st (show 8 * sp + 8 ≤ Z by omega),
    hsu.ld (show a.length.offset + 8 ≤ Z by omega),
    hsu.st (show 8 * sl + 8 ≤ Z by omega)]

end VG.Proof.Dsa.X86_64

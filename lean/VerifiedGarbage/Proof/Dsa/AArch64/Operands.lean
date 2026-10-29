module

import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract

/-! # Passing DSA operands through the parent workspace's call header -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def pointerValue (mem : Mem) (B : Addr) : Pointer → Addr
  | .input f => word mem B f.offset
  | .local offset => off B offset
  | .signatureS => word mem B Field.signature.offset + word mem B Field.qLen.offset

def pointerFits : Pointer → Prop
  | .local offset => offset < 2 ^ 16
  | _ => True

theorem fieldAddress (B : Addr) (f : Field) : B + BitVec.ofNat 64 f.offset = off B f.offset := by
  rfl

theorem field_enc (f : Field) : f.offset % 8 = 0 ∧ f.offset < 32768 := by
  cases f <;> decide

/-- Resolve caller buffers, computed scratch values and the second scalar. -/
theorem pointer_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (p : Pointer) (hp : pointerFits p) :
    WP isa (.block (Core.pointer p)) s fun t =>
      t.gpr .x3 = pointerValue s.mem B p ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hl (f : Field) : InRegions (s.rd ++ s.wr) (off B f.offset) 8 :=
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = pointerValue s.mem B p ∧ t.mem = s.mem) ?_ ?_ ?_ ?_)
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  · cases p with
    | input f =>
      unfold Core.pointer pointerValue Core.field
      brun [hdi, field_enc f, fieldAddress, hl f]
    | «local» offset =>
      change offset < 2 ^ 16 at hp
      unfold Core.pointer pointerValue
      brun [hdi]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    | signatureS =>
      unfold Core.pointer pointerValue Core.field
      brun [hdi, field_enc Field.signature, field_enc Field.qLen, fieldAddress, hl Field.signature, hl Field.qLen]
  all_goals cases p <;> rfl

/-- Passing an operand changes only its two call-header slots. The length
field remains readable after storing the pointer, since fields begin at 256. -/
theorem operand_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (a : Operand) (ha : pointerFits a.pointer)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) :
    WP isa (.block (Core.operand sp sl a)) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)).writeW
        (off B (8 * sl)) (word s.mem B a.length.offset) ∧ Keep [.x3, .x4] s t := by
  unfold Core.operand
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  have hsu := hs.congr hku.wr
  have hdu := (hku.gpr .x0 (show Reg.x0 ∉ [Reg.x3, Reg.x4] by decide)).trans hdi
  have hn := hs.nowrap
  have hbounds := VG.Proof.Dsa.field_bounds a.length
  have hpMin : 256 ≤ pWorkspace := by decide
  have hpMax : pWorkspace < 2 ^ 64 := by decide
  have hw : word (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)) B a.length.offset =
      word s.mem B a.length.offset := by
    rw [(writeW_outside u.mem B (pointerValue s.mem B a.pointer) (by omega)).word
      (Or.inr (by omega)) (by omega), hum]
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.mem = (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)).writeW
      (off B (8 * sl)) (word s.mem B a.length.offset)) ?_ rfl rfl rfl)
    fun t ⟨htm, hkt⟩ => ⟨by rw [hum] at htm; exact htm, (hku.trans hkt).mono (by decide)⟩
  unfold Core.field
  brun [field_enc a.length, hdu, hdr_enc hsp, hdr_enc hsl, hua, fieldAddress, hw,
    hsu.st (show 8 * sp + 8 ≤ Z by omega),
    hsu.ld (show a.length.offset + 8 ≤ Z by omega),
    hsu.st (show 8 * sl + 8 ≤ Z by omega)]

end VG.Proof.Dsa.AArch64

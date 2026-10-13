module

public import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

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

/-- A local offset is a 16-bit immediate (`movz`). -/
def pointerFits : Pointer → Prop
  | .local offset => offset < 2 ^ 16
  | _ => True

theorem field_enc (f : Field) : f.offset % 8 = 0 ∧ f.offset < 32768 := by cases f <;> decide

/-- Resolve caller buffers, computed scratch values and the second scalar. -/
theorem pointer_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (p : Pointer) (hp : pointerFits p) :
    WP isa (.block (Core.pointer p)) s fun t =>
      t.gpr .x3 = pointerValue s.mem B p ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hl (f : Field) : InRegions (s.rd ++ s.wr) (off B f.offset) 8 :=
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
    t.gpr .x3 = pointerValue s.mem B p ∧ t.mem = s.mem) ?_ (by cases p <;> rfl) (by cases p <;> rfl)
      (by cases p <;> rfl))
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  cases p with
  | input f =>
    unfold Core.pointer pointerValue Core.field
    brun [hdi, field_enc, hl f]
  | «local» offset =>
    unfold Core.pointer pointerValue
    brun [hdi]
    unfold pointerFits at hp
    unfold off
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  | signatureS =>
    unfold Core.pointer pointerValue Core.field
    brun [hdi, field_enc, hl Field.signature, hl Field.qLen]

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
  have hdu := (hku.gpr .x0 (by decide)).trans hdi
  have hn := hs.nowrap
  have hbounds := VG.Proof.Dsa.field_bounds a.length
  have hpMin : 256 ≤ pWorkspace := by decide
  have hpMax : pWorkspace < 2 ^ 64 := by decide
  have hw : word (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)) B a.length.offset =
      word s.mem B a.length.offset := by
    rw [(writeW_outside u.mem B (pointerValue s.mem B a.pointer) (by omega)).word
      (Or.inr (by omega)) (by omega), hum]
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = (u.mem.writeW (off B (8 * sp)) (pointerValue s.mem B a.pointer)).writeW
      (off B (8 * sl)) (word s.mem B a.length.offset)) ?_ rfl rfl rfl)
    fun t ⟨htm, hkt⟩ => ⟨by rw [hum] at htm; exact htm, (hku.trans hkt).mono (by decide)⟩
  unfold Core.field
  brun [hdu, hdr_enc hsp, hdr_enc hsl, field_enc, hua,
    hsu.st (show 8 * sp + 8 ≤ Z by omega),
    hsu.ld (show a.length.offset + 8 ≤ Z by omega),
    hsu.st (show 8 * sl + 8 ≤ Z by omega)]
  simp only [word, off] at hw ⊢
  rw [hw]

end VG.Proof.Dsa.AArch64

module
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract

/-! # Saving sign and verify arguments without changing stack inputs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev signFields := SignVerify.signFields
abbrev verifyFields := SignVerify.verifyFields

def signFieldMem (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) : Mem :=
  (((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) out).writeW (off B Field.p.offset) key).writeW
    (off B Field.pLen.offset) plen).writeW (off B Field.nonce.offset) nonce).writeW
    (off B Field.qLen.offset) qlen).writeW (off B Field.digest.offset) digest).writeW
    (off B Field.digestLen.offset) digestLen

def verifyFieldMem (mem : Mem) (B key plen qlen signature digest digestLen : Addr) : Mem :=
  (((((((mem.writeW (off B Field.out.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW (off B Field.p.offset) key).writeW (off B Field.pLen.offset) plen).writeW
    (off B Field.qLen.offset) qlen).writeW (off B Field.signature.offset) signature).writeW
    (off B Field.digest.offset) digest).writeW (off B Field.digestLen.offset) digestLen

theorem field_write_stack (mem : Mem) (B sp : Addr) (v : BitVec 64) (f : Field) {d Z : Nat}
    (hZ : pWorkspace ≤ Z) (hsep : ∀ i < 8, Z ≤ ofs B (off sp d + BitVec.ofNat 64 i)) :
    word (mem.writeW (off B f.offset) v) sp d = word mem sp d := by
  have hf := VG.Proof.Dsa.field_bounds f
  apply Mem.readW_congr
  intro i hi
  exact writeW_outside mem B v (Nat.le_trans hf.2 (by decide)) _ (Or.inr (Nat.le_trans (Nat.le_trans hf.2 hZ) (hsep i hi)))

theorem signFields_ok {s : State} {B sp digestLen : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hsp : s.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : InRegions (s.rd ++ s.wr) sp 8)
    (hsep : ∀ i < 8, Z ≤ ofs B (sp + BitVec.ofNat 64 i))
    (hdl : word s.mem sp 0 = digestLen) :
    WP isa (.block signFields) s fun t =>
      t.mem = signFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4)
        (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) digestLen ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hstack (mem : Mem) (v : BitVec 64) (f : Field) :=
    field_write_stack mem B sp v f (d := 0) hZ (by simpa only [off_zero] using hsep)
  simp only [word, off_zero] at hstack hdl
  unfold signFields SignVerify.signFields
  brun [exec_ldrSp_x', SignVerify.initial, h11, hsp, fieldAddress,
    field_enc .signature, field_enc .out, field_enc .p, field_enc .pLen,
    field_enc .nonce, field_enc .qLen, field_enc .digest, field_enc .digestLen,
    hw .signature, hw .out, hw .p, hw .pLen, hw .nonce, hw .qLen, hw .digest, hw .digestLen,
    hr, hstack, hdl]
  rfl

theorem verifyFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block verifyFields) s fun t =>
      t.mem = verifyFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3)
        (s.gpr .x4) (s.gpr .x6) (s.gpr .x7) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold verifyFields SignVerify.verifyFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .out, field_enc .nonce, field_enc .p, field_enc .pLen,
    field_enc .qLen, field_enc .signature, field_enc .digest, field_enc .digestLen,
    hw .out, hw .nonce, hw .p, hw .pLen, hw .qLen, hw .signature, hw .digest, hw .digestLen]
  rfl

end VG.Proof.Dsa.AArch64

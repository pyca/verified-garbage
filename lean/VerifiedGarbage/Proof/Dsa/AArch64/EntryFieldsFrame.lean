module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive

/-! ### `Dsa.AArch64.KeyPointers`, which this module and modules that import it used -/

section

/-! # Resolving the packed DSA key into component pointers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def keyPointerMem (mem : Mem) (B p pl ql : Addr) : Mem :=
  (((mem.writeW (off B Field.q.offset) (p + pl)).writeW (off B Field.g.offset) (p + pl + ql)).writeW
    (off B Field.y.offset) (p + pl + ql + pl)).writeW (off B Field.x.offset) (p + pl + ql + pl + pl)

theorem field_write_other (mem : Mem) (B : Addr) (v : BitVec 64) (f readField : Field) (hne : f ≠ readField) :
    word (mem.writeW (off B f.offset) v) B readField.offset = word mem B readField.offset := by
  apply (writeW_outside mem B v (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).word
  · cases f <;> cases readField <;> simp_all [Field.offset]
  · exact Nat.le_trans (VG.Proof.Dsa.field_bounds readField).2 (by decide)

theorem keyPointerMem_fields (mem : Mem) (B p pl ql : Addr) :
    word (keyPointerMem mem B p pl ql) B Field.q.offset = p + pl ∧
    word (keyPointerMem mem B p pl ql) B Field.g.offset = p + pl + ql ∧
    word (keyPointerMem mem B p pl ql) B Field.y.offset = p + pl + ql + pl ∧
    word (keyPointerMem mem B p pl ql) B Field.x.offset = p + pl + ql + pl + pl := by
  simp (disch := decide) only [keyPointerMem, field_write_other, word_writeW_self, and_self]

theorem keyPointerMem_frame (mem : Mem) (B p pl ql : Addr) :
    Outside B 264 32 mem (keyPointerMem mem B p pl ql) := by
  intro x hx
  unfold keyPointerMem
  rw [writeW_outside _ B _ (d := Field.x.offset) (by decide) x (by change ofs B x < 288 ∨ 296 ≤ ofs B x; omega_using [hx]),
    writeW_outside _ B _ (d := Field.y.offset) (by decide) x (by change ofs B x < 280 ∨ 288 ≤ ofs B x; omega_using [hx]),
    writeW_outside _ B _ (d := Field.g.offset) (by decide) x (by change ofs B x < 272 ∨ 280 ≤ ofs B x; omega_using [hx]),
    writeW_outside _ B _ (d := Field.q.offset) (by decide) x (by change ofs B x < 264 ∨ 272 ≤ ofs B x; omega_using [hx])]

theorem keyPointers_ok {s : State} {B p pl ql : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z)
    (hp : word s.mem B Field.p.offset = p) (hpl : word s.mem B Field.pLen.offset = pl)
    (hql : word s.mem B Field.qLen.offset = ql) :
    WP isa (.block SignVerify.keyPointers) s fun t =>
      t.mem = keyPointerMem s.mem B p pl ql ∧ t.gpr .x0 = B ∧ Keep [.x3, .x12, .x13, .x0] s t := by
  refine WP.mono (WP.keep [.x3, .x12, .x13, .x0] (Q := fun t =>
      t.mem = keyPointerMem s.mem B p pl ql ∧ t.gpr .x0 = B) ?_ rfl rfl rfl)
    fun t ⟨⟨hm, hd⟩, hk⟩ => ⟨hm, hd, hk⟩
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold SignVerify.keyPointers
  brun [field_enc .p, field_enc .pLen, field_enc .qLen, field_enc .q, field_enc .g, field_enc .y, field_enc .x, SignVerify.initial, h11, fieldAddress, hp, hpl, hql,
    hl .p, hl .pLen, hl .qLen, hw .q, hw .g, hw .y, hw .x,
    field_write_other _ _ _ .q .qLen (by decide),
    field_write_other _ _ _ .q .pLen (by decide),
    field_write_other _ _ _ .g .pLen (by decide),
    field_write_other _ _ _ .y .pLen (by decide)]
  rfl

end VG.Proof.Dsa.AArch64

end

end

/-! # Saved arguments and the memory footprint of DSA entry stores -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/EntryFields.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum

theorem field_write_frame (mem : Mem) (B : Addr) (v : BitVec 64) (f : Field) :
    Outside B 256 (pWorkspace - 256) mem (mem.writeW (off B f.offset) v) := by
  have hb := VG.Proof.Dsa.field_bounds f
  exact (writeW_outside mem B v (Nat.le_trans hb.2 (by decide))).mono hb.1 (by
    have : 256 ≤ pWorkspace := by decide
    omega_using [hb])

theorem signFieldMem_fields (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) :
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.out.offset = out ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.p.offset = key ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.pLen.offset = plen ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.nonce.offset = nonce ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.qLen.offset = qlen ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.digest.offset = digest ∧
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.digestLen.offset = digestLen := by
  simp (disch := decide) only [signFieldMem, field_write_other, word_writeW_self, and_self]

theorem verifyFieldMem_fields (mem : Mem) (B key plen qlen signature digest digestLen : Addr) :
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.p.offset = key ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.pLen.offset = plen ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.qLen.offset = qlen ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.signature.offset = signature ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.digest.offset = digest ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.digestLen.offset = digestLen := by
  simp (disch := decide) only [verifyFieldMem, field_write_other, word_writeW_self, and_self]

theorem signFieldMem_frame (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) :
    Outside B 256 (pWorkspace - 256) mem (signFieldMem mem B out key plen nonce qlen digest digestLen) := by
  intro x hx
  simp only [signFieldMem, field_write_frame _ B _ _ x hx]

theorem verifyFieldMem_frame (mem : Mem) (B key plen qlen signature digest digestLen : Addr) :
    Outside B 256 (pWorkspace - 256) mem (verifyFieldMem mem B key plen qlen signature digest digestLen) := by
  intro x hx
  simp only [verifyFieldMem, field_write_frame _ B _ _ x hx]

theorem signFieldMem_unused (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) :
    word (signFieldMem mem B out key plen nonce qlen digest digestLen) B Field.signature.offset = (0#64) := by
  simp (disch := decide) only [signFieldMem, field_write_other, word_writeW_self]

theorem verifyFieldMem_unused (mem : Mem) (B key plen qlen signature digest digestLen : Addr) :
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.out.offset = (0#64) ∧
    word (verifyFieldMem mem B key plen qlen signature digest digestLen) B Field.nonce.offset = (0#64) := by
  simp (disch := decide) only [verifyFieldMem, field_write_other, word_writeW_self, and_self]

end VG.Proof.Dsa.AArch64

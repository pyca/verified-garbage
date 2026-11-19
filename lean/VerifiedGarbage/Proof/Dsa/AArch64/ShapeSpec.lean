module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.Block
public import Aesop.BuiltinRules
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive

/-! ### `Dsa.AArch64.InitializedFields`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.EntryFieldsFrame`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.AArch64.VerifyEntry`, which this module and modules that import it used -/

section

/-! # Complete AAPCS64 entry for DSA verification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerifyEntryPost (original : State) (B digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  p : word t.mem B Field.p.offset = original.gpr .x0
  pLen : word t.mem B Field.pLen.offset = original.gpr .x2
  qLen : word t.mem B Field.qLen.offset = original.gpr .x3
  signature : word t.mem B Field.signature.offset = original.gpr .x4
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .x0 + original.gpr .x2
  g : word t.mem B Field.g.offset = original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  y : word t.mem B Field.y.offset = original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2
  x : word t.mem B Field.x.offset = original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  unused : word t.mem B Field.out.offset = 0 ∧ word t.mem B Field.nonce.offset = 0
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.x0, .x3, .x11, .x12, .x13] original t

theorem verifyEntry_ok {s0 : State} {B sp digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : InRegions (s0.rd ++ s0.wr) sp 8)
    (hd : s0.gpr .x6 = digest) (hdl : s0.gpr .x7 = digestLen) (hb : word s0.mem sp 0 = B) :
    WP isa (.block SignVerify.verifyEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  unfold SignVerify.verifyEntry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (entryScratch_ok 0 (by decide) hsp (by simpa only [Nat.mul_zero, off_zero] using hr) hb)
    fun s2 ⟨h11, hmem1, hk12⟩ => ?_
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s2.gpr reg = s0.gpr reg :=
    hk12.gpr reg (by simpa using hne)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok (hs.congr hk12.wr) h11 hZ) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x3 (by decide), hreg .x4 (by decide),
    hreg .x6 (by decide), hreg .x7 (by decide), hd, hdl] at hmem3
  have hfields := verifyFieldMem_fields s2.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) digest digestLen
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s2.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  refine WP.mono (keyPointers_ok (hs.congr hk123.wr) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · rw [← hmem1]
    exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64

end

end

/-! # Every saved argument has a defined value after the public shape check -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/SignEntry.lean`, which only this module imported.
section

/-! # Complete AAPCS64 entry for a DSA signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SignEntryPost (original : State) (B qlen digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  out : word t.mem B Field.out.offset = original.gpr .x0
  p : word t.mem B Field.p.offset = original.gpr .x2
  pLen : word t.mem B Field.pLen.offset = original.gpr .x4
  nonce : word t.mem B Field.nonce.offset = original.gpr .x5
  qLen : word t.mem B Field.qLen.offset = qlen
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .x2 + original.gpr .x4
  g : word t.mem B Field.g.offset = original.gpr .x2 + original.gpr .x4 + qlen
  y : word t.mem B Field.y.offset = original.gpr .x2 + original.gpr .x4 + qlen + original.gpr .x4
  x : word t.mem B Field.x.offset = original.gpr .x2 + original.gpr .x4 + qlen + original.gpr .x4 + original.gpr .x4
  unused : word t.mem B Field.signature.offset = 0
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.x0, .x3, .x11, .x12, .x13] original t

theorem signEntry_ok {s0 : State} {B sp qlen digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j < 2, InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ i < 8, Z ≤ ofs B (sp + BitVec.ofNat 64 i))
    (hq : s0.gpr .x6 = qlen) (hd : s0.gpr .x7 = digest)
    (hdl : word s0.mem sp 0 = digestLen) (hb : word s0.mem sp 8 = B) :
    WP isa (.block SignVerify.signEntry) s0 (SignEntryPost s0 B qlen digest digestLen) := by
  unfold SignVerify.signEntry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (entryScratch_ok 1 (by decide) hsp (hr 1 (by decide)) hb)
    fun s2 ⟨h11, hmem1, hk12⟩ => ?_
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s2.gpr reg = s0.gpr reg :=
    hk12.gpr reg (by simpa using hne)
  rw [WP.block_append_iff]
  refine WP.mono (signFields_ok (digestLen := digestLen) (hs.congr hk12.wr) h11 (hk12.sp.trans hsp) hZ
    (by rw [hk12.rd, hk12.wr]; simpa only [Nat.mul_zero, off_zero] using hr 0 (by decide)) hsep
    (by rw [hmem1]; exact hdl)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x4 (by decide), hreg .x5 (by decide),
    hreg .x6 (by decide), hreg .x7 (by decide), hq, hd] at hmem3
  have hfields := signFieldMem_fields s2.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x5) qlen digest digestLen
  rw [← hmem3] at hfields
  have hunused := signFieldMem_unused s2.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x5) qlen digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact signFieldMem_frame _ _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  refine WP.mono (keyPointers_ok (hs.congr hk123.wr) h113 hZ hfields.2.1 hfields.2.2.1 hfields.2.2.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .x2) (s0.gpr .x4) qlen
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .out (by decide)).trans hfields.1, (hsame .p (by decide)).trans hfields.2.1,
    (hsame .pLen (by decide)).trans hfields.2.2.1, (hsame .nonce (by decide)).trans hfields.2.2.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.2.2.1, (hsame .digest (by decide)).trans hfields.2.2.2.2.2.1,
    (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2.2, hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2,
    ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact (hsame .signature (by decide)).trans hunused
  · rw [← hmem1]
    exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def signFieldValues (original : State) (qlen digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .x2
  | .q => original.gpr .x2 + original.gpr .x4
  | .g => original.gpr .x2 + original.gpr .x4 + qlen
  | .y => original.gpr .x2 + original.gpr .x4 + qlen + original.gpr .x4
  | .x => original.gpr .x2 + original.gpr .x4 + qlen + original.gpr .x4 + original.gpr .x4
  | .signature => 0
  | .nonce => original.gpr .x5
  | .digest => digest
  | .out => original.gpr .x0
  | .pLen => original.gpr .x4
  | .qLen => qlen
  | .digestLen => digestLen
  | .digestPrefixLen => prefixLen
  | .mask => mask valid

def verifyFieldValues (original : State) (digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .x0
  | .q => original.gpr .x0 + original.gpr .x2
  | .g => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .y => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2
  | .x => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  | .signature => original.gpr .x4
  | .nonce => 0
  | .digest => digest
  | .out => 0
  | .pLen => original.gpr .x2
  | .qLen => original.gpr .x3
  | .digestLen => digestLen
  | .digestPrefixLen => prefixLen
  | .mask => mask valid

theorem SignEntryPost.shapeFields {original s t : State} {B qlen digest digestLen prefixLen : Addr} {valid : Bool}
    (h : SignEntryPost original B qlen digest digestLen s)
    (hf : Frm B shapeRanges s.mem t.mem)
    (hp : word t.mem B Field.digestPrefixLen.offset = prefixLen)
    (hm : word t.mem B Field.mask.offset = mask valid) :
    ∀ f, word t.mem B f.offset = signFieldValues original qlen digest digestLen prefixLen valid f := by
  intro f
  cases f
  case digestPrefixLen => exact hp
  case mask => exact hm
  case p =>
    exact (shape_field hf .p (by decide) (by decide)).trans h.p
  case q =>
    exact (shape_field hf .q (by decide) (by decide)).trans h.q
  case g =>
    exact (shape_field hf .g (by decide) (by decide)).trans h.g
  case y =>
    exact (shape_field hf .y (by decide) (by decide)).trans h.y
  case x =>
    exact (shape_field hf .x (by decide) (by decide)).trans h.x
  case signature =>
    exact (shape_field hf .signature (by decide) (by decide)).trans h.unused
  case nonce =>
    exact (shape_field hf .nonce (by decide) (by decide)).trans h.nonce
  case digest =>
    exact (shape_field hf .digest (by decide) (by decide)).trans h.digest
  case out =>
    exact (shape_field hf .out (by decide) (by decide)).trans h.out
  case pLen =>
    exact (shape_field hf .pLen (by decide) (by decide)).trans h.pLen
  case qLen =>
    exact (shape_field hf .qLen (by decide) (by decide)).trans h.qLen
  case digestLen =>
    exact (shape_field hf .digestLen (by decide) (by decide)).trans h.digestLen

theorem VerifyEntryPost.shapeFields {original s t : State} {B digest digestLen prefixLen : Addr} {valid : Bool}
    (h : VerifyEntryPost original B digest digestLen s)
    (hf : Frm B shapeRanges s.mem t.mem)
    (hp : word t.mem B Field.digestPrefixLen.offset = prefixLen)
    (hm : word t.mem B Field.mask.offset = mask valid) :
    ∀ f, word t.mem B f.offset = verifyFieldValues original digest digestLen prefixLen valid f := by
  intro f
  cases f
  case digestPrefixLen => exact hp
  case mask => exact hm
  case p =>
    exact (shape_field hf .p (by decide) (by decide)).trans h.p
  case q =>
    exact (shape_field hf .q (by decide) (by decide)).trans h.q
  case g =>
    exact (shape_field hf .g (by decide) (by decide)).trans h.g
  case y =>
    exact (shape_field hf .y (by decide) (by decide)).trans h.y
  case x =>
    exact (shape_field hf .x (by decide) (by decide)).trans h.x
  case signature =>
    exact (shape_field hf .signature (by decide) (by decide)).trans h.signature
  case nonce =>
    exact (shape_field hf .nonce (by decide) (by decide)).trans h.unused.2
  case digest =>
    exact (shape_field hf .digest (by decide) (by decide)).trans h.digest
  case out =>
    exact (shape_field hf .out (by decide) (by decide)).trans h.unused.1
  case pLen =>
    exact (shape_field hf .pLen (by decide) (by decide)).trans h.pLen
  case qLen =>
    exact (shape_field hf .qLen (by decide) (by decide)).trans h.qLen
  case digestLen =>
    exact (shape_field hf .digestLen (by decide) (by decide)).trans h.digestLen

end VG.Proof.Dsa.AArch64

end

end

/-! # Public shape acceptance and early rejection in the DSA specification -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/DomainShape.lean`, which only this module imported.
section

/-! # Functional correctness of the public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def shapeValid (p q : List Byte) (pLast qLast : Byte) : Bool :=
  decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) &&
    (decide (Spec.Dsa.supportedSizes (8 * (VG.Proof.Dsa.significant p).1)
      (8 * (VG.Proof.Dsa.significant q).1)) &&
      (decide (128 ≤ (VG.Proof.Dsa.significant q).2.toNat) &&
        decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat)))

theorem shapeValid_spec (p q : List Byte) (pLast qLast : Byte) :
    shapeValid p q pLast qLast = decide (
      Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
        (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) := by
  unfold shapeValid
  rw [← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_and]
  apply decide_eq_decide.mpr
  rw [VG.Proof.Dsa.supported_scans]
  constructor
  · rintro ⟨⟨hp, hq⟩, hs, htq, htp⟩
    exact ⟨⟨htp, htq, hs⟩, hp, hq⟩
  · rintro ⟨⟨htp, htq, hs⟩, hp, hq⟩
    exact ⟨⟨hp, hq⟩, hs, htq, htp⟩

theorem domainShape_ok {s : State} {B pp qp : Addr} {Z n : Nat} {p q : List Byte}
    {pLast qLast : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64)
    (hplast : p[p.length - 1] = pLast) (hqlast : q[q.length - 1] = qLast)
    (hn : n < 2 ^ 64) (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n) :
    WP isa Checks.domainShape s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n (VG.Proof.Dsa.significant q).1) ∧
      word t.mem B Field.mask.offset = mask (shapeValid p q pLast qLast) ∧
      (t.gpr .x3 == (0#64)) = !(shapeValid p q pLast qLast) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  have h : WP isa (.seq shapeSizes (.block shapeTail)) s (fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n (VG.Proof.Dsa.significant q).1) ∧
      word t.mem B Field.mask.offset = mask (shapeValid p q pLast qLast) ∧
      (t.gpr .x3 == (0#64)) = !(shapeValid p q pLast qLast) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t) := by
    refine WP.seq (WP.mono (shapeSizes_ok hs hdi hZ hpp hqp hpl hql hps hqs hp1 hp64 hq1 hq64)
      fun u ⟨hua, hum, huw, hfu, hku⟩ => ?_)
    have hudi := (hku.gpr .x0 (show Reg.x0 ∉ mmRegs by decide)).trans hdi
    refine WP.mono (shapeTail_ok (hs.congr hku.wr) hudi hZ
      ((shape_field hfu .p (by decide) (by decide)).trans hpp)
      ((shape_field hfu .q (by decide) (by decide)).trans hqp)
      ((shape_field hfu .pLen (by decide) (by decide)).trans hpl)
      ((shape_field hfu .qLen (by decide) (by decide)).trans hql)
      (shape_source hfu hku (Nat.le_trans (by decide) hZ) hps)
      (shape_source hfu hku (Nat.le_trans (by decide) hZ) hqs)
      hp1 hp64 hq1 hq64 hplast hqlast hn
      (Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits q) hq64)
      ((shape_field hfu .digestLen (by decide) (by decide)).trans hd) huw hua hum)
      fun t ⟨htw, htm, htz, hft, hkt⟩ => ?_
    exact ⟨htw, htm, htz, hfu.trans hft, (hku.trans hkt).mono (by decide)⟩
  exact h

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG

theorem decodeBE_last_parity (bs : List Byte) (hn : 0 < bs.length) :
    Spec.Dsa.decodeBE bs % 2 = (bs[bs.length - 1]'(by omega_using [hn])).toNat % 2 := by
  have hne : bs ≠ [] := by intro h; simp only [h, List.length_nil, Nat.lt_irrefl] at hn
  have he := VG.Proof.Dsa.decodeBE_last_mod_two bs.dropLast (bs.getLast hne)
  rw [List.dropLast_concat_getLast hne, List.getLast_eq_getElem] at he
  exact he

def shapeAccepted (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) : Bool :=
  shapeValid p q (p[p.length - 1]'(by omega_using [hp])) (q[q.length - 1]'(by omega_using [hq]))

theorem shapeAccepted_spec (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) :
    shapeAccepted p q hp hq = decide (
      Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
        (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) := by
  unfold shapeAccepted
  rw [shapeValid_spec, ← decodeBE_last_parity p hp, ← decodeBE_last_parity q hq]

theorem shapeAccepted_false {p q : List Byte} {hp : 0 < p.length} {hq : 0 < q.length}
    (h : shapeAccepted p q hp hq = false) (g : Nat) :
    ¬ Spec.Dsa.parametersValid ⟨Spec.Dsa.decodeBE p, Spec.Dsa.decodeBE q, g⟩ := by
  rw [shapeAccepted_spec] at h
  intro hv
  have ht : decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) = true :=
    decide_eq_true ⟨hv.1, hv.2.1, hv.2.2.1⟩
  rw [h] at ht
  cases ht

theorem signBytes_invalid_shape {pLen qLen : Nat} {key nonce digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes pLen qLen key).params) :
    Spec.Dsa.signBytes pLen qLen key nonce digest = none := by
  unfold Spec.Dsa.signBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]

theorem verifyBytes_invalid_shape {pLen qLen : Nat} {key signature digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes pLen qLen key).params) :
    Spec.Dsa.verifyBytes pLen qLen key signature digest = false := by
  unfold Spec.Dsa.verifyBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.false_and]

end VG.Proof.Dsa.AArch64

module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # AAPCS64 entry of the domain check and key derivation

Both entries save the callee-saved registers and fill every field but the
digest prefix and the mask, which the shape checks write. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem word_fieldWrite (mem : Mem) (B : Addr) (v : BitVec 64) (f r : Field) :
    word (mem.writeW (off B f.offset) v) B r.offset = if f = r then v else word mem B r.offset := by
  by_cases h : f = r
  · subst h
    simp [word_writeW_self]
  · simp only [h, ↓reduceIte]
    exact field_write_other _ _ _ _ _ h

/-- Fields captured by the caller-saved-register entry. -/
structure KeygenEntryPost (original : State) (B : Addr) (values : Field → Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  fields : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → word t.mem B f.offset = values f
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.x0, .x3, .x11, .x12, .x13] original t

def checkFieldValues (original : State) (valid : Bool) : Field → Addr
  | .p => original.gpr .x0
  | .q => original.gpr .x0 + original.gpr .x2
  | .g => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .y => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .x => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => 0
  | .pLen => original.gpr .x2
  | .qLen => original.gpr .x3
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

abbrev checkFields := Generate.checkFields

def checkFieldMem (mem : Mem) (B p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) (0#64)).writeW
    (off B Field.nonce.offset) (0#64)).writeW (off B Field.digest.offset) (0#64)).writeW
    (off B Field.digestLen.offset) (0#64)).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem checkFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block checkFields) s fun t =>
      t.mem = checkFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold checkFields Generate.checkFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .signature, field_enc .out, field_enc .nonce, field_enc .digest,
    field_enc .digestLen, field_enc .p, field_enc .pLen, field_enc .qLen,
    hw .signature, hw .out, hw .nonce, hw .digest, hw .digestLen, hw .p, hw .pLen, hw .qLen]
  rfl

/-- Point the public value at g. -/
theorem publicGenerator_ok {s : State} {B v : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z)
    (hg : word s.mem B Field.g.offset = v) :
    WP isa (.block [.ldr .x .x3 .x11 Field.g.offset, SignVerify.initial .x3 .y]) s fun t =>
      t.mem = s.mem.writeW (off B Field.y.offset) v ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .g, field_enc .y, hl .g, hw .y, hg]

theorem moveScratch_ok (s : State) :
    WP isa (.block [mov .x11 .x4]) s fun t =>
      t.gpr .x11 = s.gpr .x4 ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = s.gpr .x4 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  brun []

theorem checkEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h8 : s0.gpr .x4 = B) :
    WP isa (.block Generate.checkEntry) s0 (KeygenEntryPost s0 B (checkFieldValues s0 true)) := by
  unfold Generate.checkEntry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  refine WP.mono (checkFields_ok (hs.congr hk1.wr) h11 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x3 (by decide)] at hmem3
  have hk123 := hk1.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (checkFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x0) (pl := s0.gpr .x2) (ql := s0.gpr .x3) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  have hg4 : word s4.mem B Field.g.offset = s0.gpr .x0 + s0.gpr .x2 + s0.gpr .x3 := by
    rw [hmem4]; exact (keyPointerMem_fields _ _ _ _ _).2.1
  refine WP.mono (publicGenerator_ok (hs.congr hk1234.wr) h114 (by decide) hg4) fun t ⟨hmem5, hk5⟩ => ?_
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [checkFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, checkFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega
    rw [hmem5, hmem4, hmem3]
    simp only [checkFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

end VG.Proof.Dsa.AArch64

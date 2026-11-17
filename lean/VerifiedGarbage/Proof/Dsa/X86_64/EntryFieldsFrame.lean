module

public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push

/-! ### `Dsa.X86_64.KeyPointers`, which this module and modules that import it used -/

section

/-! # Resolving the packed DSA key into component pointers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z)
    (hp : word s.mem B Field.p.offset = p) (hpl : word s.mem B Field.pLen.offset = pl)
    (hql : word s.mem B Field.qLen.offset = ql) :
    WP isa (.block SignVerify.keyPointers) s fun t =>
      t.mem = keyPointerMem s.mem B p pl ql ∧ t.gpr .rdi = B ∧ Keep [.rax, .rdi] s t := by
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t =>
      t.mem = keyPointerMem s.mem B p pl ql ∧ t.gpr .rdi = B) ?_ rfl)
    fun t ⟨⟨hm, hd⟩, hk⟩ => ⟨hm, hd, hk⟩
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold SignVerify.keyPointers
  xrun [State.ea, SignVerify.initial, h11, fieldAddress, hp, hpl, hql,
    hl .p, hl .pLen, hl .qLen, hw .q, hw .g, hw .y, hw .x,
    field_write_other _ _ _ .q .qLen (by decide),
    field_write_other _ _ _ .q .pLen (by decide),
    field_write_other _ _ _ .g .pLen (by decide),
    field_write_other _ _ _ .y .pLen (by decide)]
  rfl

end VG.Proof.Dsa.X86_64

end

end

/-! # Saved arguments and the memory footprint of DSA entry stores -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout
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

end VG.Proof.Dsa.X86_64

module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push

/-! ### `Dsa.X86_64.EntryFieldsFrame`, which the modules that import this one used -/

section

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

end

end

/-! # Saving System V callee-saved registers in caller scratch -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def savedMem (s : State) (B : Addr) : Mem :=
  (((((s.mem.writeW (off B 0) (s.gpr .rbx)).writeW (off B 8) (s.gpr .rbp)).writeW
    (off B 16) (s.gpr .r12)).writeW (off B 24) (s.gpr .r13)).writeW
    (off B 32) (s.gpr .r14)).writeW (off B 40) (s.gpr .r15)

theorem savedMem_word (s : State) (B : Addr) (i : Nat) (hi : i < 6) :
    word (savedMem s B) B (8 * i) = s.gpr (saved.getD i .rax) := by
  have other (mem : Mem) (v : BitVec 64) (d e : Nat) (h : e + 8 ≤ d ∨ d + 8 ≤ e)
      (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      word (mem.writeW (off B d) v) B e = word mem B e :=
    (writeW_outside mem B v hd).word h he
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [savedMem, show 8 * 0 = 0 from rfl, show 8 * 1 = 8 from rfl,
      show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl, show 8 * 4 = 32 from rfl, show 8 * 5 = 40 from rfl]
    simp (disch := decide) only [other, word_writeW_self]
    rfl

theorem savedMem_frame (s : State) (B : Addr) : Outside B 0 48 s.mem (savedMem s B) := by
  intro x hx
  have h48 : 48 ≤ ofs B x := by omega_using [hx]
  unfold savedMem
  rw [writeW_outside _ B _ (d := 40) (by decide) x (Or.inr h48),
    writeW_outside _ B _ (d := 32) (by decide) x (Or.inr (by omega_using [hx])),
    writeW_outside _ B _ (d := 24) (by decide) x (Or.inr (by omega_using [hx])),
    writeW_outside _ B _ (d := 16) (by decide) x (Or.inr (by omega_using [hx])),
    writeW_outside _ B _ (d := 8) (by decide) x (Or.inr (by omega_using [hx])),
    writeW_outside _ B _ (d := 0) (by decide) x (Or.inr (by omega_using [hx]))]

theorem save_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : 48 ≤ Z) :
    WP isa (.block SignVerify.save) s fun t =>
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Outside B 0 48 s.mem t.mem ∧ Keep [] s t := by
  have he : SignVerify.save = [.store { base := .r11, disp := 0 } .rbx,
      .store { base := .r11, disp := 8 } .rbp, .store { base := .r11, disp := 16 } .r12,
      .store { base := .r11, disp := 24 } .r13, .store { base := .r11, disp := 32 } .r14,
      .store { base := .r11, disp := 40 } .r15] := rfl
  rw [he]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = savedMem s B) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨fun i hi => by rw [hm]; exact savedMem_word s B i hi,
      by rw [hm]; exact savedMem_frame s B, hk⟩
  have h0 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by omega_using [hZ])
  xrun [State.ea, h11, h0, show B + BitVec.ofInt 64 0 = off B 0 from rfl,
    show B + BitVec.ofInt 64 8 = off B 8 from rfl, show B + BitVec.ofInt 64 16 = off B 16 from rfl,
    show B + BitVec.ofInt 64 24 = off B 24 from rfl, show B + BitVec.ofInt 64 32 = off B 32 from rfl,
    show B + BitVec.ofInt 64 40 = off B 40 from rfl,
    hs.st (d := 0) (by omega_using [hZ]), hs.st (d := 8) (by omega_using [hZ]), hs.st (d := 16) (by omega_using [hZ]),
    hs.st (d := 24) (by omega_using [hZ]), hs.st (d := 32) (by omega_using [hZ]), hs.st (d := 40) hZ]
  simp only [savedMem, show off B 0 = B by simp [off]]

end VG.Proof.Dsa.X86_64

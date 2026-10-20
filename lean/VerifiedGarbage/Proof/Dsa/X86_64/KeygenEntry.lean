module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # System V entry of the domain check and key derivation

Both entries save the callee-saved registers and fill every field but the
digest prefix and the mask, which the shape checks write. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem word_fieldWrite (mem : Mem) (B : Addr) (v : BitVec 64) (f r : Field) :
    word (mem.writeW (off B f.offset) v) B r.offset = if f = r then v else word mem B r.offset := by
  by_cases h : f = r
  · subst h
    simp [word_writeW_self]
  · simp only [h, ↓reduceIte]
    exact field_write_other _ _ _ _ _ h

/-- The fields `values` holds, but for the shape checks' two, after an entry
that saves the callee-saved registers. -/
structure KeygenEntryPost (original : State) (B : Addr) (values : Field → Addr) (t : State) : Prop where
  base : t.gpr .rdi = B
  fields : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → word t.mem B f.offset = values f
  saved : ∀ i < 6, word t.mem B (8 * i) = original.gpr (saved.getD i .rax)
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.rax, .rdi, .r11] original t

/-- A field write of the entry stays in the fields' area. -/
theorem fieldWrite_frame (mem : Mem) (B : Addr) (v : BitVec 64) (f : Field) :
    Outside B 48 (pWorkspace - 48) mem (mem.writeW (off B f.offset) v) :=
  (field_write_frame mem B v f).mono (by decide) (by decide)

/-- After `save`, the fields of an entry: a block of field writes from
registers, whose final memory is `m`. -/
theorem keygenEntry_finish {original s t : State} {B : Addr} {values : Field → Addr}
    (hsaved : ∀ i < 6, word s.mem B (8 * i) = original.gpr (saved.getD i .rax))
    (hf0 : Outside B 0 48 original.mem s.mem)
    (hf : Outside B 48 (pWorkspace - 48) s.mem t.mem)
    (hfields : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → word t.mem B f.offset = values f)
    (hdi : t.gpr .rdi = B) (hk : Keep [.rax, .rdi, .r11] original t) :
    KeygenEntryPost original B values t := by
  refine ⟨hdi, hfields, fun i hi => (hf.word (Or.inl (by omega)) (by omega)).trans (hsaved i hi), ?_, hk⟩
  intro x hx
  have h : pWorkspace ≤ ofs B x := by omega
  exact (hf x (Or.inr (by change 48 + (3456 - 48) ≤ ofs B x at *; omega))).trans
    (hf0 x (Or.inr (by change 3456 ≤ ofs B x at h; omega)))

def checkFieldValues (original : State) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdi
  | .q => original.gpr .rdi + original.gpr .rdx
  | .g => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  | .y => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  | .x => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => 0
  | .pLen => original.gpr .rdx
  | .qLen => original.gpr .rcx
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

def checkFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .signature) .rax,
    .store (SignVerify.initial .out) .rax, .store (SignVerify.initial .nonce) .rax,
    .store (SignVerify.initial .digest) .rax, .store (SignVerify.initial .digestLen) .rax,
    .store (SignVerify.initial .p) .rdi, .store (SignVerify.initial .pLen) .rdx,
    .store (SignVerify.initial .qLen) .rcx]

def checkFieldMem (mem : Mem) (B p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) (0#64)).writeW
    (off B Field.nonce.offset) (0#64)).writeW (off B Field.digest.offset) (0#64)).writeW
    (off B Field.digestLen.offset) (0#64)).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem checkFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block checkFields) s fun t =>
      t.mem = checkFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold checkFields
  xrun [State.ea, SignVerify.initial, h11, fieldAddress,
    hw .signature, hw .out, hw .nonce, hw .digest, hw .digestLen, hw .p, hw .pLen, hw .qLen]
  rfl

/-- Point the public value at g. -/
theorem publicGenerator_ok {s : State} {B v : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z)
    (hg : word s.mem B Field.g.offset = v) :
    WP isa (.block [.mov .rax (.mem (SignVerify.initial .g)), .store (SignVerify.initial .y) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B Field.y.offset) v ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  xrun [State.ea, SignVerify.initial, h11, fieldAddress, hl .g, hw .y, hg]

theorem moveScratch_ok (s : State) :
    WP isa (.block [.mov .r11 (.reg .r8)]) s fun t =>
      t.gpr .r11 = s.gpr .r8 ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = s.gpr .r8 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  xrun []

theorem checkEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h8 : s0.gpr .r8 = B) :
    WP isa (.block Generate.checkEntry) s0 (KeygenEntryPost s0 B (checkFieldValues s0 true)) := by
  change WP isa (.block (([.mov .r11 (.reg .r8)] : List Instr) ++ SignVerify.save ++ checkFields ++
    SignVerify.keyPointers ++ [.mov .rax (.mem (SignVerify.initial .g)), .store (SignVerify.initial .y) .rax])) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (by decide)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have h112 : s2.gpr .r11 = B := (hk2.gpr (by decide)).trans h11
  rw [WP.block_append_iff]
  refine WP.mono (checkFields_ok (hs.congr hk12.2.2) h112 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide)] at hmem3
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans h112
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (checkFieldMem s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .rdi) (pl := s0.gpr .rdx) (ql := s0.gpr .rcx) (hs.congr hk123.2.2) h113 (by decide)
    ((hw3 .p).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .r11 = B := (hk4.gpr (by decide)).trans h113
  have hg4 : word s4.mem B Field.g.offset = s0.gpr .rdi + s0.gpr .rdx + s0.gpr .rcx := by
    rw [hmem4]; exact (keyPointerMem_fields _ _ _ _ _).2.1
  refine WP.mono (publicGenerator_ok (hs.congr hk1234.2.2) h114 (by decide) hg4) fun t ⟨hmem5, hk5⟩ => ?_
  refine keygenEntry_finish (s := s2)
    (fun i hi => (hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
    (by have := hf2; rwa [hmem1] at this) ?_ ?_ ((hk5.gpr (by decide)).trans hdi4)
    ((hk1234.trans hk5).mono (by decide))
  · intro x hx
    rw [hmem5, hmem4, hmem3]
    simp only [checkFieldMem, keyPointerMem, fieldWrite_frame _ B _ _ x hx]
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [checkFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, checkFieldValues]; try rfl)

def deriveFieldValues (original : State) (qlen B : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdx
  | .q => original.gpr .rdx + original.gpr .r8
  | .g => original.gpr .rdx + original.gpr .r8 + qlen
  | .y => B + BitVec.ofNat 64 derivedY
  | .x => original.gpr .r9
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => original.gpr .rdi
  | .pLen => original.gpr .r8
  | .qLen => qlen
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

def deriveFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .signature) .rax,
    .store (SignVerify.initial .nonce) .rax, .store (SignVerify.initial .digest) .rax,
    .store (SignVerify.initial .digestLen) .rax,
    .store (SignVerify.initial .out) .rdi, .store (SignVerify.initial .p) .rdx,
    .store (SignVerify.initial .pLen) .r8,
    .mov .rax (.mem (Crt.stk 1)), .store (SignVerify.initial .qLen) .rax]

def deriveFieldMem (mem : Mem) (B out p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW
    (off B Field.digest.offset) (0#64)).writeW (off B Field.digestLen.offset) (0#64)).writeW
    (off B Field.out.offset) out).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem deriveFields_ok {s : State} {B sp qlen : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hsp : s.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : InRegions (s.rd ++ s.wr) (off sp 8) 8)
    (hsep : ∀ i < 8, Z ≤ ofs B (off sp 8 + BitVec.ofNat 64 i)) (hq : word s.mem sp 8 = qlen) :
    WP isa (.block deriveFields) s fun t =>
      t.mem = deriveFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) qlen ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hstack (mem : Mem) (v : BitVec 64) (f : Field) := field_write_stack mem B sp v f hZ hsep
  unfold deriveFields
  rw [show Crt.stk 1 = ({ base := .rsp, disp := 8 } : MemOp) from rfl]
  xrun [State.ea, SignVerify.initial, h11, hsp, fieldAddress,
    show sp + BitVec.ofInt 64 8 = off sp 8 from rfl,
    hw .signature, hw .nonce, hw .digest, hw .digestLen, hw .out, hw .p, hw .pLen, hw .qLen,
    hr, hstack, hq]
  rfl

/-- Point x at the supplied scalar and y at the derived value's slot. -/
theorem deriveTail_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block [.store (SignVerify.initial .x) .r9, .mov .rax (.reg .r11),
      .alu .add .rax (.imm (BitVec.ofNat 32 derivedY)), .store (SignVerify.initial .y) .rax]) s fun t =>
      t.mem = (s.mem.writeW (off B Field.x.offset) (s.gpr .r9)).writeW (off B Field.y.offset)
        (B + BitVec.ofNat 64 derivedY) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  xrun [State.ea, SignVerify.initial, h11, fieldAddress, hw .x, hw .y]
  rfl

theorem deriveEntry_ok {s0 : State} {B sp qlen : Addr} (hs : Scr s0 B usedBytes) (hsp : s0.gpr .rsp = sp)
    (hr : ∀ j, 1 ≤ j → j ≤ 2 → InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 2 → ∀ i < 8, usedBytes ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hq : word s0.mem sp 8 = qlen) (hb : word s0.mem sp 16 = B) :
    WP isa (.block Generate.deriveEntry) s0 (KeygenEntryPost s0 B (deriveFieldValues s0 qlen B true)) := by
  change WP isa (.block (([.mov .r11 (.mem (Crt.stk 2))] : List Instr) ++ SignVerify.save ++ deriveFields ++
    SignVerify.keyPointers ++ [.store (SignVerify.initial .x) .r9, .mov .rax (.reg .r11),
      .alu .add .rax (.imm (BitVec.ofNat 32 derivedY)), .store (SignVerify.initial .y) .rax])) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok 2 hsp (hr 2 (by decide) (by decide)) hb) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (by decide)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have h112 : s2.gpr .r11 = B := (hk2.gpr (by decide)).trans h11
  have hq2 : word s2.mem sp 8 = qlen := by
    rw [entry_stack_frame hf2 (by decide) (hsep 1 (by decide) (by decide)), hmem1]; exact hq
  rw [WP.block_append_iff]
  refine WP.mono (deriveFields_ok (hs.congr hk12.2.2) h112 ((hreg .rsp (by decide)).trans hsp) (by decide)
    (by rw [hk12.2.1, hk12.2.2]; exact hr 1 (by decide) (by decide)) (hsep 1 (by decide) (by decide)) hq2)
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .r8 (by decide)] at hmem3
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans h112
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (deriveFieldMem s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .r8) qlen) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .rdx) (pl := s0.gpr .r8) (ql := qlen) (hs.congr hk123.2.2) h113 (by decide)
    ((hw3 .p).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .r11 = B := (hk4.gpr (by decide)).trans h113
  have h94 : s4.gpr .r9 = s0.gpr .r9 := hk1234.gpr (by decide)
  refine WP.mono (deriveTail_ok (hs.congr hk1234.2.2) h114 (by decide)) fun t ⟨hmem5, hk5⟩ => ?_
  rw [h94] at hmem5
  refine keygenEntry_finish (s := s2)
    (fun i hi => (hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
    (by have := hf2; rwa [hmem1] at this) ?_ ?_ ((hk5.gpr (by decide)).trans hdi4)
    ((hk1234.trans hk5).mono (by decide))
  · intro x hx
    rw [hmem5, hmem4, hmem3]
    simp only [deriveFieldMem, keyPointerMem, fieldWrite_frame _ B _ _ x hx]
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [deriveFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, deriveFieldValues]; try rfl)

end VG.Proof.Dsa.X86_64

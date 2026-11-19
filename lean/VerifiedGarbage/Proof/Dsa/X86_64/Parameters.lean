module

public import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive

/-! ### `Dsa.X86_64.VerifyFailure`, which this module and modules that import it used -/

section

/-! # Early verification failure restores System V registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyFailure_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) s fun t =>
      t.gpr .rax = 0 ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hs.ld (Nat.le_trans (show 8 * i + 8 ≤ pWorkspace by change 8 * i + 8 ≤ 3456; omega_using [hi]) hZ)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
    t.gpr .rax = 0 ∧
    t.gpr .rbx = word s.mem B 0 ∧ t.gpr .rbp = word s.mem B 8 ∧
    t.gpr .r12 = word s.mem B 16 ∧ t.gpr .r13 = word s.mem B 24 ∧
    t.gpr .r14 = word s.mem B 32 ∧ t.gpr .r15 = word s.mem B 40 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, h0, h1, h2, h3, h4, h5, hmem⟩, hk⟩ => ?_
  · simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, Core.field, fieldAddress,
     
      hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide), hl 5 (by decide)]
  · refine ⟨ht, ?_, hmem, hk⟩
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.KeygenEntry`, which this module and modules that import it used -/

section

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
  refine ⟨hdi, hfields, fun i hi => (hf.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hsaved i hi), ?_, hk⟩
  intro x hx
  have h : pWorkspace ≤ ofs B x := by omega_using [hx]
  exact (hf x (Or.inr (by change 48 + (3456 - 48) ≤ ofs B x at *; omega_using [h]))).trans
    (hf0 x (Or.inr (by change 3456 ≤ ofs B x at h; omega_using [h])))

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

end

end

/-! # Functional correctness of the x86-64 DSA domain check

The domain check is the signer's checks of a key whose public value is g:
the entry points y at g. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The fields after the shape checks, from an entry's: the shape checks
write the digest prefix and the mask, and keep the rest. -/
theorem KeygenEntryPost.shapeFields {original s t : State} {B : Addr} {values final : Field → Addr}
    (h : KeygenEntryPost original B values s) (hf : Frm B shapeRanges s.mem t.mem)
    (hv : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → values f = final f)
    (hp : word t.mem B Field.digestPrefixLen.offset = final .digestPrefixLen)
    (hm : word t.mem B Field.mask.offset = final .mask) :
    ∀ f, word t.mem B f.offset = final f := by
  intro f
  by_cases h1 : f = .digestPrefixLen
  · subst h1; exact hp
  by_cases h2 : f = .mask
  · subst h2; exact hm
  exact ((shape_field hf f h1 h2).trans (h.fields f h1 h2)).trans (hv f h1 h2)

structure ParametersInput where
  base : Addr
  pLen : Nat
  qLen : Nat
  params : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  paramsLength : params.length = 2 * pLen + qLen

namespace ParametersInput

variable (p : ParametersInput)

abbrev pb : List Byte := p.params.take p.pLen
abbrev qb : List Byte := (p.params.drop p.pLen).take p.qLen
abbrev gb : List Byte := (p.params.drop (p.pLen + p.qLen)).take p.pLen

theorem pbLength : p.pb.length = p.pLen := by
  simp only [List.length_take, p.paramsLength]; omega_using []
theorem qbLength : p.qb.length = p.qLen := component_length (by rw [p.paramsLength]; omega_using [])
theorem gbLength : p.gb.length = p.pLen := component_length (by rw [p.paramsLength]; omega_using [])

theorem pPositive : 0 < p.pb.length := by
  rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
theorem qPositive : 0 < p.qb.length := by
  rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]

abbrev accepted : Bool := shapeAccepted p.pb p.qb p.pPositive p.qPositive

theorem shapeFacts {p : ParametersInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.pb))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.qb)) ∧
    Spec.Dsa.decodeBE p.pb % 2 = 1 ∧ Spec.Dsa.decodeBE p.qb % 2 = 1 := by
  rw [ParametersInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def layout (original : State) (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.pb
  subgroup := Spec.Dsa.decodeBE p.qb
  pInverse := 0
  qInverse := 0
  fields := checkFieldValues original p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := hq

end ParametersInput

structure ParametersPre (p : ParametersInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  base : s.gpr .r8 = p.base
  pLength : s.gpr .rdx = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .rcx = BitVec.ofNat 64 p.qLen
  paramsSource : Src s p.base usedBytes (s.gpr .rdi) p.params

theorem ParametersPre.sources {p : ParametersInput} {original s : State} (h : ParametersPre p original)
    (hm : InScr p.base usedBytes original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base usedBytes (original.gpr .rdi) p.pb ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx) p.qb ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx + original.gpr .rcx) p.gb := by
  have hsrc := h.paramsSource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_using [])
  · rw [h.pLength, h.qLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_using [])

structure ParametersShapePost (p : ParametersInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem parametersShape_ok {p : ParametersInput} {s0 : State} (h : ParametersPre p s0) :
    WP isa (.seq (.block Generate.checkEntry) Checks.domainShape) s0
      (ParametersShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (checkEntry_ok h.scratch h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := h.sources hinside (he.keep.mono (by decide))
  have hp64 : p.pb.length < 2 ^ 64 := by
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (n := 0) (h.scratch.congr he.keep.2.2) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.pbLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.qbLength]; exact h.qLength))
    hps hqs p.pPositive hp64 p.qPositive hq64 rfl rfl (by decide)
    (he.fields .digestLen (by decide) (by decide))) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

def ParametersPost (p : ParametersInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem ParametersInput.check_eq (p : ParametersInput) :
    Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params =
      (p.accepted && (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb)
          (Spec.Dsa.decodeBE p.pb) = 1) &&
        (decide ((Spec.Dsa.decodeBE p.pb - 1) % Spec.Dsa.decodeBE p.qb = 0) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) && true))))) := by
  rw [VG.Proof.Dsa.checkParametersBytes_eq p.lengths p.paramsLength, ParametersInput.accepted,
    shapeAccepted_spec]
  rfl

theorem toNat_ofNat_if (b : Bool) :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (if b = true then 1 else 0) := by
  cases b <;> rfl

theorem parametersRejected_ok {p : ParametersInput} {original s : State} (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ VG.Impl.Bignum.X86_64.Public.exit)) s
      (ParametersPost p original) := by
  refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
    fun t ⟨hret, hsave, hmem, hk⟩ => ?_
  unfold ParametersPost
  rw [p.check_eq, ha, Bool.false_and]
  exact ⟨hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

/-- After the workspaces: the domain's operands, with the public value g. -/
structure ParametersOperands (L : ExecutionLayout) (p : ParametersInput) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator p.gb
  publicValue : OperandBytes s L.base usedBytes Core.publicValue p.gb
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ p.qb

def ParametersInitialized (p : ParametersInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    ParametersOperands ((p.layout original hp hq).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem parametersInitialize_ok {p : ParametersInput} {original st : State} (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (ParametersInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.rdi hs.fields hps hqs
    p.pbLength p.qbLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  have hframe : InScr p.base usedBytes original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  have hkeep := hs.keep.trans hk
  obtain ⟨_, hqs', hgs'⟩ := h.sources hframe (hkeep.mono (by decide))
  have hpl : L'.fields .pLen = BitVec.ofNat 64 p.gb.length := by
    rw [p.gbLength]; exact h.pLength
  refine ⟨pi, qi, hr', ⟨hr'.inputOperand .g .pLen (by decide) (by decide) hgs' hpl,
    hr'.inputOperand .y .pLen (by decide) (by decide) hgs' hpl,
    hr'.inputOperand .q .qLen (by decide) (by decide) hqs' (by rw [p.qbLength]; exact h.qLength)⟩,
    hm.trans ((hs.fields .mask).trans (congrArg mask ha)),
    fun i hi => (hf.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hs.saved i hi),
    hframe, hkeep.mono (by decide)⟩

/-- The signer's checks of the domain, with g as the public value. -/
theorem parametersBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {p : ParametersInput} {s : State}
    (hr : Ready L s) (ho : ParametersOperands L p s)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hgl : p.gb.length = L.pLen) (hql : p.qb.length = L.qLen) (hqv : Spec.Dsa.decodeBE p.qb = L.subgroup)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    WP isa (.seq (Checks.signingKey Sq.mm M.mm) (.block SignVerify.result)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (signingKeyAccepted L p.gb p.gb true).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (signingKey_ok M Sq hr hp hq hpo hqo hpf hqf ho.generator ho.publicValue
    ho.subgroup hgl hgl hql hqv hm) fun u ⟨hu, hmu, _, hfu, hku⟩ => ?_)
  refine WP.mono (result_ok hu.scratch hu.parent.rdi (by decide) hmu) fun v ⟨hret, hsave, hmem, hkv⟩ => ?_
  exact ⟨hret, fun i hi => (hsave i hi).trans (hfu.word (Or.inl (by omega_using [hi])) (by omega_using [hi])),
    by rw [hmem]; exact hfu, (hku.trans hkv).mono (by decide)⟩

theorem parametersSuccess_ok (M : Mont) (Sq : MontS) {p : ParametersInput} {original st : State}
    (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, .block SignVerify.result]) st
      (ParametersPost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  refine WP.seq (WP.mono (parametersInitialize_ok h hs ha) fun t ⟨pi, qi, hr, ho, hm, hsv, hframe, hkeep⟩ => ?_)
  have hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (parametersBody_ok M Sq hr ho hp1 hq255 hpo hqo hpf hqf p.gbLength p.qbLength rfl hm)
    fun v ⟨hret, hsave, hfu, hkv⟩ => ?_
  refine ⟨?_, fun i hi => (hsave i hi).trans (hsv i hi),
    hframe.trans (InScr.of_outside hfu (by decide)), (hkeep.trans hkv).mono (by decide)⟩
  rw [hret, p.check_eq, ha, Bool.true_and]
  exact toNat_ofNat_if _

theorem parametersMain_ok (M : Mont) (Sq : MontS) {p : ParametersInput} {s0 : State} (h : ParametersPre p s0) :
    WP isa (Generate.checkParameters Sq.mm M.mm) s0 (ParametersPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (parametersShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => parametersRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => parametersSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

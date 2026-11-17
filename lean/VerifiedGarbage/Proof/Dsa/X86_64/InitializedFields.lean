module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame

/-! ### `Dsa.X86_64.VerifyEntry`, which this module and modules that import it used -/

section

/-! # Complete System V entry for DSA verification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerifyEntryPost (original : State) (B digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .rdi = B
  p : word t.mem B Field.p.offset = original.gpr .rdi
  pLen : word t.mem B Field.pLen.offset = original.gpr .rdx
  qLen : word t.mem B Field.qLen.offset = original.gpr .rcx
  signature : word t.mem B Field.signature.offset = original.gpr .r8
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .rdi + original.gpr .rdx
  g : word t.mem B Field.g.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  y : word t.mem B Field.y.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx
  x : word t.mem B Field.x.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  unused : word t.mem B Field.out.offset = 0 ∧ word t.mem B Field.nonce.offset = 0
  saved : ∀ i < 6, word t.mem B (8 * i) = original.gpr (saved.getD i .rax)
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.rax, .rdi, .r11] original t

theorem verifyEntry_ok {s0 : State} {B sp digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 3 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hd : word s0.mem sp 8 = digest) (hdl : word s0.mem sp 16 = digestLen) (hb : word s0.mem sp 24 = B) :
    WP isa (.block SignVerify.verifyEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  change WP isa (.block (([.mov .r11 (.mem (Crt.stk 3))] : List Instr) ++ SignVerify.save ++ verifyFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok 3 hsp (hr 3 (by decide) (by decide)) hb) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have hr2 : ∀ j, 1 ≤ j → j ≤ 2 → InRegions (s2.rd ++ s2.wr) (off sp (8 * j)) 8 := by
    intro j hj1 hj2
    rw [hk12.2.1, hk12.2.2]
    exact hr j hj1 (by omega_using [hj2])
  have hstack (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) : word s2.mem sp (8 * j) = word s0.mem sp (8 * j) := by
    rw [entry_stack_frame hf2 (Nat.le_trans (by decide) hZ) (hsep j hj1 (by omega_using [hj2])), hmem1]
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11)
    ((hreg .rsp (by decide)).trans hsp) hZ hr2 (fun j h1 h2 => hsep j h1 (by omega_using [h2]))
    ((hstack 1 (by decide) (by decide)).trans hd) ((hstack 2 (by decide) (by decide)).trans hdl))
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide), hreg .r8 (by decide)] at hmem3
  have hfields := verifyFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) digest digestLen
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · intro i hi
    exact ((hf4.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SignEntry`, which only this module used -/

section

/-! # Complete System V entry for a DSA signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SignEntryPost (original : State) (B qlen digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .rdi = B
  out : word t.mem B Field.out.offset = original.gpr .rdi
  p : word t.mem B Field.p.offset = original.gpr .rdx
  pLen : word t.mem B Field.pLen.offset = original.gpr .r8
  nonce : word t.mem B Field.nonce.offset = original.gpr .r9
  qLen : word t.mem B Field.qLen.offset = qlen
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .rdx + original.gpr .r8
  g : word t.mem B Field.g.offset = original.gpr .rdx + original.gpr .r8 + qlen
  y : word t.mem B Field.y.offset = original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8
  x : word t.mem B Field.x.offset = original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8 + original.gpr .r8
  unused : word t.mem B Field.signature.offset = 0
  saved : ∀ i < 6, word t.mem B (8 * i) = original.gpr (saved.getD i .rax)
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.rax, .rdi, .r11] original t

theorem signEntry_ok {s0 : State} {B sp qlen digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 4 → InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 4 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hq : word s0.mem sp 8 = qlen) (hd : word s0.mem sp 16 = digest)
    (hdl : word s0.mem sp 24 = digestLen) (hb : word s0.mem sp 32 = B) :
    WP isa (.block SignVerify.signEntry) s0 (SignEntryPost s0 B qlen digest digestLen) := by
  change WP isa (.block (([.mov .r11 (.mem (Crt.stk 4))] : List Instr) ++ SignVerify.save ++ signFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok 4 hsp (hr 4 (by decide) (by decide)) hb) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have hr2 : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s2.rd ++ s2.wr) (off sp (8 * j)) 8 := by
    intro j hj1 hj3
    rw [hk12.2.1, hk12.2.2]
    exact hr j hj1 (by omega_using [hj3])
  have hstack (j : Nat) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) : word s2.mem sp (8 * j) = word s0.mem sp (8 * j) := by
    rw [entry_stack_frame hf2 (Nat.le_trans (by decide) hZ) (hsep j hj1 (by omega_using [hj3])), hmem1]
  rw [WP.block_append_iff]
  refine WP.mono (signFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11)
    ((hreg .rsp (by decide)).trans hsp) hZ hr2 (fun j h1 h3 => hsep j h1 (by omega_using [h3]))
    ((hstack 1 (by decide) (by decide)).trans hq) ((hstack 2 (by decide) (by decide)).trans hd)
    ((hstack 3 (by decide) (by decide)).trans hdl)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .r8 (by decide), hreg .r9 (by decide)] at hmem3
  have hfields := signFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .r8) (s0.gpr .r9) qlen digest digestLen
  rw [← hmem3] at hfields
  have hunused := signFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .r8) (s0.gpr .r9) qlen digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact signFieldMem_frame _ _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.2.1 hfields.2.2.1 hfields.2.2.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdx) (s0.gpr .r8) qlen
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .out (by decide)).trans hfields.1, (hsame .p (by decide)).trans hfields.2.1,
    (hsame .pLen (by decide)).trans hfields.2.2.1, (hsame .nonce (by decide)).trans hfields.2.2.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.2.2.1, (hsame .digest (by decide)).trans hfields.2.2.2.2.2.1,
    (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2.2, hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2,
    ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact (hsame .signature (by decide)).trans hunused
  · intro i hi
    exact ((hf4.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end


/-! # Every saved argument has a defined value after the public shape check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

def signFieldValues (original : State) (qlen digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdx
  | .q => original.gpr .rdx + original.gpr .r8
  | .g => original.gpr .rdx + original.gpr .r8 + qlen
  | .y => original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8
  | .x => original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8 + original.gpr .r8
  | .signature => 0
  | .nonce => original.gpr .r9
  | .digest => digest
  | .out => original.gpr .rdi
  | .pLen => original.gpr .r8
  | .qLen => qlen
  | .digestLen => digestLen
  | .digestPrefixLen => prefixLen
  | .mask => mask valid

def verifyFieldValues (original : State) (digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdi
  | .q => original.gpr .rdi + original.gpr .rdx
  | .g => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  | .y => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx
  | .x => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  | .signature => original.gpr .r8
  | .nonce => 0
  | .digest => digest
  | .out => 0
  | .pLen => original.gpr .rdx
  | .qLen => original.gpr .rcx
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

end VG.Proof.Dsa.X86_64

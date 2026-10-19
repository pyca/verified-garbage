module
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Save

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
    exact hr j hj1 (by omega)
  have hstack (j : Nat) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) : word s2.mem sp (8 * j) = word s0.mem sp (8 * j) := by
    rw [entry_stack_frame hf2 (Nat.le_trans (by decide) hZ) (hsep j hj1 (by omega)), hmem1]
  rw [WP.block_append_iff]
  refine WP.mono (signFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11)
    ((hreg .rsp (by decide)).trans hsp) hZ hr2 (fun j h1 h3 => hsep j h1 (by omega))
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
    exact ((hf4.word (Or.inl (by omega)) (by omega)).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64

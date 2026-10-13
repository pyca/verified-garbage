module

public import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

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
  keep : Keep [.x0, .x3, .x4, .x5, .x8, .x9] original t

/-- AAPCS64 entry: `digest` and `digest_len` arrive in `x6` and `x7`, `scratch`
in the first stack slot. -/
theorem verifyEntry_ok {s0 : State} {B sp digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : InRegions (s0.rd ++ s0.wr) (off sp 0) 8)
    (hd : s0.gpr .x6 = digest) (hdl : s0.gpr .x7 = digestLen) (hb : word s0.mem sp 0 = B) :
    WP isa (.block SignVerify.verifyEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  change WP isa (.block (([.ldrSp .x8 0] : List Instr) ++ verifyFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok (by decide) hsp hr hb) fun s1 ⟨h8, hmem1, hk1⟩ => ?_
  have hreg (reg : Reg) (hne : reg ≠ .x8) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok (hs.congr hk1.wr) h8 hZ) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x3 (by decide), hreg .x4 (by decide),
    hreg .x6 (by decide), hreg .x7 (by decide), hd, hdl, hmem1] at hmem3
  have hfields := verifyFieldMem_fields s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) digest digestLen
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s0.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk13 := hk1.trans hk3
  have h83 : s3.gpr .x8 = B := (hk3.gpr .x8 (by decide)).trans h8
  refine WP.mono (keyPointers_ok (hs.congr hk13.wr) h83 hZ hfields.1 hfields.2.1 hfields.2.2.1)
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
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2,
    ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩, ?_,
    (hk13.trans hk4).mono (by decide)⟩
  exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64

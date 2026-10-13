module

public import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

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
  keep : Keep [.x0, .x3, .x4, .x5, .x8, .x9] original t

/-- AAPCS64 entry: `q_len` and `digest` arrive in `x6` and `x7`, `digest_len`
and `scratch` in the first two stack slots. -/
theorem signEntry_ok {s0 : State} {B sp qlen digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.sp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j < 2, InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ i < 8, Z ≤ ofs B (off sp 0 + BitVec.ofNat 64 i))
    (hq : s0.gpr .x6 = qlen) (hd : s0.gpr .x7 = digest)
    (hdl : word s0.mem sp 0 = digestLen) (hb : word s0.mem sp 8 = B) :
    WP isa (.block SignVerify.signEntry) s0 (SignEntryPost s0 B qlen digest digestLen) := by
  change WP isa (.block (([.ldrSp .x8 8] : List Instr) ++ signFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hr8 : InRegions (s0.rd ++ s0.wr) (off sp 8) 8 := hr 1 (by decide)
  refine WP.mono (entryScratch_ok (by decide) hsp hr8 hb) fun s1 ⟨h8, hmem1, hk1⟩ => ?_
  have hreg (reg : Reg) (hne : reg ≠ .x8) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  have hr1 : InRegions (s1.rd ++ s1.wr) (off sp 0) 8 := by rw [hk1.rd, hk1.wr]; exact hr 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (signFields_ok (hs.congr hk1.wr) h8 (hk1.sp.trans hsp) hZ hr1 hsep (hmem1 ▸ hdl))
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x4 (by decide), hreg .x5 (by decide),
    hreg .x6 (by decide), hreg .x7 (by decide), hq, hd, hmem1] at hmem3
  have hfields := signFieldMem_fields s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x5) qlen digest digestLen
  rw [← hmem3] at hfields
  have hunused := signFieldMem_unused s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x5) qlen digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s0.mem s3.mem := by rw [hmem3]; exact signFieldMem_frame _ _ _ _ _ _ _ _ _
  have hk13 := hk1.trans hk3
  have h83 : s3.gpr .x8 = B := (hk3.gpr .x8 (by decide)).trans h8
  refine WP.mono (keyPointers_ok (hs.congr hk13.wr) h83 hZ hfields.2.1 hfields.2.2.1 hfields.2.2.2.2.1)
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
    (hsame .signature (by decide)).trans hunused, ?_, (hk13.trans hk4).mono (by decide)⟩
  exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64

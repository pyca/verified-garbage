module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Framework.Block
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

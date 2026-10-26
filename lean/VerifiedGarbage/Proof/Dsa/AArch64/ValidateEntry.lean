module

import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyEntry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete AAPCS64 entry for DSA verification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyCapture_ok {s0 : State} {B : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h11 : s0.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block (SignVerify.verifyFields ++ SignVerify.keyPointers)) s0
      (VerifyEntryPost s0 B (s0.gpr .x6) (s0.gpr .x7)) := by
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok hs h11 hZ) fun s3 ⟨hmem3, hk3⟩ => ?_

  have hfields := verifyFieldMem_fields s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) (s0.gpr .x6) (s0.gpr .x7)
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) (s0.gpr .x6) (s0.gpr .x7)
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s0.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  refine WP.mono (keyPointers_ok (hs.congr hk123.wr) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
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
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

structure ValidateEntryPost (original : State) (B : Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  fields : ∀ f, f ≠ .mask → f ≠ .digestPrefixLen →
    word t.mem B f.offset = verifyFieldValues original 0 0 0 true f
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep coreRegs original t

theorem validateEntry_ok {s0 : State} {B : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h4 : s0.gpr .x4 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block Prevalidated.validateEntry) s0 (ValidateEntryPost s0 B) := by
  unfold Prevalidated.validateEntry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x11, .x6, .x7]
    (Q := fun s => s.gpr .x11 = B ∧ s.gpr .x6 = 0 ∧ s.gpr .x7 = 0 ∧ s.mem = s0.mem)
    (by brun [h4]) rfl rfl rfl) fun s1 ⟨⟨h11, h6, h7, hmem⟩, hk⟩ => ?_
  refine WP.mono (verifyCapture_ok (hs.congr hk.wr) h11 hZ) fun t ht => ?_
  have he (r : Reg) (hr : r ∉ [.x11, .x6, .x7]) := hk.gpr r hr
  refine ⟨ht.base, ?_, ?_, (hk.trans ht.keep).mono (by decide)⟩
  · intro f hm hp
    cases f
    case mask => exact False.elim (hm rfl)
    case digestPrefixLen => exact False.elim (hp rfl)
    case p => exact ht.p.trans (he .x0 (by decide))
    case pLen => exact ht.pLen.trans (he .x2 (by decide))
    case qLen => exact ht.qLen.trans (he .x3 (by decide))
    case signature => exact ht.signature.trans (he .x4 (by decide))
    case digest => exact ht.digest.trans h6
    case digestLen => exact ht.digestLen.trans h7
    case out => exact ht.unused.1
    case nonce => exact ht.unused.2
    case q => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide)] using ht.q
    case g => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.g
    case y => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.y
    case x => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.x
  · rw [← hmem]
    exact ht.frame

end VG.Proof.Dsa.AArch64

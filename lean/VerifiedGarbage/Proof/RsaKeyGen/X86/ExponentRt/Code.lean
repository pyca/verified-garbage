module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Filter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRanges
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentImport
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentClass
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFilterContext
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The exponent stage at a run-time width: save, import and coprimality, with the candidate kept -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def ranges (w : Nat) : List (Nat × Nat) := [(slot w 5, 8 * w), (128, 8)] ++ ExponentFilter.ranges w

theorem prepare_ok {s : State} {base : Addr} {size w candidate len : Nat} {e : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (large : 1 < candidate) (odd : candidate % 2 = 1)
    (pointer : s.mem.readW (off base 12) 32 = e) (length : w32 s.mem base 16 = len)
    (ePositive : 0 < len) (eBound : len ≤ 8) (eFit : e.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len)
    (separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨base, size⟩)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat)
    (outLen : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code) s fun t =>
      ExponentFilter.Input base size w candidate
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) t ∧
      WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w), (128, 8)] s.mem t.mem ∧
      Frame [⟨base, size⟩] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      t.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
  have gap : slot w 0 + 8 * w ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  have savedLo : 400 ≤ slot w 5 := by unfold slot stride VG.Impl.Bignum.hdrBytes; omega
  have sourceLo : 256 ≤ slot w 0 := by change 256 ≤ 256 + 0 * stride w; omega
  have header : 256 ≤ size := by omega
  have exponentBound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) < 2 ^ 64 := by
    calc _ < 256 ^ len := by
           simpa only [VG.Proof.Bignum.bytesAt_length] using VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)
         _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) eBound
         _ = 2 ^ 64 := by decide
  refine WP.seq (WP.mono (save_ok S width widthBound space outLen
    (by rw [candidateEq]; exact odd)) fun a ⟨saved, Oa, Ka⟩ => ?_)
  rw [candidateEq] at saved
  have savedA : val32 a.mem base (slot w 5) (2 * w) = candidate - 1 := by omega
  have originalA : val32 a.mem base (slot w 0) (2 * w) = candidate :=
    (Oa.val32 (Or.inl (by omega)) (by have := S.nowrap; omega)).trans candidateEq
  have Sa := S.of_keeps Ka (by decide)
  have Fa := VG.Proof.Bignum.outside_frame Oa (by have := S.nowrap; omega)
  have eUnchanged : Spec.Rsa.bytesAt a.mem (e.setWidth 64) len = Spec.Rsa.bytesAt s.mem (e.setWidth 64) len :=
    VG.Proof.RsaKeyGen.frame_bytesAt Fa
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact separateE.sub_right (Offset.sub_base base space))
      (by omega)
  refine WP.mono (ExponentImport.code_ok Sa header
    (by rw [BitVec.eq_of_toNat_eq (Oa.w32 (d := 12) (by omega) (by decide))]; exact pointer)
    (by rw [Oa.w32 (d := 16) (by omega) (by decide)]; exact length)
    ePositive eBound eFit (by rw [Ka.2.1, Ka.2.2]; exact readable)
    (separateE.sub_right (Offset.sub_base base (by omega)))) fun b ⟨value, Ob, Kb⟩ => ?_
  rw [eUnchanged] at value
  have originalB := (Ob.val32 (d := slot w 0) (k := 2 * w) (Or.inr (by omega)) (by have := S.nowrap; omega)).trans originalA
  have savedB := (Ob.val32 (d := slot w 5) (k := 2 * w) (Or.inr (by omega)) (by have := S.nowrap; omega)).trans savedA
  have exponentEq : Mod64.exponentValue b.mem base 128 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) := by
    rw [ExponentFilter.exponent_word, value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt exponentBound]
  have Ksb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (Ka.mono (by decide)).trans Kb
  have I : ExponentFilter.Input base size w candidate (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) b :=
    ⟨Sa.of_keeps Kb (by decide), width, widthBound, space, originalB, savedB, large, odd, exponentEq,
      by rw [Ksb.1 .esp (by decide)]; exact fit, by rw [Ksb.1 .esp (by decide)]; exact separateStack⟩
  have Wa : WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w)] s.mem a.mem :=
    WorkspaceFrame.of_outs S.nowrap (Outs.of_outside Oa (List.mem_singleton_self _))
  have Wb : WorkspaceFrame ⟨base, size, w⟩ [(128, 8)] a.mem b.mem :=
    WorkspaceFrame.of_outs S.nowrap (Outs.of_outside Ob (List.mem_singleton_self _))
  have W : WorkspaceFrame ⟨base, size, w⟩ [(slot w 5, 8 * w), (128, 8)] s.mem b.mem :=
    (Wa.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans
      (Wb.mono (fun _ mem => List.mem_cons_of_mem _ mem))
  have Fsave : Frame [⟨base, size⟩] s.mem a.mem := workspaceGlobalFrame (g := ⟨base, size, w⟩)
    (Outs.of_outside Oa (List.mem_singleton_self _)) (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change slot w 5 + 8 * w ≤ size; exact space)
  have Fimport : Frame [⟨base, size⟩] a.mem b.mem := workspaceGlobalFrame (g := ⟨base, size, w⟩)
    (Outs.of_outside Ob (List.mem_singleton_self _)) (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 128 + 8 ≤ size; omega)
  have lenB : b.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) := by
    rw [BitVec.eq_of_toNat_eq (Ob.w32 (d := 4) (by omega) (by omega)),
      BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (by have := slot5_eq w; omega) (by omega)), outLen]
  exact ⟨I, W, Fsave.trans Fimport, Ksb, lenB⟩

theorem code_ok {s : State} {base : Addr} {size w candidate len : Nat} {e : BitVec 32}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size)
    (candidateEq : val32 s.mem base (slot w 0) (2 * w) = candidate)
    (large : 1 < candidate) (odd : candidate % 2 = 1)
    (pointer : s.mem.readW (off base 12) 32 = e) (length : w32 s.mem base 16 = len)
    (ePositive : 0 < len) (eBound : len ≤ 8) (eFit : e.toNat + len ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len)
    (separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨base, size⟩)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separateStack : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat)
    (outLen : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentRt.code s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len)) = 1)).toNat ∧
      val32 t.mem base (slot w 0) (2 * w) = candidate ∧
      val32 t.mem base (slot w 5) (2 * w) = candidate - 1 ∧
      WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem ∧
      Frame [⟨base, size⟩, below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentRt.code
  apply WP.assoc
  refine WP.seq (WP.mono (prepare_ok S width widthBound space candidateEq large odd pointer length
    ePositive eBound eFit readable separateE fit separateStack outLen) fun b ⟨I, Wb, Fb, Kb, lenB⟩ => ?_)
  refine WP.mono (filter_ok I lenB) fun t T => ?_
  have W : WorkspaceFrame ⟨base, size, w⟩ (ranges w) s.mem t.mem :=
    (Wb.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (T.workspace.mono (fun _ mem => List.mem_append_right _ mem))
  refine ⟨T.result, T.original, (T.savedValue width space).trans I.saved, W, ?_, Kb.trans T.keeps⟩
  have Ft := T.frame
  rw [Kb.1 .esp (by decide)] at Ft
  exact (Fb.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)).trans Ft

end VG.Proof.RsaKeyGen.X86.ExponentRt

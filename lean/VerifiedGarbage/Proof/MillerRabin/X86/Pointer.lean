module

import VerifiedGarbage.Proof.MillerRabin.X86.Scale
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Runtime prepared array pointers on i686 -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.Mont (arrAt hdrBytes)

theorem ptr_ok {s : State} {W : Addr} {L w j : Nat} (hw : Ws s W L)
    (base : PtrAt s W .edi 0) (index : j < 32) (arrayFit : arrAt w j < L)
    (headerFit : 228 ≤ L) (stride : w32 s.mem W 224 = 8 * (w + 2))
    (pointers : ∀ k < 8, w32 s.mem W (64 + 8 * k) = (W.toNat + arrAt w k) % 2 ^ 32)
    (r : Reg) (notBase : .edi ≠ r) (notTmp : .edx ≠ r) :
    WP isa (.block (ptr r j)) s fun t =>
      PtrAt t W r (arrAt w j) ∧ t.mem = s.mem ∧ Keeps [r, .edx] s t := by
  have nowrap := hw.nowrap
  unfold ptr
  split
  · rename_i short
    refine wp_movS (readSrc_ptr hw base (d := 64 + 8 * j) (by omega)) fun t T _ => WP.block_nil ?_
    refine ⟨?_, T.mem, T.keeps.mono (by simp)⟩
    rw [PtrAt, T.gpr, Nat.zero_add]
    exact pointers j short
  · rename_i long
    simp only [List.cons_append, List.nil_append]
    refine wp_movS (readSrc_ptr hw base (d := 224) (by omega)) fun a A _ => ?_
    refine wp_movS rfl fun b B _ => ?_
    have value : (b.gpr .edx).toNat = 8 * (w + 2) := by
      rw [B.other .edx notTmp, A.gpr, Nat.zero_add]; exact stride
    refine WP.block_append (WP.mono (scaleIndex_ok b r .edx notTmp j index B.gpr) fun c ⟨R, M, K⟩ => ?_)
    refine wp_addS rfl fun d D _ => wp_addS rfl fun t T _ => WP.block_nil ?_
    have baseVal : (s.gpr .edi).toNat = W.toNat := by
      rw [base, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    have ediC : c.gpr .edi = s.gpr .edi := by
      rw [K.1 .edi (by simpa using notBase), B.other .edi notBase, A.other .edi (by decide)]
    refine ⟨?_, T.mem.trans (D.mem.trans (M.trans (B.mem.trans A.mem))), ?_⟩
    · rw [PtrAt, T.gpr, D.gpr, R, ediC, BitVec.toNat_add, BitVec.toNat_add,
        BitVec.toNat_mul, BitVec.toNat_ofNat, show (256 : BitVec 32).toNat = 256 from rfl, value, baseVal]
      rw [Nat.mod_eq_of_lt (a := j) (by omega)]
      unfold arrAt hdrBytes at arrayFit ⊢
      omega
    · exact (((A.keeps.mono (by simp)).widen B.keeps (by simp)).trans (K.mono (by simp))).trans
        ((D.keeps.mono (by simp)).trans (T.keeps.mono (by simp)))

end VG.Proof.MillerRabin.X86

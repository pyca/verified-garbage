module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorResult
import VerifiedGarbage.Proof.Framework.Omega

/-! # Common frame binding for generator-input and generator-result checks -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.Rsa VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem generatorCheck_ok {s : State} {B F : Addr} {Z w len : Nat} {W : Nat → BitVec 64}
    {pb xb : List Byte} (result : Bool) (h : Ws s B Z w) (hl : len < 2 ^ 16)
    (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (sp : Src s B Z (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sx : Src s B Z (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) xb)
    (hp : pb.length = len) (hx : xb.length = len) (hpos : 1 ≤ len) (hfit : len ≤ 8 * w)
    (hodd : result = false → Spec.Rsa.os2ip pb % 2 = 1)
    (hresult : result = true → Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb) :
    WP isa (.seq (.block (headerArguments (generatorRangeArguments len result)))
      (if result then generatorResult else generatorRange)) s fun t =>
      t.gpr .x3 = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [(128, 128), ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (generatorArguments_ok h hl result hsp hr hwords hsep)
    fun u ⟨hu, up, upl, ux, uxl, fu, ku⟩ => ?_)
  have ff : Frm B [(128, 128)] s.mem u.mem := Frm.of_outside fu (by simp)
  have hb : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ Z := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.h256
  have spu := sp.congrK (InScr.of_frm ff hb) ku
  have sxu := sx.congrK (InScr.of_frm ff hb) ku
  have check : WP isa (if result then generatorResult else generatorRange) u fun t =>
      t.gpr .x3 = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] u.mem t.mem ∧ Keep mmRegs u t := by
    cases result with
    | false =>
      exact generatorRange_ok hu up (by rw [hp]; exact upl) ux (by rw [hx]; exact uxl)
        spu sxu (by omega) (by omega) (by omega) (by omega) (hodd rfl)
    | true =>
      exact generatorResult_ok hu up (by rw [hp]; exact upl) ux (by rw [hx]; exact uxl)
        spu sxu (by omega) (by omega) (by omega) (by omega) (hresult rfl)
  exact WP.mono check fun t ⟨hm, ht, ft, kt⟩ =>
    ⟨hm, ht, (ff.mono (by simp)).trans (ft.mono (fun r hr => List.mem_cons_of_mem _ hr)),
      (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

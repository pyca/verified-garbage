module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Copies between the modulus, prime and exponent banks share one loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem copy_loc_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (w : Width) (out src : Loc)
    (fo : out.offset n + 4 * w.words n ≤ Z) (fs : src.offset n + 4 * w.words n ≤ Z)
    (sep : out.offset n + 4 * w.words n ≤ src.offset n ∨
      src.offset n + 4 * w.words n ≤ out.offset n) :
    WP isa (copy w out src) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * w.words n) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (w.words n) = val32 s.mem B (src.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  have positive := h.old.wpos
  have divisible := h.width
  have wp : 0 < w.words n := by cases w <;> simp only [Width.words] <;> omega
  unfold copy
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok src (by decide) (by decide) (by omega) fun a K1 m1 P1 => ?_)
  have ha := h.keep K1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine ha.ptr_ok out (by decide) (by decide) (by omega) fun b K2 m2 P2 => ?_
  have hb := ha.keep K2 (by rw [m2]; exact Outside.refl _ _ _ _)
  refine hb.bytes_ok w .edi fun c K3 m3 count => wp_movS rfl fun d U _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s d :=
    ((K1.mono (by decide)).trans (K2.mono (by decide))).trans
      ((K3.mono (by decide)).trans (U.keeps.mono (by decide)))
  have m : d.mem = s.mem := U.mem.trans (m3.trans (m2.trans m1))
  have psrc : PtrAt d B .ebp (src.offset n) := by
    rw [PtrAt, U.other _ (by decide), K3.1 _ (by decide), K2.1 _ (by decide)]
    exact P1
  have pout : PtrAt d B .ebx (out.offset n) := by
    rw [PtrAt, U.other _ (by decide), K3.1 _ (by decide)]
    exact P2
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok (h.full.rt.of_keeps K)
    true wp fs fo sep psrc pout (by rw [U.other _ (by decide)]; exact count) U.gpr)
    fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans
    (Kt.mono (by decide))
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restore VG.Impl.Rsa.X86.KeyRt.restoreEdi
  refine wp_movS (h.full.wsArg.keep KK (by decide) O0).readSrc fun u U _ => WP.block_nil ?_
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide)))
      (U.gpr.trans (VG.Proof.Rsa.X86.KeyRt.RtWs.edi_eq h.full).symm)
  refine ⟨h.keep Kall (by rw [U.mem]; exact O0), ?_, ?_, Kall⟩
  · rw [U.mem]; exact O
  · simpa only [U.mem, ite_true] using V

end VG.Proof.RsaKeyGen.X86.KeyRuntime

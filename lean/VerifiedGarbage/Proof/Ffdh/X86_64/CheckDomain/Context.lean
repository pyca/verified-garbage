module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH domain validation on x86-64: input memory and sizes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure CdCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (s.gpr .r8).toNat * 8
  scr : Scr s (s.gpr .rcx) ((s.gpr .r8).toNat * 8)
  dom : Src s (s.gpr .rcx) ((s.gpr .r8).toNat * 8) (s.gpr .rdi) (cdDom s)

theorem cdCtx_of {s : State} (h : cdPre s) : CdCtx s := by
  obtain ⟨hrd, hwr, dds, wD, wS, _, _, ⟨hk1, hk2⟩, hdl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds⟩

def cdOf (s : State) : CdP :=
  ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8, (s.gpr .rdx).toNat, (s.gpr .rsi).toNat,
    s.gpr .rdi, cdDom s, s.gpr .rsp⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

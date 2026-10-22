module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
meta import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
meta import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin

/-!
# AES-GCM `seal_split` on x86-64: the one-pass loops

Untrusted: everything here is checked by Lean. What `prefixN` needs of its
loop (`EncNOk`, the taint check from `encNRegs`, and that no instruction
loads `MXCSR` or writes `rsp` and nothing is pushed), for the loop on
512-bit registers (`StitchZHTo.encN`, from its literal) and for that on
256-bit ones (`StitchR.encN`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64

theorem encNR_ok {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (hS : Gcm.X86_64.StitchR.SetupFin np hpn) :
    EncNOk np hpn Impl.Gcm.X86_64.StitchR.encN :=
  fun hp hm hn => Gcm.X86_64.StitchR.encN_ok hS hp hm hn

theorem encNZ_ok (h1 : Gcm.X86_64.StitchZHTo.PhaseOne) : EncNOk 24 (by decide) Impl.Gcm.X86_64.StitchZHTo.encN :=
  fun hp hm hn => Gcm.X86_64.StitchZHTo.encN_ok h1 hp hm hn

theorem encNZ_check :
    ∃ hc, (taint.check (Taint.ofRegs encNRegs) Impl.Gcm.X86_64.StitchZHTo.encN hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encNZ_mx : Impl.Gcm.X86_64.StitchZHTo.encN.allInstrs (fun i => !loadsMxcsr i) = true := by
  lit_decide
theorem encNZ_spSafe : Impl.Gcm.X86_64.StitchZHTo.encN.all (fun i => !X86_64.isa.writesSp i) = true :=
  Code.all_of_allInstrs (by lit_decide)
theorem encNZ_xdepth : Impl.Gcm.X86_64.StitchZHTo.encN.x86_64Depth = 0 := by decide +kernel

end VG.Proof.AesGcm.X86_64.Split

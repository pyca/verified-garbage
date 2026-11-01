module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline

import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
import VerifiedGarbage.Proof.Dsa.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

/-! # The domain check and key derivation with call-based arithmetic backends -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem parameters_implies8 :
    (Proof.Dsa.checkParametersContract abi).Implies (Proof.Dsa.checkParametersContract abi 8) where
  pre := by
    intro s h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
      [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem derive_implies8 : (Spec.Dsa.deriveKeyContract abi).Implies (Spec.Dsa.deriveKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
      [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem parameters_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Proof.Dsa.checkParametersContract abi).post s b) :
    (Proof.Dsa.checkParametersContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem derive_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyContract abi).post s b) :
    (Spec.Dsa.deriveKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := deriveABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self) ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem parameters_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.checkParameters Sq.mm M.mm)
    (hmx : (Generate.checkParameters Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Proof.Dsa.checkParametersContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ parametersCorrect M Sq hmx) (hin ▸ parametersConstantTime M Sq)
    parameters_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => parameters_patch s b hv u hp)

theorem derive_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveKey Sq.mm M.mm)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCorrect M Sq hmx) (hin ▸ deriveConstantTime M Sq)
    derive_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    derive_patch

end VG.Proof.Dsa.X86_64

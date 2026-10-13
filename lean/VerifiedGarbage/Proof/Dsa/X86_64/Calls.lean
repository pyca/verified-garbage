module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-! # DSA using RSA's callable Montgomery kernels

The shared contracts already parameterize stack use. Calls need eight bytes
for the return address; the arithmetic and leakage proofs apply to their
inlined bodies. Output buffers remain disjoint from that stack slot.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem signing_implies8 : (Spec.Dsa.signContract abi).Implies (Spec.Dsa.signContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
    sig_split h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
      [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem verifying_implies8 : (Spec.Dsa.verifyContract abi).Implies (Spec.Dsa.verifyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at h
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at h
    sig_split h
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
      [verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifyingSatState

theorem signing_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.signContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.signContract abi).post s b) :
    (Spec.Dsa.signContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := signingABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self)
    ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp ⊢
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem verifying_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Spec.Dsa.verifyContract abi).post s b) :
    (Spec.Dsa.verifyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at hp ⊢
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem signing_call_verified (M : Mont) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = SignVerify.sign M.mm)
    (hmx : (SignVerify.sign M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.signContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ signingCorrect M hmx) (hin ▸ signingConstantTime M)
    signing_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    signing_patch

theorem verifying_call_verified (M : Mont) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = SignVerify.verify M.mm)
    (hmx : (SignVerify.verify M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.verifyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ verifyingCorrect M hmx) (hin ▸ verifyingConstantTime M)
    verifying_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => verifying_patch s b hv u hp)

end VG.Proof.Dsa.X86_64

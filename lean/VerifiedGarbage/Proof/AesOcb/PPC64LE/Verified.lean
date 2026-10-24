module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Seal
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Open
import VerifiedGarbage.Proof.AesOcb.PPC64LE.FnCT
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# AES-OCB on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; with no stack: a call keeps the return address
in the link register, which each function saves in the working space).
`Frame.lean` allocates the working space; `init` is AES-GCM's
(`Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

theorem seal_correct (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0, with
the stack arguments at `0x8060`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 1 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8068 then 4 else bif Nat.beq a.toNat 0x8061 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified PPC64LE.target «seal» (Proof.AesOcb.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealPPC64LE, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified PPC64LE.target «open» (Proof.AesOcb.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Spec.Ocb.openPost, Spec.Ocb.openLeak, openPPC64LE, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW,
        Mem.read] using openSat }

end VG.Proof.AesOcb.PPC64LE

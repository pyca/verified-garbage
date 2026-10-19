module

import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Ecb
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.ConstantTime
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Step
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox

/-! # The SSE2 bitsliced ECB functions meet their contracts -/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedSse

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (contract ecbTaint_agree satState publicRegs_five)

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceSse.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .encrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceSse.encrypt) (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceSse.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .decrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceSse.decrypt) (by lit_decide) he ha, hp⟩

theorem encrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceSse.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encrypt_constantTime _ _ (ecbTaint_agree .encrypt)) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_five] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceSse.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decrypt_constantTime _ _ (ecbTaint_agree .decrypt)) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, contract, publicRegs_five] [satState] using satState

end VG.Proof.TripleDes.X86_64.BitslicedSse

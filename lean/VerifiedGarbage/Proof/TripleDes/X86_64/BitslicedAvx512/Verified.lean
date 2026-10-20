module

import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Ecb
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Ecb
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Ecb
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox

/-! # The AVX-512 bitsliced ECB functions are correct

The ECB functions run this code with the core's inlined; they are verified
in `EcbCall/Verified.lean`. -/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (contract)

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx512.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .encrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceAvx512.encrypt) (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx512.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .decrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.TripleDes.X86_64.BitsliceAvx512.decrypt) (by lit_decide) he ha, hp⟩

end VG.Proof.TripleDes.X86_64.BitslicedAvx512

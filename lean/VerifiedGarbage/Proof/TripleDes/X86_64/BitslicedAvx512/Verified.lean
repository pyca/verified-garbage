import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Ecb
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified

/-! # The AVX-512 bitsliced ECB functions are correct

The ECB functions run this code with the core's inlined; they are verified
in `EcbCall/Verified.lean`. -/

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

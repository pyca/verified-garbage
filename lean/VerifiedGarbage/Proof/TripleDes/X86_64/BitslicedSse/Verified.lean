module

import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Ecb
public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Lit

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

end VG.Proof.TripleDes.X86_64.BitslicedSse

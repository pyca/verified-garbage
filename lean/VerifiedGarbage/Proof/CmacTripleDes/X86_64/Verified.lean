module

import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.CT
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Implies
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.Scratch
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# TDEA-CMAC on x86-64: `Verified`

Correctness and constant time under this target's contracts (`Contract.lean`),
and the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which imply them, with no stack: the
functions call nothing.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem update_mx : update.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finalize_mx : finalize.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

theorem update_correct (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec update_mx he hg, hp⟩

theorem finalize_correct (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec finalize_mx he hg, hp⟩

theorem init_verified : Verified X86_64.target init (initScratchContract X86_64.abi 0) :=
  Verified.of_correct init_correct init_ct init_implies

theorem update_verified : Verified X86_64.target update (updateScratchContract X86_64.abi 0) :=
  Verified.of_correct update_correct update_ct update_implies

theorem finalize_verified : Verified X86_64.target finalize (finalizeScratchContract X86_64.abi 0) :=
  Verified.of_correct finalize_correct finalize_ct finalize_implies

end VG.Proof.CmacTripleDes.X86_64

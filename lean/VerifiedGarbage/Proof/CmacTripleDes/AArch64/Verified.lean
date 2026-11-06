module
public import VerifiedGarbage.Impl.CmacTripleDes.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.Scratch

import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Init
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# TDEA-CMAC on AArch64: correctness

Correctness under this target's contracts (`Contract.lean`), with no stack:
the functions call nothing, and write only `x0`–`x17` and the callee-saved
registers the block saves and restores (`block_ok`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.AArch64

/-- The registers the ABI preserves that the code never writes. -/
def unsaved : List Reg := preserved.filter (· ∉ savedRegs)

/-- The ABI's obligations, for code that keeps the registers of `savedRegs`,
writes none of the others it preserves and no vector register, and calls
nothing. -/
theorem abi_of {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => Q s' ∧ ∀ r ∈ savedRegs, s'.gpr r = s.gpr r)
    (hc : c.allInstrs (fun i => unsaved.all fun r => !clobbers i r) = true)
    (hn : c.noCalls = true) (hv : c.allInstrs keepsV = true) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s' := by
  obtain ⟨t, s', he, ⟨hq, hsv⟩, hg⟩ := WP.gprs h hc hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩, hq⟩
  by_cases hs : r ∈ savedRegs
  · exact hsv r hs
  · exact hg r (List.mem_filter.mpr ⟨hr, by simpa using hs⟩)

theorem init_correct (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  abi_of (init_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

theorem update_correct (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  abi_of (WP.mono (update_wp hs) fun _ ⟨h, sv⟩ => ⟨h, fun r hr => by
    obtain ⟨i, hi, rfl⟩ := mem_savedRegs hr; exact sv i hi⟩) (by lit_decide) (by lit_decide)
    (by lit_decide)

theorem finalize_correct (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  abi_of (finalize_wp hs) (by lit_decide) (by lit_decide) (by lit_decide)

end VG.Proof.CmacTripleDes.AArch64

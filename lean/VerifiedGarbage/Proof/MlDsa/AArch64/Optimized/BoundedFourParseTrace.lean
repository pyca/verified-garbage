import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def parseModel (η k off : Nat) : Prog isa :=
 .seq (.block (parseAddress k off))
   (.seq (parseCore η) (.block [.str .x .x4 .x19 (7904+8*k)]))

/-- Reassociation and splitting a straight-line prefix preserve the exact trace. -/
theorem parse_exec_model {η k off : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) s tr t) :
    Exec isa (parseModel η k off) s tr t := by
  change Exec isa (.seq (.block (parseAddress k off++parseSetup η))
    (.seq (.ite (.zero .x .x8) (.block []) (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
      (.seq (.block fallbackSetup)
        (.seq (.ite (.zero .x .x8) (.block []) (.loop (scalarLoopBody η) (.nonzero .x .x8)))
          (.block [.str .x .x4 .x19 (7904+8*k)]))))) s tr t at h
  cases h with | seq hp hr =>
    cases hr with | seq hv hr =>
      cases hr with | seq hf hr =>
        cases hr with | seq hs ht =>
          rw [Exec.block_iff,execBlock_append] at hp
          obtain ⟨⟨a,ta⟩,ha,hb⟩:=Option.bind_eq_some_iff.mp hp
          obtain ⟨⟨b,tb⟩,hc,he⟩:=Option.map_eq_some_iff.mp hb
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl,rfl⟩:=he
          have hx : Exec isa (parseModel η k off) s _ t :=
            .seq (.block ha) (.seq (.seq (.block hc) (.seq hv (.seq hf hs))) ht)
          simpa only [List.append_assoc] using hx

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

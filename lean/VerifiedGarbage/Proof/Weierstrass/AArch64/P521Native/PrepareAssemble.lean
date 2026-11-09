module

-- separate module: literal phase concatenation is checked separately from the machine-state contracts it connects

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PreparePre
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PreparePeer
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareRepresentation
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareScalar
import VerifiedGarbage.Proof.Framework.Block

/-! The proven preparation components concatenate to the selected outer phase. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock001 outerBlock003 outerBlock005 sequence validateAndPrepare)

def prepareStages : Prog isa :=
  .seq (.block (outerBlock001.take 5)) <| .seq prepareLoadBits <|
  .seq preparePeer <| .seq prepareCheck <| .seq prepareRepresentations (.block outerBlock005)

/-- Joining adjacent straight-line blocks and omitting empty sequence terminals
preserves all preparation postconditions, including those of the machine proofs. -/
theorem prepare_stages_wp {s : State} {Q : State → Prop} (h : WP isa prepareStages s Q) :
    WP isa validateAndPrepare s Q := by
  have first : outerBlock001=outerBlock001.take 5++outerBlock001.drop 5 := (List.take_append_drop ..).symm
  have peer : outerBlock003=outerBlock003.take 137++outerBlock003.drop 137 := (List.take_append_drop ..).symm
  simp only [validateAndPrepare,sequence,List.foldr_cons,List.foldr_nil]
  rw [first,peer]
  simp only [prepareStages,prepareLoadBits,preparePeer,prepareCheck,prepareRepresentations,prepareFromSlots,
    sequence,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil] at h ⊢
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)] at h ⊢
  exact h

end VG.Proof.Weierstrass.AArch64.P521Native

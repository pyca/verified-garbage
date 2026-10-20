module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def parseAddress : List Instr :=
 [Impl.MlKem.AArch64.mov .x2 .x24,Impl.MlKem.AArch64.mov .x3 .x25,.ldr .x .x4 .x26 0]

theorem parseAddress_ok {s : State}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x26) 8) :
    WP isa (.block parseAddress) s fun t=>Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2=s.gpr .x24 ∧ t.gpr .x3=s.gpr .x25 ∧
      t.gpr .x4=s.mem.readW (s.gpr .x26) 64 := by
  unfold parseAddress
  refine wp_mov fun a ha h2=>wp_mov fun b hb h3=>
    wp_ldrx (a := s.gpr .x26) (by decide)
      (by rw [hb.get .x26,ha.get .x26]; exact BitVec.add_zero _)
      (by rw [hb.rd,ha.rd,hb.wr,ha.wr]; exact hr) fun t ht h4=>wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,hb.get .x2,h2]
  · rw [ht.get .x3,h3,ha.get .x25]
  · rw [h4,hb.mem,ha.mem]

theorem parse_wp (η : Nat) (s : State) (Q : State→Prop) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η) s Q ↔
      WP isa (.seq (.block parseAddress)
        (.seq (parseCore η) (.block VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parseNext))) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse,parseCore,
    fallback,fallbackSetup,scalarLoopBody]
  simp only [WP.seq_iff (M := isa)]
  change WP isa (.block (parseAddress ++ (scalarSetup η ++
    VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.vectorSetup η ++
    [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]))) s _ ↔ _
  rw [WP.block_append_iff]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

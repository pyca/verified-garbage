import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseCore

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def parseAddress (k off : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (840+544*k+off),.addImm .x .x3 .x21 (1024*k),
  .ldr .x .x4 .x19 (7904+8*k)]

theorem parseAddress_ok {s : State} {k off : Nat} (hk : k<4) (ho : off≤272)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (7904+8*k)) 8) :
    WP isa (.block (parseAddress k off)) s fun t=>Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2=s.gpr .x19+BitVec.ofNat 64 (840+544*k+off) ∧
      t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧
      t.gpr .x4=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (7904+8*k)) 64 := by
  unfold parseAddress
  refine wp_addImm (by omega) fun a ha h2=>wp_addImm (by omega) fun b hb h3=>
    wp_ldrx (by omega) (by rw [hb.get .x19,ha.get .x19])
      (by rw [hb.rd,ha.rd,hb.wr,ha.wr]; exact hr) fun t ht h4=>wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,hb.get .x2,h2]
  · rw [ht.get .x3,h3,ha.get .x21]
  · rw [h4,hb.mem,ha.mem]

theorem parse_wp (η k off : Nat) (s : State) (Q : State→Prop) :
    WP isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) s Q ↔
      WP isa (.seq (.block (parseAddress k off))
        (.seq (parseCore η) (.block [.str .x .x4 .x19 (7904+8*k)]))) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse,parseCore,
    VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.counts,fallback,fallbackSetup,scalarLoopBody]
  simp only [WP.seq_iff (M := isa)]
  change WP isa (.block (parseAddress k off ++ (scalarSetup η ++
    VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.vectorSetup η ++
    [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]))) s _ ↔ _
  rw [WP.block_append_iff]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

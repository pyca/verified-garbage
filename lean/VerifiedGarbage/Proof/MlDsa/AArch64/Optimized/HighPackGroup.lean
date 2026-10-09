import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

def groupTemps : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7]

def groupCode (g : Nat) : List Instr :=
  (([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j) =>
    [.ldrq r .x0 (16*j)] ++ hb g r r) ++ packTail (packWidth g)

structure GroupPost (g block : Nat) (a : Addr) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀ r, r∉groupTemps → t.v r=s.v r
  ready : PackReady g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (highPacked g (polyAt s.mem a))[(2*packWidth g)*block+i]!

/-- One actual machine group reads sixteen coefficients, computes HighBits,
and writes the corresponding original-specification bytes. -/
theorem group_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {a : Addr} {s : State} (hr : Reduced s.mem a) (hc : PackReady g s)
    (hp : s.gpr .x0=a+BitVec.ofNat 64 (64*block))
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, GroupPost g block a s t → WP isa (.block rest) t Q) :
    WP isa (.block (groupCode g ++ rest)) s Q := by
  unfold groupCode
  rw [List.append_assoc]
  refine loadFour_ok hg hc.toHighConstants hin fun u hu _ hv => ?_
  have cu := hc.afterLoads hu
  refine packTail_ok hg cu (by rw [hu.wr,hu.gpr]; exact hw8)
    (fun h => by rw [hu.wr,hu.gpr]; exact hw4 h) fun t ht => ?_
  refine k t ⟨(hu.keep.trans ht.keep).mono (by decide),?_,ht.ready,?_,?_⟩
  · intro r hrt
    have h0 : r∉[VReg.v0,.v1,.v2,.v3,.v7] := by
      intro h; exact hrt (by simp only [groupTemps,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    have h1 : r∉[VReg.v4,.v5,.v6] := by
      intro h; exact hrt (by simp only [groupTemps,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
    rw [ht.vec r h1,hu.get r h0]
  · simpa only [hu.gpr,hu.mem] using ht.frame
  · intro i hi
    have hbyte := ht.bytes i hi
    rw [hu.gpr] at hbyte
    rw [hbyte]
    exact packedVector_spec hg hr cu.toPackConstants hb hi (by simpa only [hp] using hv)

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedReduce
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Signed correction with the exact registers used by each pipelined lane. -/
def lowCadd (a t : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 t a 31),.vop (.logic .and t t .v31),.vop (.add .s4 a a t)]

theorem lowCadd_ok {a t : VReg} (hat : a≠t) (htq : t≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀u,VChg [t,a] s u →
      (∀e<4,vword (u.v a) e=Inverse.signCorrected (vword (s.v a) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (lowCadd a t++rest)) s Q := by
  refine wp_vop (d:=t) rfl fun u hu => wp_vop (d:=t) rfl fun v hv =>
    wp_vop (d:=a) rfl fun w hw => ?_
  refine k w (((hu.chg.trans hv.chg).trans hw.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hw.v,VG.AArch64.vword_map2 _ _ _ he,hv.get a hat,hu.get a hat,hv.v,Inverse.word_and,
      hu.v,VG.AArch64.vword_map2 _ _ _ he,hu.get .v31 (Ne.symm htq),hq e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

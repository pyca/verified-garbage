import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask)

def rawNorm (raw : VReg) : List Instr := ([.vop (.mov .v24 raw)] : List Instr) ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce ++ VG.Impl.MlDsa.AArch64.Optimized.Paired.norm

theorem rawNorm_ok (raw : VReg) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀t,VChg [.v24,.v25,.v30] s t →
      (∀e<4,vword (t.v .v24) e=reduceWord (vword (s.v raw) e)) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (rawNorm raw++rest)) s Q := by
  unfold rawNorm
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_vop (d:=.v24) rfl fun a ha => ?_
  refine reduce_ok (by intro e he; rw [ha.get .v31 (by decide)]; exact hq e he)
    (by intro e he; rw [ha.get .v8 (by decide)]; exact hc e he) fun b hb hv => ?_
  have hh : VChg [.v24,.v25] s b := (ha.chg.trans hb).mono (by decide)
  refine norm_ok fun t ht hn => ?_
  refine k t ((hh.trans ht).mono (by decide)) ?_ ?_
  · intro e he
    rw [ht.get .v24 (by decide),hv e he,ha.v]
  · intro e he
    rw [hn e he,hh.get .v30 (by decide),hh.get .v9 (by decide),hh.get .v10 (by decide),hv e he,ha.v]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

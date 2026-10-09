import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask minMask)

/-- Register-parametric form used by the two interleaved final r0 lanes. -/
def reduceRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31)]

theorem reduceRegs_ok {a t : VReg} (hat : a≠t) (htq : t≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,VChg [t,a] s u → (∀e<4,vword (u.v a) e=reduceWord (vword (s.v a) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (reduceRegs a t++rest)) s Q := by
  refine wp_vop (d := t) rfl fun u hu => wp_vop (d := t) rfl fun v hv =>
    wp_vop (d := a) rfl fun w hw => ?_
  refine k w (((hu.chg.trans hv.chg).trans hw.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hw.v,vword_mapWords3 _ _ _ _ he,hv.get a hat,hu.get a hat,
      hv.v,VG.AArch64.vword_map2 _ _ _ he,hu.v,VG.AArch64.vword_map2 _ _ _ he,
      hv.get .v31 (Ne.symm htq),hu.get .v31 (Ne.symm htq),hc e he,hq e he]
    rfl

def normRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v9),.vop (.umin t t .v10),
  .vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)]

theorem normRegs_ok {a t : VReg} (htw : t≠.v10) (htf : t≠.v30)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀u,VChg [t,.v30] s u → (∀e<4,vword (u.v .v30) e=
      vword (s.v .v30) e ||| normMask (vword (s.v a) e)
        (vword (s.v .v9) e) (vword (s.v .v10) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (normRegs a t++rest)) s Q := by
  refine wp_vop (d := t) rfl fun u hu => wp_vop (d := t) rfl fun v hv =>
    wp_vop (d := t) rfl fun w hw => wp_vop (d := .v30) rfl fun y hy => ?_
  refine k y (((hu.chg.trans hv.chg).trans hw.chg).trans hy.chg |>.mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [hy.v]
    simp only [vword,BitVec.extractLsb'_or]
    change vword (w.v .v30) e ||| vword (w.v t) e=_
    rw [hw.get .v30 (Ne.symm htf),hv.get .v30 (Ne.symm htf),hu.get .v30 (Ne.symm htf),
      hw.v,VG.AArch64.vword_map2 _ _ _ he,hv.v,VG.AArch64.vword_map2 _ _ _ he,
      hv.get .v10 (Ne.symm htw),hu.get .v10 (Ne.symm htw),hu.v,
      VG.AArch64.vword_map2 _ _ _ he,minMask]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

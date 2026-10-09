import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq wp_strq)

def laneVector (f : Nat → BitVec 32) : BitVec 128 := ofVWords (f 0) (f 1) (f 2) (f 3)
theorem laneVector_word (f : Nat → BitVec 32) {e : Nat} (he : e<4) : vword (laneVector f) e=f e := by
  rw [laneVector,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have h : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

def addInput (s : State) (off e : Nat) : BitVec 32 :=
  reduceWord (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e+
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16) e)
def addGroup (off : Nat) : List Instr :=
  [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,.vop (.add .s4 .v0 .v0 .v1)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Response.reduce .v0 ++ [.strq .v0 .x0 off] ++
  VG.Impl.MlDsa.AArch64.Optimized.Response.testNorm

theorem addGroup_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v1,.v2,.v6,.v31] s t →
      t.mem=s.mem.write (s.gpr .x0+BitVec.ofNat 64 off) 16 (laneVector (addInput s off)) →
      (∀e<4,vword (t.v .v31) e=vword (s.v .v31) e |||
        normMask (addInput s off e) (vword (s.v .v27) e) (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (addGroup off++rest)) s Q := by
  unfold addGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  refine wp_ldrq ho rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr] using hb) fun b h2 => ?_
  refine wp_vop (d := .v0) rfl fun c h3 => ?_
  have hk : VChg [.v0,.v1] s c := ((h1.chg.trans h2.chg).trans h3.chg).mono (by decide)
  refine reduce_ok (by decide : VReg.v0≠.v6)
    (by intro e he; rw [hk.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hk.get .v25 (by decide)]; exact hc e he) fun d hd hv => ?_
  have hd' : VChg [.v0,.v1,.v6] s d := (hk.trans hd).mono (by decide)
  have hval : d.v .v0=laneVector (addInput s off) := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he,hv e he,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v0,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
    rfl
  refine wp_strq ho rfl (by simpa only [hd'.wr,hd'.gpr] using hw) fun e he => ?_
  refine norm_ok fun t ht hn => ?_
  refine k t ?_ ?_ ?_
  · exact (((StepKeep.ofChg hd' (by decide)).trans (StepKeep.ofMem he)).trans
      (StepKeep.ofChg ht (by decide))).mono (by decide)
  · rw [ht.mem,he.mem,hd'.mem,hd'.gpr,hval]
  · intro i hi
    rw [hn i hi,he.v,hd'.get .v31 (by decide),hd'.get .v27 (by decide),
      hd'.get .v24 (by decide),hval,laneVector_word _ hi]

end VG.Proof.MlDsa.AArch64.Optimized.Response

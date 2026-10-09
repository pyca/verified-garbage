import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourState
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

structure InitKeep (rs : List Reg) (vs : List VReg) (s t : State) : Prop where
 keep : Keep rs s t
 mem : t.mem=s.mem
 vec : ∀r,r∉vs→t.v r=s.v r

theorem InitKeep.trans {rs qs : List Reg} {vs ws : List VReg} {s t u : State}
    (h : InitKeep rs vs s t) (k : InitKeep qs ws t u) : InitKeep (rs++qs) (vs++ws) s u := by
  refine ⟨h.keep.trans k.keep,k.mem.trans h.mem,?_⟩
  intro r hr
  rw [List.mem_append,not_or] at hr
  exact (k.vec r hr.2).trans (h.vec r hr.1)

theorem InitKeep.mono {rs qs : List Reg} {vs ws : List VReg} {s t : State}
    (h : InitKeep rs vs s t) (hr : ∀r∈rs,r∈qs) (hv : ∀r∈vs,r∈ws) : InitKeep qs ws s t :=
  ⟨h.keep.mono hr,h.mem,fun r hn=>h.vec r (fun hm=>hn (hv r hm))⟩

theorem InitKeep.ofV {s t : State} {d : VReg} {v : BitVec 128} (h : VUpd s t d v) (hd : d∉preservedV) :
    InitKeep [] [d] s t :=
  ⟨h.keep hd,h.mem,fun r hr=>h.other r (by simpa using hr)⟩

theorem InitKeep.ofOnly {rs : List Reg} {s t : State} (h : Only rs s t) (hv : t.v=s.v) :
    InitKeep rs [] s t := ⟨h.keep,h.mem,fun _ _=>congrFun hv _⟩

def pairSetup (d : VReg) (lo hi : BitVec 64) : List Instr :=
 Impl.MlKem.AArch64.movImm .x6 lo ++ Impl.MlKem.AArch64.movImm .x7 hi ++
 [.vop (.dup .d2 d .x6),.vop (.ins .d2 d 1 .x7)]

theorem pairSetup_ok (s : State) (d : VReg) (lo hi : BitVec 64) (hd : d∉preservedV) :
    WP isa (.block (pairSetup d lo hi)) s fun t=>
      InitKeep [.x6,.x7] [d] s t ∧ t.v d=ofVDwords lo hi := by
  unfold pairSetup
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 lo) fun a ha=>?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok a .x7 hi) fun b hb=>?_
  refine wp_vop (d := d) rfl fun c hc=>wp_vop (d := d) rfl fun t ht=>wp_nil ?_
  refine ⟨?_,?_⟩
  · refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
    · intro r hr
      have h6 : r≠.x6 := fun h=>hr (by simp [h])
      have h7 : r≠.x7 := fun h=>hr (by simp [h])
      rw [ht.gpr,hc.gpr,hb.2.1 r h7,ha.2.1 r h6]
    · rw [ht.rd,hc.rd,hb.2.2,ha.2.2]
    · rw [ht.wr,hc.wr,hb.2.2,ha.2.2]
    · rw [ht.sp,hc.sp,hb.2.2,ha.2.2]
    · intro r hr
      have hn : r≠d := fun h=>hd (h ▸ hr)
      rw [ht.other r hn,hc.other r hn,hb.2.2,ha.2.2]
    · rw [ht.mem,hc.mem,hb.2.2,ha.2.2]
    · intro r hr
      have hd : r≠d := by simpa using hr
      rw [ht.other r hd,hc.other r hd,hb.2.2,ha.2.2]
  · rw [ht.v,hc.gpr,hb.1,hc.v,hb.2.1 .x6 (by decide),ha.1]
    exact setLane_pair_hi _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

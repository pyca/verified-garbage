module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics

/-! ### `MlDsa.AArch64.Sign.CommitTailModel`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailFirst`, which this module and modules that import it used -/

section

/-! ## From `CommitTailAbsorb.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CommitTailWord.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem low_zero (w : BitVec 64) : setLane 0 64 0 w=ofVDwords w 0 := by
  apply vec64_ext
  · change (setLane 0 64 0 w).extractLsb' (64*0) 64=_
    rw [extract_setLane64 0 w (i := 0) (j := 0) (by decide) (by decide),vdword_ofVDwords_0]
    rfl
  · change (setLane 0 64 0 w).extractLsb' (64*1) 64=_
    rw [extract_setLane64 0 w (i := 0) (j := 1) (by decide) (by decide),vdword_ofVDwords_1]
    rfl

/-- A commitment absorb changes only the low lane. The independent mask
stream in the high lane remains intact across every block. -/
theorem lowWord_ok {s : State} {r : VReg} {off : Nat}
    (hr : r≠.v25) (ho : off%8=0 ∧ off<4096*8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 8) :
    WP isa (.block (lowWord r off)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      (∀v,v≠r → v≠.v25 → t.v v=s.v v) ∧
      t.v r=s.v r ^^^ ofVDwords (s.mem.readW (s.gpr .x5+BitVec.ofNat 64 off) 64) 0 := by
  unfold lowWord
  refine wp_ldr ho rfl hin fun a ha =>
    wp_vop (d := .v25) rfl fun b hb =>
    wp_vop (d := .v25) rfl fun c hc =>
    wp_vop (d := r) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((((RegKeep.upd ha).trans (RegKeep.vupd hb)).trans (RegKeep.vupd hc)).trans
    (RegKeep.vupd ht)).mono (by simp),ht.mem.trans (hc.mem.trans (hb.mem.trans ha.mem)),?_,?_⟩
  · intro v hvr hv25
    rw [ht.get v hvr,hc.get v hv25,hb.get v hv25,ha.vec]
  · rw [ht.v,hc.get r hr,hb.get r hr,ha.vec,hc.v,hb.v,hb.gpr,ha.gpr]
    exact congrArg (fun x => s.v r ^^^ x) (low_zero _)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords xorWords_get)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- One word extends the commitment prefix without touching the paired mask. -/
theorem lowWord_step {s : State} {A B : Spec.Sha3.State} {m : Mem} {p : Addr} {j : Nat}
    (hj : j<17) (hm : s.mem=m) (h5 : s.gpr .x5=p)
    (hp : Pairs s (xorWords A m p j) B)
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block (lowWord (vreg j) (8*j))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=m ∧ Pairs t (xorWords A m p (j+1)) B := by
  have h25 : vreg j≠.v25 := by
    change vreg j≠vreg 25
    rw [ne_eq,vreg_inj j (by omega_using [hj]) 25 (by decide)]
    omega_using [hj]
  refine WP.mono (lowWord_ok h25 ⟨by omega_using [],by omega_using [hj]⟩ (by rw [h5]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega_using [hj]),hm,h5,pair_xor]
    simp only [getElem!_pos (xorWords A m p j) j (by omega_using [hj]),
      getElem!_pos (xorWords A m p (j+1)) j (by omega_using [hj]), getElem!_pos B j (by omega_using [hj])]
    rw [xorWords_get _ _ _ _ _ (by omega_using [hj]),xorWords_get _ _ _ _ _ (by omega_using [hj])]
    simp only [Nat.lt_irrefl,ite_false,show j<j+1 by omega_using [],ite_true]
    rw [show A[j] ^^^ (0:BitVec 64)=A[j] from BitVec.xor_zero,
      show B[j] ^^^ (0:BitVec 64)=B[j] from BitVec.xor_zero]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he
    have hi25 : vreg i≠.v25 := by
      change vreg i≠vreg 25
      rw [ne_eq,vreg_inj i (by omega_using [hi]) 25 (by decide)]
      omega_using [hi]
    rw [hv _ hij hi25,hp i hi]
    have hh : (xorWords A m p j)[i]! = (xorWords A m p (j+1))[i]! := by
      simp only [getElem!_pos (xorWords A m p j) i hi,
        getElem!_pos (xorWords A m p (j+1)) i hi]
      rw [xorWords_get _ _ _ _ _ hi,xorWords_get _ _ _ _ _ hi]
      have hc : (i<j)=(i<j+1) := propext (by omega_using [he])
      simp only [hc]
    rw [hh]

/-- Fixed-count low-lane absorption leaves every high lane unchanged. -/
theorem lowWords_ok {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (n : Nat) (hn : n≤17)
    (hin : ∀j<n, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => lowWord (vreg j) (8*j))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (xorWords A s.mem (s.gpr .x5) n) B := by
  let I := fun j t => RegKeep [.x7] s t ∧ t.mem=s.mem ∧
    Pairs t (xorWords A s.mem (s.gpr .x5) j) B
  have hzero : xorWords A s.mem (s.gpr .x5) 0=A := by
    apply Vector.ext
    intro i hi
    simp only [xorWords_get, Nat.not_lt_zero, ite_false]
    exact BitVec.xor_zero
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) n (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (lowWord_step (by omega_using [hn, hj]) hm (hk.gpr .x5 (by decide)) hp ?_)
      fun u ⟨hk',hm',hp'⟩ => ⟨(hk.trans hk').mono (by simp),hm',hp'⟩
    rw [hk.rd,hk.wr]
    exact hin j hj
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hzero]; exact hp⟩

/-- A complete SHAKE-rate block advances only the commitment input pointer. -/
theorem full_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<17, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block full) s fun t =>
      RegKeep [.x5,.x7] s t ∧ t.mem=s.mem ∧
      t.gpr .x5=s.gpr .x5+136 ∧
      Pairs t (xorWords A s.mem (s.gpr .x5) 17) B := by
  rw [full,WP.block_append_iff]
  refine WP.mono (lowWords_ok hp 17 (by decide) hin) fun t ⟨hk,hm,hp'⟩ => ?_
  refine VG.Proof.Sha3.AArch64.WP.cons rfl (WP.block_nil_iff.mpr ?_)
  refine ⟨?_,hm,?_,hp'⟩
  · refine ⟨fun r hr => ?_,hk.rd,hk.wr,hk.sp⟩
    have h5 : r≠.x5 := by intro he; apply hr; simp only [he,List.mem_cons,true_or]
    simp only [RegUpd.gpr_write,h5,ite_false]
    exact hk.gpr r (by simp only [List.mem_cons,not_or] at hr ⊢; exact hr.2)
  · simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq]
    rw [hk.gpr .x5 (by decide)]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailLoadPair.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq wp_vop)
open VG.Proof.Sha3.AArch64.Sha3.Vector (low low_ext8)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Loads two consecutive words into consecutive low lanes; the temporary
high-lane values are overwritten by the independent mask initialization. -/
theorem loadPair_ok {s : State} {j off : Nat} {r : Reg}
    (hj : j+1<25) (ho : off%16=0 ∧ off<4096*16)
    (hin : InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 off) 16) :
    WP isa (.block [.ldrq (vreg j) r off,
      .vop (.ext (vreg (j+1)) (vreg j) (vreg j) 8)]) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<25,
      low t (vreg i)= if i=j+1 then (s.mem.read (s.gpr r+BitVec.ofNat 64 off) 16).extractLsb' 64 64
        else if i=j then (s.mem.read (s.gpr r+BitVec.ofNat 64 off) 16).extractLsb' 0 64
        else low s (vreg i) := by
  refine wp_ldrq ho rfl hin fun a ha =>
    wp_vop (d:=vreg (j+1)) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.vupd ha).trans (RegKeep.vupd ht)).mono (by simp),ht.mem.trans ha.mem,?_⟩
  intro i hi
  by_cases he : i=j+1
  · subst i
    simp only [ite_true,low,ht.v,ha.v]
    exact low_ext8 _
  · have he' : vreg i≠vreg (j+1) := by
      rw [ne_eq,vreg_inj i (by omega_using [hi]) (j+1) (by omega_using [hj])]; exact he
    simp only [he,ite_false,low,ht.get _ he']
    by_cases he0 : i=j
    · subst i
      simp only [ite_true,ha.v]
      rfl
    · have he0' : vreg i≠vreg j := by
        rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he0
      rw [ite_eq_right he0,ha.get _ he0']

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailLoadWords.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low pair_low pair_high)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3 (laneAddr)

structure Loaded (s : State) (r : Reg) (start n : Nat) (t : State) : Prop where
  keep : RegKeep [] s t
  mem : t.mem=s.mem
  lanes : ∀i<25, low t (vreg i)=if start≤i ∧ i<start+2*n
    then s.mem.readW (laneAddr (s.gpr r) (i-start)) 64 else low s (vreg i)

/-- Loads either μ or the packed commitment prefix, keeping the other lanes. -/
theorem loadWords_ok {s : State} {r : Reg} (start n : Nat) (hn : start+2*n≤25)
    (hin : ∀j<n, InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block ((List.range n).flatMap fun j =>
      ([.ldrq (vreg (start+2*j)) r (16*j),
        .vop (.ext (vreg (start+2*j+1)) (vreg (start+2*j)) (vreg (start+2*j)) 8)] : List Instr)))
      s (Loaded s r start n) := by
  refine wp_range_flatMap (M:=isa) (Loaded s r start) (fun j t hj ht => ?_) n
    (Nat.le_refl _) s ⟨RegKeep.refl _ _,rfl,?_⟩
  · have hin' : InRegions (t.rd++t.wr) (t.gpr r+BitVec.ofNat 64 (16*j)) 16 := by
      rw [ht.keep.rd,ht.keep.wr,ht.keep.gpr r (by simp)]
      exact hin j hj
    refine WP.mono (loadPair_ok (j:=start+2*j) (by omega_using [hn, hj]) ⟨by omega_using [],by omega_using [hn, hj]⟩ hin')
      fun u ⟨hu,hmu,hlu⟩ => ⟨(ht.keep.trans hu).mono (by simp),hmu.trans ht.mem,?_⟩
    intro i hi
    rw [hlu i hi,ht.mem,ht.keep.gpr r (by simp)]
    have hlow := pair_low s.mem (s.gpr r) j
    have hhigh := pair_high s.mem (s.gpr r) j
    change (s.mem.read (s.gpr r+BitVec.ofNat 64 (16*j)) 16).extractLsb' 0 64=_ at hlow
    change (s.mem.read (s.gpr r+BitVec.ofNat 64 (16*j)) 16).extractLsb' 64 64=_ at hhigh
    rw [hlow,hhigh]
    by_cases he1 : i=start+2*j+1
    · subst i
      rw [ite_eq_left rfl,ite_eq_left (by omega_using []),show start+2*j+1-start=2*j+1 by omega_using []]
    · rw [ite_eq_right he1]
      by_cases he0 : i=start+2*j
      · subst i
        rw [ite_eq_left rfl,ite_eq_left (by omega_using []),show start+2*j-start=2*j by omega_using []]
      · rw [ite_eq_right he0,ht.lanes i hi]
        have he : (start≤i ∧ i<start+2*j)↔(start≤i ∧ i<start+2*(j+1)) := by omega_using [he1, he0]
        simp only [he]
  · intro i hi
    rw [ite_eq_right (by omega_using [])]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailLoadEnd.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.Sha3.AArch64.Sha3.Vector (low)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Final input word of the first commitment-rate block. -/
theorem loadLast_ok {s : State}
    (hin : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8) :
    WP isa (.block [.ldr .x .x6 .x1 64,.vop (.dup .d2 .v16 .x6)]) s fun t =>
      RegKeep [.x6] s t ∧ t.mem=s.mem ∧ ∀i<25,
      low t (vreg i)=if i=16 then s.mem.readW (s.gpr .x1+64) 64 else low s (vreg i) := by
  refine wp_ldr (by decide) rfl hin fun a ha =>
    wp_vop (d:=.v16) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.upd ha).trans (RegKeep.vupd ht)).mono (by simp),ht.mem.trans ha.mem,?_⟩
  intro i hi
  by_cases he : i=16
  · subst i
    rw [ite_eq_left rfl]
    change vdword (t.v .v16) 0=_
    rw [ht.v,ha.gpr]
    exact vdword_ofVDwords_0 _ _
  · have he' : vreg i≠.v16 := by
      change vreg i≠vreg 16
      rw [ne_eq,vreg_inj i (by omega_using [hi]) 16 (by decide)]
      exact he
    simp only [he,ite_false,low,ht.get _ he',ha.vec]

structure Zeroed (s : State) (n : Nat) (t : State) : Prop where
  keep : RegKeep [] s t
  mem : t.mem=s.mem
  lanes : ∀i<25, low t (vreg i)=if 17≤i ∧ i<17+n then 0 else low s (vreg i)

/-- The capacity words of the low-lane SHAKE state start at zero. -/
theorem zeroCapacity_ok (s : State) :
    WP isa (.block ((List.range 8).map fun i => .vop (.movi0 (vreg (17+i))))) s (Zeroed s 8) := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa) (Zeroed s) (fun j t hj ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,?_⟩
  · refine wp_vop (d:=vreg (17+j)) rfl fun u hu => WP.block_nil_iff.mpr
      ⟨(ht.keep.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.mem,?_⟩
    intro i hi
    by_cases he : i=17+j
    · subst i
      rw [ite_eq_left (by omega_using [])]
      change vdword (u.v (vreg (17+j))) 0=0
      rw [hu.v]
      rfl
    · have he' : vreg i≠vreg (17+j) := by
        rw [ne_eq,vreg_inj i (by omega_using [hi]) (17+j) (by omega_using [hj])]; exact he
      change vdword (u.v (vreg i)) 0=_
      rw [hu.get _ he']
      change low t (vreg i)=_
      rw [ht.lanes i hi]
      have hh : (17≤i ∧ i<17+j)↔(17≤i ∧ i<17+(j+1)) := by omega_using [he]
      simp only [hh]
  · intro i hi
    rw [ite_eq_right (by omega_using [])]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailFirst.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low Lanes)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3 (laneAddr)

def firstState (m : Mem) (mu w1 : Addr) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<8 then m.readW (laneAddr mu i.val) 64
    else if i.val<17 then m.readW (laneAddr w1 (i.val-8)) 64 else 0

/-- Initializes the complete low-lane first block from μ and packed w₁. -/
theorem first_ok {s : State}
    (hmu : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*j)) 16)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8) :
    WP isa (.block first) s fun t => RegKeep [.x6] s t ∧ t.mem=s.mem ∧
      Lanes t (firstState s.mem (s.gpr .x0) (s.gpr .x1)) := by
  unfold first
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadWords_ok (r:=.x0) 0 4 (by decide) hmu) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWords_ok (r:=.x1) 8 4 (by decide) ?_) fun b hb => ?_
  · intro j hj
    rw [ha.keep.rd,ha.keep.wr,ha.keep.gpr .x1 (by simp)]
    exact hw j hj
  · rw [WP.block_append_iff]
    refine WP.mono (loadLast_ok ?_) fun c ⟨hc,hmc,hlc⟩ => ?_
    · rw [hb.keep.rd,hb.keep.wr,hb.keep.gpr .x1 (by simp),ha.keep.rd,ha.keep.wr,
        ha.keep.gpr .x1 (by simp)]
      exact hl
    · refine WP.mono (zeroCapacity_ok c) fun t ht => ?_
      refine ⟨(((ha.keep.trans hb.keep).trans hc).trans ht.keep).mono (by simp),
        ht.mem.trans (hmc.trans (hb.mem.trans ha.mem)),?_⟩
      intro i hi
      rw [ht.lanes i hi,hlc i hi,hb.lanes i hi,ha.lanes i hi,hb.mem,ha.mem,
        hb.keep.gpr .x1 (by simp),ha.keep.gpr .x1 (by simp)]
      simp only [firstState,Vector.getElem_ofFn,Nat.zero_add,Nat.sub_zero]
      by_cases h8 : i<8
      · rw [ite_eq_right (by omega_using [h8] : ¬ (17≤i ∧ i<17+8)),
          ite_eq_right (by omega_using [h8] : ¬ i=16),
          ite_eq_right (by omega_using [h8] : ¬ (8≤i ∧ i<8+2*4)),
          ite_eq_left (by omega_using [h8] : 0≤i ∧ i<2*4),ite_eq_left h8]
      · by_cases h16 : i<16
        · rw [ite_eq_right (by omega_using [h16] : ¬ (17≤i ∧ i<17+8)),
            ite_eq_right (by omega_using [h16] : ¬ i=16),
            ite_eq_left (by omega_using [h8, h16] : 8≤i ∧ i<8+2*4),ite_eq_right h8,
            ite_eq_left (by omega_using [h16] : i<17)]
        · by_cases he : i=16
          · subst i
            rw [ite_eq_right (by decide : ¬ (17≤16 ∧ 16<17+8)),ite_eq_left rfl,
              ite_eq_right (by decide : ¬ (16:Nat)<8),ite_eq_left (by decide : (16:Nat)<17)]
            rfl
          · rw [ite_eq_left (by omega_using [hi, h16, he] : 17≤i ∧ i<17+8),ite_eq_right h8,
              ite_eq_right (by omega_using [h16, he] : ¬ i<17)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end

/-! ### `MlDsa.AArch64.Sign.CommitTailPadding`, which only this module used -/

section

/-! ## From `CommitTailPaddingWord.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.Sha3.AArch64 (WP.cons Upd)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def xorWord (A : Spec.Sha3.State) (j : Nat) (w : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val=j then A[i] ^^^ w else A[i]

theorem xorWord_get (A : Spec.Sha3.State) (j : Nat) (w : BitVec 64) (i : Nat) (hi : i<25) :
    (xorWord A j w)[i]! = if i=j then A[i]! ^^^ w else A[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq A hi]
  simp only [xorWord,Vector.getElem_ofFn,Fin.getElem_fin]

def paddingWord (j : Nat) (imm : BitVec 16) (shift : Nat) : List Instr :=
  [.movz .x .x7 imm shift,.vop (.movi0 .v25),.vop (.ins .d2 .v25 0 .x7),
    .vop (.logic .eor (vreg j) (vreg j) .v25)]

/-- One low-lane padding constant never affects the cached mask stream. -/
theorem paddingWord_ok {s : State} {A B : Spec.Sha3.State} {j : Nat} (hj : j<25)
    (imm : BitVec 16) (shift : Nat) (hs : shift<4) (hp : Pairs s A B) :
    WP isa (.block (paddingWord j imm shift)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (xorWord A j (imm.setWidth 64 <<< (16*shift))) B := by
  unfold paddingWord
  let w : BitVec 64 := imm.setWidth 64 <<< (16*shift)
  refine WP.cons (s':=s.write .x .x7 w) (by simp [exec,w,Size.bits,Nat.mul_comm]; omega_using [hs]) ?_
  have hu := Upd.write64 s .x7 w
  refine wp_vop (d:=.v25) rfl fun a ha =>
    wp_vop (d:=.v25) rfl fun b hb =>
    wp_vop (d:=vreg j) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((((RegKeep.upd hu).trans (RegKeep.vupd ha)).trans (RegKeep.vupd hb)).trans
    (RegKeep.vupd ht)).mono (by simp),ht.mem.trans (hb.mem.trans (ha.mem.trans hu.mem)),?_⟩
  have hj25 : vreg j≠.v25 := by
    change vreg j≠vreg 25
    rw [ne_eq,vreg_inj j (by omega_using [hj]) 25 (by decide)]; omega_using [hj]
  have hv25 : b.v .v25=ofVDwords w 0 := by
    rw [hb.v,ha.v,ha.gpr,hu.gpr]
    apply vec64_ext
    · change (setLane 0 64 0 w).extractLsb' (64*0) 64=_
      rw [extract_setLane64 0 w (i:=0) (j:=0) (by decide) (by decide),vdword_ofVDwords_0]
      rfl
    · change (setLane 0 64 0 w).extractLsb' (64*1) 64=_
      rw [extract_setLane64 0 w (i:=0) (j:=1) (by decide) (by decide),vdword_ofVDwords_1]
      rfl
  intro i hi
  have hi25 : vreg i≠.v25 := by
    change vreg i≠vreg 25
    rw [ne_eq,vreg_inj i (by omega_using [hi]) 25 (by decide)]; omega_using [hi]
  by_cases he : i=j
  · subst i
    rw [ht.v,hv25,hb.get _ hj25,ha.get _ hj25,hu.vec,hp j hj,pair_xor,xorWord_get _ _ _ _ hj,
      ite_eq_left rfl,show B[j]! ^^^ (0:BitVec 64)=B[j]! from BitVec.xor_zero]
  · have he' : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he
    rw [ht.get _ he',hb.get _ hi25,ha.get _ hi25,hu.vec,hp i hi,xorWord_get _ _ _ _ hi,ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailPadding.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def paddedState (A : Spec.Sha3.State) (j : Nat) : Spec.Sha3.State :=
  xorWord (xorWord A j 0x1f) 16 0x8000000000000000

/-- Adds SHAKE256 domain separation and the rate-block terminal bit. -/
theorem padding_ok {s : State} {A B : Spec.Sha3.State} {j : Nat}
    (hj : j<25) (hp : Pairs s A B) :
    WP isa (.block (paddingWord j 31 0 ++ paddingWord 16 0x8000 3)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t (paddedState A j) B := by
  rw [WP.block_append_iff]
  refine WP.mono (paddingWord_ok hj 31 0 (by decide) hp) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (paddingWord_ok (by decide) 0x8000 3 (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

/-- ML-DSA-65 has two words left after six complete rate blocks. -/
theorem tail_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<2, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block tail) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (paddedState (xorWords A s.mem (s.gpr .x5) 2) 2) B := by
  change WP isa (.block (((List.range 2).flatMap fun j => lowWord (vreg j) (8*j)) ++
    (paddingWord 2 31 0 ++ paddingWord 16 0x8000 3))) s _
  rw [WP.block_append_iff]
  refine WP.mono (lowWords_ok hp 2 (by decide) hin) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (padding_ok (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted RateBlock StreamOutput)

/-- Low-lane absorb performed after permutation `i`. The last permutation
has no following absorb; only its digest is serialized. -/
def absorbAfter (wlen : Nat) (m : Mem) (w1 : Addr) (i : Nat) (A : Spec.Sha3.State) : Spec.Sha3.State :=
  let n := (64+wlen)/136
  if i<n-1 then xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 17
  else if i=n-1 then
    if wlen=768 then paddedState (xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 2) 2
    else paddedState A 0
  else A

def lowRun (wlen : Nat) (m : Mem) (w1 : Addr) (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | i+1 => absorbAfter wlen m w1 i (Spec.Sha3.keccakF (lowRun wlen m w1 A i))

def fullCount (wlen i : Nat) : Nat := min i ((64+wlen)/136-1)

def inputPtr (wlen : Nat) (w1 : Addr) (i : Nat) : Addr :=
  w1+BitVec.ofNat 64 (72+136*fullCount wlen i)

/-- One newly serialized high-lane block leaves previous blocks unchanged. -/
theorem streamOutput_append {m m' : Mem} {p : Addr} {j : Nat} {B : Spec.Sha3.State}
    (hj : j<5) (h : StreamOutput m p 8 j B)
    (hn : RateBlock m' (p+BitVec.ofNat 64 (136*j)) 8 (permuted B (j+1)))
    (hf : Frame [⟨p+BitVec.ofNat 64 (136*j),136⟩] m m') :
    StreamOutput m' p 8 (j+1) B := by
  intro i hi
  by_cases he : i=j
  · subst i; exact hn
  · refine (h i (by omega_using [hi, he])).keep (by decide) hf ?_
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact VG.Proof.MlDsa.AArch64.Optimized.Resident.block_disjoint (by decide) (by omega_using [hi, he]) (by omega_using [hj])

/-- Absorbs depend only on the words in their readable input slice. -/
theorem xorWords_congr {A : Spec.Sha3.State} {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀j<n,m'.readW (p+BitVec.ofNat 64 (8*j)) 64=m.readW (p+BitVec.ofNat 64 (8*j)) 64) :
    xorWords A m' p n=xorWords A m p n := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get,
    VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get]
  by_cases hn : i<n
  · rw [ite_eq_left hn,ite_eq_left hn]
    exact congrArg (fun x=>A[i] ^^^ x) (h i hn)
  · rw [ite_eq_right hn,ite_eq_right hn]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted StreamOutput)

def coreRegs : List Reg := [.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x16]
def bufferBase (work : Addr) : Addr := work+256
def bufferRegion (work : Addr) : Region := ⟨bufferBase work,680⟩

structure CoreConfig (σ : State) (wlen : Nat) (w1 work : Addr) : Prop where
  length : wlen=768 ∨ wlen=1024
  workPtr : σ.gpr .x19=work
  readable : ∀d n,d+n≤wlen→InRegions (σ.rd++σ.wr) (w1+BitVec.ofNat 64 d) n
  writable : ∀d n,d+n≤2048→InRegions σ.wr (work+BitVec.ofNat 64 d) n
  separate : (Region.mk w1 wlen).Disjoint (bufferRegion work)

structure CoreEnv (σ : State) (wlen : Nat) (w1 work : Addr)
    (B : Spec.Sha3.State) (i emitted : Nat) (s : State) : Prop where
  keep : RegKeep coreRegs σ s
  frame : Frame [bufferRegion work] σ.mem s.mem
  ptr : s.gpr .x5=inputPtr wlen w1 i
  output : StreamOutput s.mem (bufferBase work) 8 (min emitted 5) B

structure CoreState (σ : State) (wlen : Nat) (w1 work : Addr)
    (A B : Spec.Sha3.State) (i : Nat) (s : State) : Prop
    extends CoreEnv σ wlen w1 work B i i s where
  pairs : Pairs s (lowRun wlen σ.mem w1 A i) (permuted B i)

structure RoundState (σ : State) (wlen : Nat) (w1 work : Addr)
    (A B : Spec.Sha3.State) (i emitted : Nat) (s : State) : Prop
    extends CoreEnv σ wlen w1 work B i emitted s where
  pairs : Pairs s (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) (permuted B (i+1))

theorem buffer_addr (work : Addr) (i : Nat) :
    work+BitVec.ofNat 64 (256+136*i)=bufferBase work+BitVec.ofNat 64 (136*i) := by
  rw [BitVec.ofNat_add,← BitVec.add_assoc]
  rfl

theorem CoreEnv.readable {σ s : State} {wlen : Nat} {w1 work : Addr}
    {B : Spec.Sha3.State} {i emitted d n : Nat} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hc : CoreConfig σ wlen w1 work) (hd : d+n≤wlen) :
    InRegions (s.rd++s.wr) (w1+BitVec.ofNat 64 d) n := by
  rw [h.keep.rd,h.keep.wr]
  exact hc.readable d n hd

theorem CoreEnv.word {σ s : State} {wlen : Nat} {w1 work : Addr}
    {B : Spec.Sha3.State} {i emitted d : Nat} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hc : CoreConfig σ wlen w1 work) (hd : d+8≤wlen) :
    s.mem.readW (w1+BitVec.ofNat 64 d) 64=σ.mem.readW (w1+BitVec.ofNat 64 d) 64 := by
  have hw : wlen≤1024 := by rcases hc.length with rfl|rfl <;> decide
  exact h.frame.readW (r:=⟨w1,wlen⟩) (Offset.contains_base w1 hd (by omega_using [hd, hw]))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hc.separate) (by decide)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

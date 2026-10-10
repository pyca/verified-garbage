import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailWord
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.AbsorbBlock

/-! ## From `CommitTailAbsorb.lean` -/

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
    rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]
    omega
  refine WP.mono (lowWord_ok h25 ⟨by omega,by omega⟩ (by rw [h5]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega),hm,h5,pair_xor]
    simp only [getElem!_pos (xorWords A m p j) j (by omega),
      getElem!_pos (xorWords A m p (j+1)) j (by omega), getElem!_pos B j (by omega)]
    rw [xorWords_get _ _ _ _ _ (by omega),xorWords_get _ _ _ _ _ (by omega)]
    simp only [Nat.lt_irrefl,ite_false,show j<j+1 by omega,ite_true]
    rw [show A[j] ^^^ (0:BitVec 64)=A[j] from BitVec.xor_zero,
      show B[j] ^^^ (0:BitVec 64)=B[j] from BitVec.xor_zero]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    have hi25 : vreg i≠.v25 := by
      change vreg i≠vreg 25
      rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]
      omega
    rw [hv _ hij hi25,hp i hi]
    have hh : (xorWords A m p j)[i]! = (xorWords A m p (j+1))[i]! := by
      simp only [getElem!_pos (xorWords A m p j) i hi,
        getElem!_pos (xorWords A m p (j+1)) i hi]
      rw [xorWords_get _ _ _ _ _ hi,xorWords_get _ _ _ _ _ hi]
      have hc : (i<j)=(i<j+1) := propext (by omega)
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
    refine WP.mono (lowWord_step (by omega) hm (hk.gpr .x5 (by decide)) hp ?_)
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
      rw [ne_eq,vreg_inj i (by omega) (j+1) (by omega)]; exact he
    simp only [he,ite_false,low,ht.get _ he']
    by_cases he0 : i=j
    · subst i
      simp only [ite_true,ha.v]
      rfl
    · have he0' : vreg i≠vreg j := by
        rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he0
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
    refine WP.mono (loadPair_ok (j:=start+2*j) (by omega) ⟨by omega,by omega⟩ hin')
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
      rw [ite_eq_left rfl,ite_eq_left (by omega),show start+2*j+1-start=2*j+1 by omega]
    · rw [ite_eq_right he1]
      by_cases he0 : i=start+2*j
      · subst i
        rw [ite_eq_left rfl,ite_eq_left (by omega),show start+2*j-start=2*j by omega]
      · rw [ite_eq_right he0,ht.lanes i hi]
        have he : (start≤i ∧ i<start+2*j)↔(start≤i ∧ i<start+2*(j+1)) := by omega
        simp only [he]
  · intro i hi
    rw [ite_eq_right (by omega)]

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
      rw [ne_eq,vreg_inj i (by omega) 16 (by decide)]
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
      rw [ite_eq_left (by omega)]
      change vdword (u.v (vreg (17+j))) 0=0
      rw [hu.v]
      rfl
    · have he' : vreg i≠vreg (17+j) := by
        rw [ne_eq,vreg_inj i (by omega) (17+j) (by omega)]; exact he
      change vdword (u.v (vreg i)) 0=_
      rw [hu.get _ he']
      change low t (vreg i)=_
      rw [ht.lanes i hi]
      have hh : (17≤i ∧ i<17+j)↔(17≤i ∧ i<17+(j+1)) := by omega
      simp only [hh]
  · intro i hi
    rw [ite_eq_right (by omega)]

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
      · rw [ite_eq_right (by omega : ¬ (17≤i ∧ i<17+8)),
          ite_eq_right (by omega : ¬ i=16),
          ite_eq_right (by omega : ¬ (8≤i ∧ i<8+2*4)),
          ite_eq_left (by omega : 0≤i ∧ i<2*4),ite_eq_left h8]
      · by_cases h16 : i<16
        · rw [ite_eq_right (by omega : ¬ (17≤i ∧ i<17+8)),
            ite_eq_right (by omega : ¬ i=16),
            ite_eq_left (by omega : 8≤i ∧ i<8+2*4),ite_eq_right h8,
            ite_eq_left (by omega : i<17)]
        · by_cases he : i=16
          · subst i
            rw [ite_eq_right (by decide : ¬ (17≤16 ∧ 16<17+8)),ite_eq_left rfl,
              ite_eq_right (by decide : ¬ (16:Nat)<8),ite_eq_left (by decide : (16:Nat)<17)]
            rfl
          · rw [ite_eq_left (by omega : 17≤i ∧ i<17+8),ite_eq_right h8,
              ite_eq_right (by omega : ¬ i<17)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

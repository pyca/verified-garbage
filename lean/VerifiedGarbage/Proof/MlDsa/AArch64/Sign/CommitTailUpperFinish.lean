import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailWord
import VerifiedGarbage.Proof.Framework.Range

/-! ## From `CommitTailUpperWord.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)

/-- Inserting one seed word into the second SHAKE stream preserves the
complete commitment state in the first lanes. -/
theorem upperWord_ok {s : State} {r : VReg} {off : Nat}
    (ho : off%8=0 ∧ off<4096*8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldr .x .x7 .x4 off,.vop (.ins .d2 r 1 .x7)]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      (∀v,v≠r → t.v v=s.v v) ∧
      t.v r=setLane (s.v r) 64 1 (s.mem.readW (s.gpr .x4+BitVec.ofNat 64 off) 64) := by
  refine wp_ldr ho rfl hin fun a ha =>
    wp_vop (d:=r) rfl fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.upd ha).trans (RegKeep.vupd ht)).mono (by simp),
    ht.mem.trans ha.mem,?_,?_⟩
  · intro v hv
    rw [ht.get v hv,ha.vec]
  · rw [ht.v,ha.vec,ha.gpr]

/-- Both 64-bit lane values after a high-lane insert. -/
theorem upper_pair (a b w : BitVec 64) :
    setLane (ofVDwords a b) 64 1 w=ofVDwords a w := by
  apply vec64_ext
  · change (setLane (ofVDwords a b) 64 1 w).extractLsb' (64*0) 64=_
    rw [extract_setLane64 _ w (i:=1) (j:=0) (by decide) (by decide),
      vdword_ofVDwords_0]
    exact vdword_ofVDwords_0 a b
  · change (setLane (ofVDwords a b) 64 1 w).extractLsb' (64*1) 64=_
    rw [extract_setLane64 _ w (i:=1) (j:=1) (by decide) (by decide),vdword_ofVDwords_1]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailUpper.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def seedPrefix (B : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<n then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64 else B[i]

theorem seedPrefix_get (B : Spec.Sha3.State) (m : Mem) (p : Addr) (n i : Nat) (hi : i<25) :
    (seedPrefix B m p n)[i]! = if i<n then m.readW (p+BitVec.ofNat 64 (8*i)) 64 else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [seedPrefix,Vector.getElem_ofFn,Fin.getElem_fin]

/-- Seed loads only replace the high lanes. -/
theorem upperWord_step {s : State} {A B : Spec.Sha3.State} {m : Mem} {p : Addr} {j : Nat}
    (hj : j<8) (hm : s.mem=m) (h4 : s.gpr .x4=p)
    (hp : Pairs s A (seedPrefix B m p j))
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block [.ldr .x .x7 .x4 (8*j),.vop (.ins .d2 (vreg j) 1 .x7)]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=m ∧ Pairs t A (seedPrefix B m p (j+1)) := by
  refine WP.mono (upperWord_ok ⟨by omega,by omega⟩ (by rw [h4]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega),upper_pair,hm,h4,seedPrefix_get _ _ _ _ _ (by omega),ite_eq_left (by omega)]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    rw [hv _ hij,hp i hi,seedPrefix_get _ _ _ _ _ hi,seedPrefix_get _ _ _ _ _ hi]
    have hc : (i<j)↔(i<j+1) := by omega
    simp only [hc]

/-- All eight seed words are loaded without disturbing the commitment. -/
theorem upperWords_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block ((List.range 8).flatMap fun j =>
      ([.ldr .x .x7 .x4 (8*j),.vop (.ins .d2 (vreg j) 1 .x7)] : List Instr))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t A (seedPrefix B s.mem (s.gpr .x4) 8) := by
  let I := fun j t => RegKeep [.x7] s t ∧ t.mem=s.mem ∧
    Pairs t A (seedPrefix B s.mem (s.gpr .x4) j)
  have hz : seedPrefix B s.mem (s.gpr .x4) 0=B := by
    apply Vector.ext
    intro i hi
    simp only [seedPrefix,Vector.getElem_ofFn,Nat.not_lt_zero,ite_false,Fin.getElem_fin]
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) 8 (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (upperWord_step hj hm (hk.gpr .x4 (by decide)) hp ?_)
      fun u ⟨hk',hm',hp'⟩ => ⟨(hk.trans hk').mono (by simp),hm',hp'⟩
    rw [hk.rd,hk.wr]
    exact hin j hj
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hz]; exact hp⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailInsert.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def replaceWord (B : Spec.Sha3.State) (j : Nat) (w : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val=j then w else B[i]

theorem replaceWord_get (B : Spec.Sha3.State) (j : Nat) (w : BitVec 64)
    (i : Nat) (hi : i<25) :
    (replaceWord B j w)[i]! = if i=j then w else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [replaceWord,Vector.getElem_ofFn,Fin.getElem_fin]

/-- A single high-lane insertion preserves every scalar register and the
independent low-lane SHAKE state. -/
theorem insertHigh_ok {s : State} {A B : Spec.Sha3.State} {j : Nat} {r : Reg}
    (hj : j<25) (hp : Pairs s A B) :
    WP isa (.block [.vop (.ins .d2 (vreg j) 1 r)]) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (replaceWord B j (s.gpr r)) := by
  refine wp_vop (d:=vreg j) rfl fun t ht => WP.block_nil_iff.mpr
    ⟨RegKeep.vupd ht,ht.mem,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht.v,hp j hj,upper_pair,replaceWord_get _ _ _ _ hj,ite_eq_left rfl]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    rw [ht.get _ hij,hp i hi,replaceWord_get _ _ _ _ hi,ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailClear.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def clearPrefix (B : Spec.Sha3.State) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => if 8≤i.val ∧ i.val<8+n then 0 else B[i]

theorem clearPrefix_get (B : Spec.Sha3.State) (n i : Nat) (hi : i<25) :
    (clearPrefix B n)[i]! = if 8≤i ∧ i<8+n then 0 else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [clearPrefix,Vector.getElem_ofFn,Fin.getElem_fin]

theorem clearPrefix_step (B : Spec.Sha3.State) (j : Nat) :
    replaceWord (clearPrefix B j) (8+j) 0=clearPrefix B (j+1) := by
  apply Vector.ext
  intro i hi
  rw [← VG.Proof.Sha3.getElem!_eq _ hi,← VG.Proof.Sha3.getElem!_eq _ hi,
    replaceWord_get _ _ _ _ hi,clearPrefix_get _ _ _ hi,clearPrefix_get _ _ _ hi]
  by_cases he : i=8+j
  · subst i
    rw [ite_eq_left rfl,ite_eq_left (by omega)]
  · have hc : (8≤i ∧ i<8+j)↔(8≤i ∧ i<8+(j+1)) := by omega
    simp only [he,ite_false,hc]

/-- Clears the unused second-lane seed words, preserving the first stream. -/
theorem clearHigh_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (h7 : s.gpr .x7=0) :
    WP isa (.block ((List.range 17).map fun j => .vop (.ins .d2 (vreg (8+j)) 1 .x7))) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B 17) := by
  let I := fun j t => RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B j)
  have hz : clearPrefix B 0=B := by
    apply Vector.ext
    intro i hi
    simp only [clearPrefix,Vector.getElem_ofFn,Fin.getElem_fin,Nat.add_zero]
    rw [ite_eq_right (by omega)]
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) 17 (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (insertHigh_ok (by omega) hp) fun u ⟨hk',hm',hp'⟩ => ?_
    refine ⟨(hk.trans hk').mono (by simp),hm'.trans hm,?_⟩
    rw [hk.gpr .x7 (by simp),h7,clearPrefix_step] at hp'
    exact hp'
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hz]; exact hp⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailNonce.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (WP.cons)

/-- The helper accepts a nonce word and absorbs precisely its low two bytes. -/
def nonceWord (k : BitVec 64) : BitVec 64 := ((k <<< 48) >>> 48)+0x1f0000

theorem nonce_ok (s : State) :
    WP isa (.block [.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,
      .movz .x .x8 31 1,.add .x .x7 .x7 .x8]) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      t.gpr .x7=nonceWord (s.gpr .x5) := by
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.block_nil_iff.mpr ?_))))
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl⟩,rfl,rfl,?_⟩
  · have h7 : r≠.x7 := fun h => hr (by simp only [h,List.mem_cons,true_or])
    have h8 : r≠.x8 := fun h => hr (by simp [h])
    simp only [RegUpd.gpr_write,h7,h8,ite_false]
  · simp only [RegUpd.gpr_write_self,RegUpd.gpr_write,State.read,Size.bits,
      BitVec.setWidth_eq,reduceCtorEq,ite_false]
    rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailUpperFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (WP.cons)

def upperFinish : List Instr :=
  [.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,.movz .x .x8 31 1,.add .x .x7 .x7 .x8,
    .vop (.ins .d2 .v8 1 .x7),.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)]

private theorem pad7_ok (s : State) :
    WP isa (.block [.movz .x .x7 0x8000 3]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ t.v=s.v ∧ t.gpr .x7=0x8000000000000000 := by
  refine WP.cons rfl (WP.block_nil_iff.mpr ?_)
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
  have hr' : r≠.x7 := by simpa using hr
  simp only [RegUpd.gpr_write,hr',ite_false]

/-- Adds the two-byte nonce and SHAKE padding to the second stream. -/
theorem upperFinish_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block upperFinish) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧
      Pairs t A (replaceWord (replaceWord B 8 (nonceWord (s.gpr .x5))) 16 0x8000000000000000) := by
  change WP isa (.block (([.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,
    .movz .x .x8 31 1,.add .x .x7 .x7 .x8] : List Instr) ++
    [.vop (.ins .d2 .v8 1 .x7),.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (nonce_ok s) fun a ⟨ha,hma,hva,ea⟩ => ?_
  have hpa : Pairs a A B := by intro i hi; rw [hva]; exact hp i hi
  change WP isa (.block (([.vop (.ins .d2 .v8 1 .x7)] : List Instr) ++
    [.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)])) a _
  rw [WP.block_append_iff]
  refine WP.mono (insertHigh_ok (j:=8) (by decide) hpa) fun b ⟨hb,hmb,hpb⟩ => ?_
  rw [ea] at hpb
  change WP isa (.block (([.movz .x .x7 0x8000 3] : List Instr) ++
    [.vop (.ins .d2 .v16 1 .x7)])) b _
  rw [WP.block_append_iff]
  refine WP.mono (pad7_ok b) fun c ⟨hc,hmc,hvc,ec⟩ => ?_
  have hpc : Pairs c A (replaceWord B 8 (nonceWord (s.gpr .x5))) := by
    intro i hi; rw [hvc]; exact hpb i hi
  refine WP.mono (insertHigh_ok (j:=16) (by decide) hpc) fun t ⟨ht,hmt,hpt⟩ => ?_
  rw [ec] at hpt
  exact ⟨(((ha.trans hb).trans hc).trans ht).mono (by simp),
    hmt.trans (hmc.trans (hmb.trans hma)),hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBlock
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRate
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CommitTail
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailModel
import VerifiedGarbage.Spec.MlDsa

/-! ### `MlDsa.AArch64.Sign.CommitTailSeed`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Sign.CommitTailUpperFinish`, which only this module used -/

section

/-! ## From `CommitTailUpperWord.lean` -/

@[expose] public section

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
  refine WP.mono (upperWord_ok ⟨by omega_using [],by omega_using [hj]⟩ (by rw [h4]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega_using [hj]),upper_pair,hm,h4,seedPrefix_get _ _ _ _ _ (by omega_using [hj]),ite_eq_left (by omega_using [])]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he
    rw [hv _ hij,hp i hi,seedPrefix_get _ _ _ _ _ hi,seedPrefix_get _ _ _ _ _ hi]
    obtain hc : (i<j)↔(i<j+1) := by omega_using [he]
    simp only [hc]

/-- All eight seed words are loaded without disturbing the commitment. -/
theorem upperWords_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block ((List.range 8).flatMap fun j =>
      ([.ldr .x .x7 .x4 (8*j),.vop (.ins .d2 (vreg j) 1 .x7)] : List Instr))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t A (seedPrefix B s.mem (s.gpr .x4) 8) := by
  let I := fun j t => RegKeep [.x7] s t ∧ t.mem=s.mem ∧
    Pairs t A (seedPrefix B s.mem (s.gpr .x4) j)
  obtain hz : seedPrefix B s.mem (s.gpr .x4) 0=B := by
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
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega_using [hi]) j (by omega_using [hj])]; exact he
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
    rw [ite_eq_left rfl,ite_eq_left (by omega_using [])]
  · have hc : (8≤i ∧ i<8+j)↔(8≤i ∧ i<8+(j+1)) := by omega_using [he]
    simp only [he,ite_false,hc]

/-- Clears the unused second-lane seed words, preserving the first stream. -/
theorem clearHigh_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (h7 : s.gpr .x7=0) :
    WP isa (.block ((List.range 17).map fun j => .vop (.ins .d2 (vreg (8+j)) 1 .x7))) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B 17) := by
  let I := fun j t => RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (clearPrefix B j)
  obtain hz : clearPrefix B 0=B := by
    apply Vector.ext
    intro i hi
    simp only [clearPrefix,Vector.getElem_ofFn,Fin.getElem_fin,Nat.add_zero]
    rw [ite_eq_right (by omega_using [])]
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) 17 (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (insertHigh_ok (by omega_using [hj]) hp) fun u ⟨hk',hm',hp'⟩ => ?_
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
    obtain h8 : r≠.x8 := fun h => hr (by simp [h])
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
  obtain hr' : r≠.x7 := by simpa using hr
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
  obtain hpa : Pairs a A B := by intro i hi; rw [hva]; exact hp i hi
  change WP isa (.block (([.vop (.ins .d2 .v8 1 .x7)] : List Instr) ++
    [.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)])) a _
  rw [WP.block_append_iff]
  refine WP.mono (insertHigh_ok (j:=8) (by decide) hpa) fun b ⟨hb,hmb,hpb⟩ => ?_
  rw [ea] at hpb
  change WP isa (.block (([.movz .x .x7 0x8000 3] : List Instr) ++
    [.vop (.ins .d2 .v16 1 .x7)])) b _
  rw [WP.block_append_iff]
  refine WP.mono (pad7_ok b) fun c ⟨hc,hmc,hvc,ec⟩ => ?_
  obtain hpc : Pairs c A (replaceWord B 8 (nonceWord (s.gpr .x5))) := by
    intro i hi; rw [hvc]; exact hpb i hi
  refine WP.mono (insertHigh_ok (j:=16) (by decide) hpc) fun t ⟨ht,hmt,hpt⟩ => ?_
  rw [ec] at hpt
  exact ⟨(((ha.trans hb).trans hc).trans ht).mono (by simp),
    hmt.trans (hmc.trans (hmb.trans hma)),hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end

/-! ### `MlDsa.AArch64.Sign.CommitTailSqueezeRate`, which only this module used -/

section

/-! ## From `CommitTailSqueezeWord.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep trn2_dwords stateReg_ne)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Proof.Sha3.AArch64 (WP.cons wp_str Upd)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Serialize a pair of high lanes without spilling the resident state. -/
theorem highPair_ok {s : State} {p : Addr} {i : Nat}
    (hi : i<8) (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block [.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
      .strq .v26 .x10 (16*i)]) s fun t => SqueezeKeep s t ∧
      t.mem=s.mem.write (p+BitVec.ofNat 64 (16*i)) 16
        (ofVDwords (vdword (s.v (vreg (2*i))) 1) (vdword (s.v (vreg (2*i+1))) 1)) := by
  refine wp_vop (d:=.v26) rfl fun a ha =>
    wp_strq ⟨by omega_using [],by omega_using [hi]⟩ (by rw [ha.gpr,hp]) (by rw [ha.wr]; exact hout)
      fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ _ => by rw [ht.gpr,ha.gpr],fun r h26 _ => by rw [ht.v,ha.get r h26],
    ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp⟩,?_⟩
  rw [ht.mem,ha.v,ha.mem,trn2_dwords]

/-- The final high rate word is stored without touching any resident lane. -/
theorem highLast_ok {s : State} {p : Addr} (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+128) 8) :
    WP isa (.block [.umov .x .x7 .v16 1,.str .x .x7 .x10 128]) s fun t =>
      SqueezeKeep s t ∧ t.mem=s.mem.writeW (p+128) (vdword (s.v .v16) 1) := by
  refine WP.cons (s':=s.write .x .x7 (vdword (s.v .v16) 1)) rfl ?_
  obtain h := Upd.write64 s .x7 (vdword (s.v .v16) 1)
  refine wp_str (by decide) (by rw [h.other .x10 (by decide),hp])
    (by rw [h.wr]; exact hout) fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ hr => (congrFun ht.gpr r).trans (h.other r hr),
    fun r _ _ => by rw [ht.vec,h.vec],ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩,?_⟩
  rw [ht.mem,h.gpr,h.mem]
  rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSqueezeRate.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep RatePairs RateBlock)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

theorem highPairs_ok {s : State} {p : Addr} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (hptr : s.gpr .x10=p)
    (hout : ∀i<8, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      ([.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
        .strq .v26 .x10 (16*i)] : List Instr))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RatePairs t.mem p 8 B ∧ Frame [⟨p,128⟩] s.mem t.mem := by
  refine WP.mono (wp_range_flatMap (M:=isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem p k B ∧ Frame [⟨p,128⟩] s.mem t.mem)
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,Frame.refl _ _⟩)
    fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2⟩
  obtain hpt := ht.1.pairs hp
  refine WP.mono (highPair_ok hk ((ht.1.gpr .x10 (by decide) (by decide)).trans hptr)
    (by rw [ht.1.wr]; exact hout k hk)) fun u hu => ?_
  obtain hm : u.mem=t.mem.write (p+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega_using [hk]),hpt _ (by omega_using [hk]),vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_⟩
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])) (by decide)]
      exact ht.2.1 i (by omega_using [hi, he])
  · rw [hm]
    exact ht.2.2.write (r:=⟨p,128⟩) (by simp) _ (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))

/-- One 136-byte high-lane squeeze preserves both resident permutation states. -/
theorem highRate_ok {s : State} {p : Addr} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) (hptr : s.gpr .x10=p)
    (hout : ∀i<8, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16)
    (hlast : InRegions s.wr (p+128) 8) :
    WP isa (.block (((List.range 8).flatMap fun i =>
      ([.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
        .strq .v26 .x10 (16*i)] : List Instr)) ++
      ([.umov .x .x7 .v16 1,.str .x .x7 .x10 128] : List Instr))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RateBlock t.mem p 8 B ∧ Frame [⟨p,136⟩] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (highPairs_ok hp hptr hout) fun a ha => ?_
  refine WP.mono (highLast_ok ((ha.1.gpr .x10 (by decide) (by decide)).trans hptr)
    (by rw [ha.1.wr]; exact hlast)) fun t ht => ?_
  obtain hm : t.mem=a.mem.writeW (p+128) B[16]! := by
    obtain hp16 : a.v .v16=ofVDwords A[16]! B[16]! := ha.2.1 16 (by decide)
    rw [ht.2,hp16,vdword_ofVDwords_1]
  refine ⟨ha.1.trans ht.1,ht.1.pairs ha.2.1,⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hm]
    change (a.mem.write (p+BitVec.ofNat 64 128) 8 B[16]!).read (p+BitVec.ofNat 64 (16*i)) 16=_
    rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=128) (k:=8)
      (by omega_using [hi]) (by omega_using [hi]) (by omega_using [])) (by decide)]
    exact ha.2.2.1 i hi
  · change t.mem.readW (p+128) 64=B[16]!
    rw [hm,Mem.readW_writeW_self64]
  · rw [hm]
    obtain hf : Frame [⟨p,136⟩] s.mem a.mem := ha.2.2.2.sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨p,136⟩,by simp,by simpa using Offset.sub_base p (d:=0) (n:=128) (k:=136) (by decide)⟩)
    exact hf.writeW (r:=⟨p,136⟩) (by simp) _ (Offset.contains_base p (by decide) (by decide))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end

/-! ## The core loop -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CommitTailInitial.lean`, which only this module imported.
section

/-! ## From `CommitTailUpperInit.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_movz)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def seedNonceState (m : Mem) (p : Addr) (k : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<8 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
    else if i.val=8 then nonceWord k else if i.val=16 then 0x8000000000000000 else 0

theorem seedNonceState_eq (B : Spec.Sha3.State) (m : Mem) (p : Addr) (k : BitVec 64) :
    replaceWord (replaceWord (clearPrefix (seedPrefix B m p 8) 17) 8 (nonceWord k))
      16 0x8000000000000000 = seedNonceState m p k := by
  apply Vector.ext
  intro i hi
  rw [← VG.Proof.Sha3.getElem!_eq _ hi,replaceWord_get _ _ _ _ hi,
    replaceWord_get _ _ _ _ hi,clearPrefix_get _ _ _ hi,seedPrefix_get _ _ _ _ _ hi]
  simp only [seedNonceState,Vector.getElem_ofFn]
  by_cases h8 : i<8
  · simp only [h8,ite_true,show ¬ i=16 by omega_using [h8],show ¬ i=8 by omega_using [h8],
      show ¬ (8≤i ∧ i<8+17) by omega_using [h8],ite_false]
  · by_cases he8 : i=8
    · subst i; simp only [ite_true,ite_false,Nat.reduceLT,ite_eq_right (by decide : ¬ (8:Nat)=16)]
    · by_cases he16 : i=16
      · subst i; simp only [ite_true,ite_false,Nat.reduceLT,ite_eq_right (by decide : ¬ (16:Nat)=8)]
      · simp only [h8,he8,he16,ite_false]
        rw [ite_eq_left (by omega_using [hi, h8])]

/-- Initializes the mask seed in the second lane while preserving the
commitment state in every first lane. -/
theorem upperInit_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block upperInit) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧
      Pairs t A (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) := by
  change WP isa (.block (((List.range 8).flatMap fun i =>
    ([.ldr .x .x7 .x4 (8*i),.vop (.ins .d2 (vreg i) 1 .x7)] : List Instr)) ++
    ([.movz .x .x7 0 0] ++
    ((List.range 17).map fun i => .vop (.ins .d2 (vreg (8+i)) 1 .x7)) ++ upperFinish))) s _
  rw [WP.block_append_iff]
  refine WP.mono (upperWords_ok hp hin) fun a ⟨ha,hma,hpa⟩ => ?_
  change WP isa (.block (.movz .x .x7 0 0 ::
    (((List.range 17).map fun i => .vop (.ins .d2 (vreg (8+i)) 1 .x7)) ++ upperFinish))) a _
  refine wp_movz fun b hb => ?_
  obtain hpb : Pairs b A (seedPrefix B s.mem (s.gpr .x4) 8) := by
    intro i hi; rw [hb.vec]; exact hpa i hi
  rw [WP.block_append_iff]
  refine WP.mono (clearHigh_ok hpb (by rw [hb.gpr]; rfl)) fun c ⟨hc,hmc,hpc⟩ => ?_
  refine WP.mono (upperFinish_ok hpc) fun t ⟨ht,hmt,hpt⟩ => ?_
  obtain h5 : c.gpr .x5=s.gpr .x5 :=
    (hc.gpr .x5 (by simp)).trans ((hb.other .x5 (by decide)).trans (ha.gpr .x5 (by decide)))
  rw [h5,seedNonceState_eq] at hpt
  exact ⟨(((ha.trans (RegKeep.upd hb)).trans hc).trans ht).mono (by simp),
    hmt.trans (hmc.trans (hb.mem.trans hma)),hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailInitial.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low Lanes)
open VG.Proof.Sha3.AArch64 (WP.cons)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def upperState (s : State) : Spec.Sha3.State :=
  Vector.ofFn fun i => vdword (s.v (vreg i.val)) 1

theorem lanes_pairs {s : State} {A : Spec.Sha3.State} (hp : Lanes s A) :
    Pairs s A (upperState s) := by
  intro i hi
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq _ hi]
  simp only [upperState,Vector.getElem_ofFn]
  apply vec64_ext
  · rw [vdword_ofVDwords_0]
    exact hp i hi
  · rw [vdword_ofVDwords_1]

/-- Both independent SHAKE streams are initialized, with the next
commitment-rate block pointer positioned immediately after the first. -/
theorem initial_ok {s : State}
    (hmu : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀j<4, InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*j)) 16)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x1+64) 8)
    (hseed : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block (first++upperInit++([.addImm .x .x5 .x1 72] : List Instr))) s fun t =>
      RegKeep [.x5,.x6,.x7,.x8] s t ∧ t.mem=s.mem ∧ t.gpr .x5=s.gpr .x1+72 ∧
      Pairs t (firstState s.mem (s.gpr .x0) (s.gpr .x1))
        (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (first_ok hmu hw hl) fun a ⟨ha,hma,hpa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (upperInit_ok (lanes_pairs hpa) ?_) fun b ⟨hb,hmb,hpb⟩ => ?_
  · intro j hj
    rw [ha.rd,ha.wr,ha.gpr .x4 (by decide)]
    exact hseed j hj
  · rw [hma,ha.gpr .x4 (by decide),ha.gpr .x5 (by decide)] at hpb
    refine WP.cons rfl (WP.block_nil_iff.mpr ?_)
    refine ⟨?_,hmb.trans hma,?_,hpb⟩
    · refine ⟨fun r hr => ?_,hb.rd.trans ha.rd,hb.wr.trans ha.wr,hb.sp.trans ha.sp⟩
      obtain h5 : r≠.x5 := fun he => hr (by simp [he])
      simp only [RegUpd.gpr_write,h5,ite_false]
      exact (hb.gpr r (fun hh => hr (by simp_all))).trans
        (ha.gpr r (fun hh => hr (by simp_all)))
    · simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq]
      rw [hb.gpr .x1 (by decide),ha.gpr .x1 (by decide)]
      rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
end

end

-- Formerly `VerifiedGarbage/Proof/Sha3/AArch64/Neon/HwRounds.lean`, which only this module imported.
section

section

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem rounds2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block rounds) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold rounds
  refine wp_range_flatMap (M := isa)
    (fun k t => CoreKeep s t ∧ Pairs t
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k t hk ⟨ht,hpt⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (round2_ok hpt hk) fun u ⟨hu,hpu⟩ => ⟨ht.trans hu,?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpu
end VG.Proof.Sha3.AArch64.Neon.Hw
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_addImm wp_subImm wp_movz)
open VG.Proof.MlKem.AArch64 (eval_zero eval_nonzero)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep)
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

/-- Writing a core register other than the input pointer keeps the core's
environment. -/
theorem CoreEnv.upd {σ s t : State} {wlen : Nat} {w1 work : Addr} {B : Spec.Sha3.State}
    {i emitted : Nat} {d : Reg} {v : BitVec 64} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hu : Upd s t d v) (hd : d ∈ coreRegs) (h5 : d ≠ .x5) :
    CoreEnv σ wlen w1 work B i emitted t := by
  refine ⟨(h.keep.trans (RegKeep.upd hu)).mono fun r hr => ?_,?_,?_,?_⟩
  · rcases List.mem_append.mp hr with hr|hr
    · exact hr
    · rw [List.mem_singleton.mp hr]; exact hd
  · rw [hu.mem]; exact h.frame
  · rw [hu.other .x5 (Ne.symm h5)]; exact h.ptr
  · rw [hu.mem]; exact h.output

theorem pairs_upd {s t : State} {A B : Spec.Sha3.State} {d : Reg} {v : BitVec 64}
    (h : Pairs s A B) (hu : Upd s t d v) : Pairs t A B := by
  intro i hi; rw [hu.vec]; exact h i hi

/-- The loop's registers before the permutation `i`, with `k` permutations
already counted down in `x11`. -/
structure LoopRegs (wlen : Nat) (work : Addr) (k i : Nat) (s : State) : Prop where
  left : s.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-k)
  masks : s.gpr .x12=BitVec.ofNat 64 (5-min i 5)
  out : s.gpr .x10=work+BitVec.ofNat 64 (256+136*min i 5)

theorem LoopRegs.keep {wlen k i : Nat} {work : Addr} {s t : State} {rs : List Reg}
    (h : LoopRegs wlen work k i s) (hk : RegKeep rs s t)
    (hrs : .x10 ∉ rs ∧ .x11 ∉ rs ∧ .x12 ∉ rs) : LoopRegs wlen work k i t :=
  ⟨(hk.gpr .x11 hrs.2.1).trans h.left,(hk.gpr .x12 hrs.2.2).trans h.masks,
    (hk.gpr .x10 hrs.1).trans h.out⟩

/-- Each permutation advances both unrelated sponge states. -/
theorem coreRound_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.block rounds) s fun t =>
      RoundState σ wlen w1 work A B i i t ∧ RegKeep [.x16] s t := by
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok h.pairs)
    fun t ⟨hk,hp⟩ => ?_
  obtain hl : RegKeep [.x16] s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by simp [he])),hk.rd,hk.wr,hk.sp⟩
  refine ⟨⟨⟨(h.keep.trans hl).mono (by simp [coreRegs]),?_,?_,?_⟩,hp⟩,hl⟩
  · rw [hk.mem]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]; exact h.ptr
  · rw [hk.mem]; exact h.output

/-- Only the first five permutations serialize the independent mask stream. -/
theorem coreEmit_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i i s) (hl : LoopRegs wlen work i i s) :
    WP isa (.ite (.zero .x .x12) (.block []) (.block squeezeNext)) s fun t =>
      RoundState σ wlen w1 work A B i (i+1) t ∧ LoopRegs wlen work i (i+1) t := by
  by_cases hi : i<5
  · have h12 : s.gpr .x12=BitVec.ofNat 64 (5-i) := by
      rw [hl.masks,Nat.min_eq_left (by omega_arith)]
    obtain h10 : s.gpr .x10=work+BitVec.ofNat 64 (256+136*i) := by
      rw [hl.out,Nat.min_eq_left (by omega_arith)]
    refine WP.ite false (by
      rw [eval_zero,h12]
      exact congrArg some (beq_eq_false_iff_ne.mpr fun he => by
        have := congrArg BitVec.toNat he
        change _=(BitVec.ofNat 64 0).toNat at this
        simp only [BitVec.toNat_ofNat] at this
        omega_arith)) (fun hb => Bool.noConfusion hb) fun _ => ?_
    unfold squeezeNext
    rw [show ∀ (L : List Instr) (a b c d : Instr), L++[a,b,c,d]=(L++[a,b])++[c,d] from
      fun _ _ _ _ _ => by simp,WP.block_append_iff]
    refine WP.mono (highRate_ok h.pairs h10 (fun j hj => ?_) ?_) fun a ⟨hk,hp,ho,hf⟩ => ?_
    · rw [h.keep.wr,Offset.add_add]
      exact hc.writable _ _ (by omega_arith)
    · rw [h.keep.wr]
      change InRegions σ.wr ((work+BitVec.ofNat 64 (256+136*i))+BitVec.ofNat 64 128) 8
      rw [Offset.add_add]
      exact hc.writable _ _ (by omega_arith)
    obtain hka : RegKeep [.x6,.x7] s a :=
      ⟨fun r hr => hk.gpr r (fun he => hr (by simp [he])) (fun he => hr (by simp [he])),
        hk.rd,hk.wr,hk.sp⟩
    refine wp_addImm (by decide) fun b hb => wp_subImm (by decide) fun t ht =>
      WP.block_nil ?_
    obtain h10a : a.gpr .x10=s.gpr .x10 := hka.gpr .x10 (by decide)
    obtain h12a : a.gpr .x12=s.gpr .x12 := hka.gpr .x12 (by decide)
    obtain h11a : a.gpr .x11=s.gpr .x11 := hka.gpr .x11 (by decide)
    rw [buffer_addr] at ho hf
    obtain hpb := pairs_upd hp hb
    obtain hpt := pairs_upd hpb ht
    refine ⟨⟨⟨((h.keep.trans hka).trans ((RegKeep.upd hb).trans (RegKeep.upd ht))).mono
      (by simp [coreRegs]),?_,?_,?_⟩,hpt⟩,⟨?_,?_,?_⟩⟩
    · rw [ht.mem,hb.mem]
      apply h.frame.trans
      exact hf.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨bufferRegion work,by simp,Offset.sub_base (bufferBase work)
          (d:=136*i) (n:=136) (k:=680) (by omega_arith)⟩)
    · rw [ht.other .x5 (by decide),hb.other .x5 (by decide),hka.gpr .x5 (by decide)]
      exact h.ptr
    · rw [ht.mem,hb.mem,Nat.min_eq_left (by omega_arith)]
      have hold := h.output
      rw [Nat.min_eq_left (by omega_arith)] at hold
      exact streamOutput_append hi hold ho hf
    · rw [ht.other .x11 (by decide),hb.other .x11 (by decide),h11a]; exact hl.left
    · rw [ht.gpr,hb.other .x12 (by decide),h12a,h12,Nat.min_eq_left (by omega_arith),
        Offset.ofNat_sub_ofNat (by omega_arith)]
      congr 1
    · rw [ht.other .x10 (by decide),hb.gpr,h10a,h10,Nat.min_eq_left (by omega_arith),
        Offset.add_add]
      congr 1
  · have h12 : s.gpr .x12=0 := by rw [hl.masks,Nat.min_eq_right (by omega_arith)]; rfl
    refine WP.ite true (by rw [eval_zero,h12]; rfl) (fun _ => WP.block_nil ?_)
      (fun hb => Bool.noConfusion hb)
    refine ⟨⟨⟨h.keep,h.frame,h.ptr,?_⟩,h.pairs⟩,⟨hl.left,?_,?_⟩⟩
    · have ho := h.output
      rw [Nat.min_eq_right (by omega_arith)] at ho
      rw [Nat.min_eq_right (by omega_arith)]
      exact ho
    · rw [hl.masks,Nat.min_eq_right (by omega_arith),Nat.min_eq_right (by omega_arith)]
    · rw [hl.out,Nat.min_eq_right (by omega_arith),Nat.min_eq_right (by omega_arith)]

private theorem full_bound {σ : State} {wlen i j : Nat} {w1 work : Addr}
    (hc : CoreConfig σ wlen w1 work) (hi : i<(64+wlen)/136-1) (hj : j<17) :
    72+136*i+8*j+8≤wlen := by
  rcases hc.length with he|he
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega_arith
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega_arith

/-- The next full commitment block is read from the immutable packed input. -/
theorem coreFull_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (hi : i<(64+wlen)/136-1) (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block full) s fun t =>
      CoreState σ wlen w1 work A B (i+1) t ∧ RegKeep [.x5,.x7] s t := by
  obtain hptr : s.gpr .x5=w1+BitVec.ofNat 64 (72+136*i) := by
    rw [h.ptr,inputPtr,fullCount,Nat.min_eq_left (by omega_arith)]
  refine WP.mono (full_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp5,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (full_bound hc hi hj)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) s.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 =
      xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) σ.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (full_bound hc hi hj)
    rw [hptr,he] at hp
    refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk⟩
    · rw [hm]; exact h.frame
    · rw [hp5,hptr]
      change (w1+BitVec.ofNat 64 (72+136*i))+BitVec.ofNat 64 136=inputPtr wlen w1 (i+1)
      rw [Offset.add_add,inputPtr,fullCount,Nat.min_eq_left (by omega_arith)]
      congr 1
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter wlen σ.mem w1 i (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_left hi]
      exact hp

theorem coreTail65_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ 768 w1 work) (h : RoundState σ 768 w1 work A B 5 6 s) :
    WP isa (.block tail) s fun t =>
      CoreState σ 768 w1 work A B 6 t ∧ RegKeep [.x5,.x7] s t := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 752 := h.ptr
  refine WP.mono (tail_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (by omega_arith)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) s.mem
        (w1+BitVec.ofNat 64 752) 2 =
      xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) σ.mem
        (w1+BitVec.ofNat 64 752) 2 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (by omega_arith)
    rw [hptr,he] at hp
    refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk.mono (by simp)⟩
    · rw [hm]; exact h.frame
    · rw [hk.gpr .x5 (by decide)]
      exact h.ptr
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter 768 σ.mem w1 5 (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5))) _
      simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
        Nat.reduceMul,ite_false,ite_true] using hp

theorem coreTail87_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (h : RoundState σ 1024 w1 work A B 7 8 s) :
    WP isa (.block (paddingWord 0 31 0 ++ paddingWord 16 0x8000 3)) s fun t =>
      CoreState σ 1024 w1 work A B 8 t ∧ RegKeep [.x5,.x7] s t := by
  refine WP.mono (padding_ok (by decide) h.pairs) fun t ⟨hk,hm,hp⟩ => ?_
  refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk.mono (by simp)⟩
  · rw [hm]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]
    exact h.ptr
  · rw [hm]; exact h.output
  · change Pairs t (absorbAfter 1024 σ.mem w1 7 (Spec.Sha3.keccakF (lowRun 1024 σ.mem w1 A 7))) _
    simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
      ite_false,ite_true,ite_eq_right (by decide : ¬ (1024:Nat)=768)] using hp

/-- The block absorbed after the permutation `i`, the last of the
`(64+wlen)/136+1-i` left. -/
theorem coreAbsorb_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work) (hiN : i≤(64+wlen)/136)
    (h : RoundState σ wlen w1 work A B i (i+1) s)
    (h11 : s.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-i)) :
    WP isa (absorbNext wlen) s fun t =>
      CoreState σ wlen w1 work A B (i+1) t ∧ RegKeep [.x5,.x7,.x13] s t := by
  obtain hN : (64+wlen)/136≤8 := by rcases hc.length with rfl|rfl <;> decide
  obtain hN1 : 1≤(64+wlen)/136 := by rcases hc.length with rfl|rfl <;> decide
  refine WP.seq (wp_subImm (by decide) fun a ha => WP.block_nil ?_)
  obtain hra : RoundState σ wlen w1 work A B i (i+1) a :=
    ⟨h.toCoreEnv.upd ha (by simp [coreRegs]) (by decide),pairs_upd h.pairs ha⟩
  obtain h13 : a.gpr .x13=BitVec.ofNat 64 ((64+wlen)/136+1-i)-BitVec.ofNat 64 1 := by
    rw [ha.gpr,h11]
  obtain h11a : a.gpr .x11=s.gpr .x11 := ha.other .x11 (by decide)
  obtain hka : RegKeep [.x13] s a := RegKeep.upd ha
  by_cases hl : i=(64+wlen)/136
  · refine WP.ite true (by
      rw [eval_zero,h13,Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
      simp [hl]) (fun _ => WP.block_nil ?_) (fun hb => Bool.noConfusion hb)
    refine ⟨⟨⟨hra.keep,hra.frame,?_,hra.output⟩,?_⟩,hka.mono (by simp)⟩
    · rw [hra.ptr,inputPtr,inputPtr,fullCount,fullCount,
        Nat.min_eq_right (by omega_arith),Nat.min_eq_right (by omega_arith)]
    · change Pairs a (absorbAfter wlen σ.mem w1 i
        (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_right (by omega_arith),ite_eq_right (by omega_arith)]
      exact hra.pairs
  refine WP.ite false (by
    rw [eval_zero,h13,Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    simp only [Option.some.injEq,decide_eq_false_iff_not]
    omega_arith) (fun hb => Bool.noConfusion hb) fun _ => ?_
  refine WP.seq (wp_subImm (by decide) fun b hb => WP.block_nil ?_)
  obtain hrb : RoundState σ wlen w1 work A B i (i+1) b :=
    ⟨hra.toCoreEnv.upd hb (by simp [coreRegs]) (by decide),pairs_upd hra.pairs hb⟩
  obtain h13b : b.gpr .x13=BitVec.ofNat 64 ((64+wlen)/136+1-i)-BitVec.ofNat 64 2 := by
    rw [hb.gpr,h11a,h11]
  obtain hkb : RegKeep [.x13] s b := (hka.trans (RegKeep.upd hb)).mono (by simp)
  by_cases hp : i=(64+wlen)/136-1
  · refine WP.ite true (by
      rw [eval_zero,h13b,Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
      simp only [Option.some.injEq,decide_eq_true_eq]
      omega_arith) (fun _ => ?_) (fun hb => Bool.noConfusion hb)
    rcases hc.length with hw|hw
    · subst wlen
      have hi5 : i=5 := hp
      subst i
      exact WP.mono (coreTail65_ok hc hrb) fun t ⟨ht,hk⟩ =>
        ⟨ht,(hkb.trans hk).mono (by simp)⟩
    · subst wlen
      have hi7 : i=7 := hp
      subst i
      exact WP.mono (coreTail87_ok hrb) fun t ⟨ht,hk⟩ =>
        ⟨ht,(hkb.trans hk).mono (by simp)⟩
  · refine WP.ite false (by
      rw [eval_zero,h13b,Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
      simp only [Option.some.injEq,decide_eq_false_iff_not]
      omega_arith) (fun hb => Bool.noConfusion hb) fun _ => ?_
    exact WP.mono (coreFull_ok hc (by omega_arith) hrb) fun t ⟨ht,hk⟩ =>
      ⟨ht,(hkb.trans hk).mono (by simp)⟩

/-- The loop's invariant, `k` iterations before its exit. -/
def CoreInv (σ : State) (wlen : Nat) (w1 work : Addr) (A B : Spec.Sha3.State)
    (k : Nat) (s : State) : Prop :=
  ∃ i, i+k=(64+wlen)/136+1 ∧ 0<k ∧ CoreState σ wlen w1 work A B i s ∧ LoopRegs wlen work i i s

/-- All the permutations: seven for ML-DSA-65, nine for ML-DSA-87, with
only five cached-mask squeeze blocks. -/
theorem core_ok {σ s : State} {wlen : Nat} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ wlen w1 work) (h : CoreState σ wlen w1 work A B 0 s) :
    WP isa (coreFor wlen) s (CoreState σ wlen w1 work A B ((64+wlen)/136+1)) := by
  obtain hN : (64+wlen)/136≤8 := by rcases hc.length with rfl|rfl <;> decide
  obtain h19 : s.gpr .x19=work := (h.keep.gpr .x19 (by decide)).trans hc.workPtr
  refine WP.seq (wp_movz fun a ha => wp_movz fun b hb => wp_addImm (by decide) fun c hc' =>
    WP.block_nil ?_)
  obtain hsc : CoreState σ wlen w1 work A B 0 c :=
    ⟨((h.toCoreEnv.upd ha (by simp [coreRegs]) (by decide)).upd hb (by simp [coreRegs])
      (by decide)).upd hc' (by simp [coreRegs]) (by decide),
      pairs_upd (pairs_upd (pairs_upd h.pairs ha) hb) hc'⟩
  obtain hlc : LoopRegs wlen work 0 0 c := by
    refine ⟨?_,?_,?_⟩
    · rw [hc'.other .x11 (by decide),hb.other .x11 (by decide),ha.gpr]
      rcases hc.length with rfl|rfl <;> rfl
    · rw [hc'.other .x12 (by decide),hb.gpr]; rfl
    · rw [hc'.gpr,hb.other .x19 (by decide),ha.other .x19 (by decide),h19]; rfl
  refine WP.loop (M:=isa) (CoreInv σ wlen w1 work A B) ?_ ((64+wlen)/136+1) c
    ⟨0,by omega_arith,by omega_arith,hsc,hlc⟩
  rintro k t ⟨i,hik,hk,hs,hl⟩
  refine WP.seq (WP.mono (coreRound_ok hs) fun a ⟨ha,hka⟩ => ?_)
  obtain hla := hl.keep hka (by simp)
  refine WP.seq (WP.mono (coreEmit_ok hc ha hla) fun b ⟨hb,hlb⟩ => ?_)
  refine WP.seq (WP.mono (coreAbsorb_ok hc (by omega_arith) hb hlb.left) fun d ⟨hd,hkd⟩ => ?_)
  obtain hld := hlb.keep hkd (by simp)
  refine wp_subImm (by decide) fun e he => WP.block_nil ?_
  obtain hse : CoreState σ wlen w1 work A B (i+1) e :=
    ⟨hd.toCoreEnv.upd he (by simp [coreRegs]) (by decide),pairs_upd hd.pairs he⟩
  obtain h11 : e.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-(i+1)) := by
    rw [he.gpr,hld.left,Offset.ofNat_sub_ofNat (by omega_arith)]
    congr 1
  by_cases hlast : i=(64+wlen)/136
  · refine Or.inl ⟨?_,?_⟩
    · rw [eval_nonzero,h11,hlast,Nat.sub_self]; rfl
    · rw [← hlast]; exact hse
  · refine Or.inr ⟨?_,k-1,by omega_arith,i+1,by omega_arith,by omega_arith,hse,⟨h11,?_,?_⟩⟩
    · rw [eval_nonzero,h11]
      exact congrArg some (bne_iff_ne.mpr fun he' => by
        have := congrArg BitVec.toNat he'
        change _=(BitVec.ofNat 64 0).toNat at this
        simp only [BitVec.toNat_ofNat] at this
        omega_arith)
    · rw [he.other .x12 (by decide)]; exact hld.masks
    · rw [he.other .x10 (by decide)]; exact hld.out

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailNonceValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

theorem nonceWord_value (k : BitVec 64) :
    (nonceWord k).toNat=k.toNat%65536+2031616 := by
  obtain hx : ((k <<< 48) >>> 48).toNat=k.toNat%65536 := by
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    change (k.toNat*281474976710656 % (65536*281474976710656))/281474976710656=_
    rw [Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by decide)]
  rw [nonceWord,BitVec.toNat_add,hx]
  change (k.toNat%65536+2031616)%18446744073709551616=_
  exact Nat.mod_eq_of_lt (by omega_arith)

theorem nonceValue_byte (a k : BitVec 64) (hk : a.toNat=k.toNat%65536+2031616) {i : Nat} (hi : i<8) :
    a.extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ 3≤i by omega_arith) with h|h|h|h
  · subst i
    simp only [ite_true,Nat.mul_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk, Nat.div_one, Nat.add_mod]
    simp only [show 2031616 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    simpa only [Nat.div_one] using Nat.mod_mul_right_mod k.toNat 256 256
  · subst i
    simp only [ite_eq_right (by decide : ¬ (1:Nat)=0),ite_true,Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk]
    change ((k.toNat % (256*256) + 7936*256)/256)%256 = _
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.add_mod]
    simp only [show 7936 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod]
  · subst i
    simp only [ite_eq_right (by decide : ¬ (2:Nat)=0),ite_eq_right (by decide : ¬ (2:Nat)=1),ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow,Nat.reduceMul]
    rw [hk]
    change ((k.toNat % 65536 + 31*65536)/65536)%256 = 31
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.mod_div_self]
  · simp only [ite_eq_right (by omega_arith : ¬ i=0),ite_eq_right (by omega_arith : ¬ i=1),
      ite_eq_right (by omega_arith : ¬ i=2)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat]
    obtain hb : 8*i≥24 := by omega_arith
    obtain he : a.toNat<2^24 := by omega_arith
    obtain hdiv : a.toNat/2^(8*i)=0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hb))
    rw [Nat.shiftRight_eq_div_pow,hdiv]
    rfl

theorem nonceWord_byte (k : BitVec 64) {i : Nat} (hi : i<8) :
    (nonceWord k).extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 :=
  nonceValue_byte (nonceWord k) k (nonceWord_value k) hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSeed.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

def seedBytes (m : Mem) (p : Addr) (k : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m p 64 ++ [k.extractLsb' 0 8,k.extractLsb' 8 8]

theorem seedBytes_length (m : Mem) (p : Addr) (k : BitVec 64) :
    (seedBytes m p k).length=66 := by
  simp only [seedBytes,List.length_append,Proof.Sha3.bytesAt_length,List.length_cons,List.length_nil]

theorem seedBytes_get (m : Mem) (p : Addr) (k : BitVec 64) {j : Nat} (hj : j<66) :
    (seedBytes m p k).getD j 0 = if j<64 then m (p+BitVec.ofNat 64 j)
      else if j=64 then k.extractLsb' 0 8 else k.extractLsb' 8 8 := by
  unfold seedBytes
  by_cases h : j<64
  · rw [ite_eq_left h]
    rw [List.getD,List.getElem?_append_left (by rw [Proof.Sha3.bytesAt_length]; exact h)]
    exact Proof.MlKem.bytesAt_getD m p h
  · rw [ite_eq_right h,List.getD,List.getElem?_append_right (by rw [Proof.Sha3.bytesAt_length]; omega_arith),Proof.Sha3.bytesAt_length]
    rcases (show j=64 ∨ j=65 by omega_arith) with rfl|rfl <;> rfl

theorem seedNonceState_get (m : Mem) (p : Addr) (k : BitVec 64) {i : Nat} (hi : i<25) :
    (seedNonceState m p k)[i]! = if i<8 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i=8 then nonceWord k else if i=16 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedNonceState
  rw [Vector.getElem_ofFn]

theorem seedNonceState_A0 (m : Mem) (p : Addr) (k : BitVec 64) :
    seedNonceState m p k = Optimized.ResidentSeed66.A0 (seedBytes m p k) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Optimized.ResidentSeed66.byteOf_A0 (seedBytes_length m p k) hj]
  unfold Proof.Sha3.byteOf
  rw [seedNonceState_get m p k (by omega_arith)]
  by_cases h32 : j<64
  · rw [ite_eq_left (by omega_arith : j/8<8),ite_eq_left (by omega_arith : j<66),
      seedBytes_get m p k (by omega_arith),ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega_arith),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8=j by omega_arith]
  · rw [ite_eq_right (by omega_arith : ¬ j/8<8)]
    by_cases h40 : j<72
    · rw [ite_eq_left (by omega_arith : j/8=8),nonceWord_byte k (by omega_arith)]
      rcases (show j=64 ∨ j=65 ∨ j=66 ∨ 67≤j by omega_arith) with h|h|h|h
      · subst j
        rw [ite_eq_left (by decide : 64<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j
        rw [ite_eq_left (by decide : 65<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j; simp
      · simp (disch := omega_arith) only [ite_eq_right]
    · rw [ite_eq_right (by omega_arith : ¬ j/8=8)]
      by_cases h20 : j/8=16
      · rw [ite_eq_left h20,Optimized.ResidentMask.pad_byte (j%8) (by omega_arith)]
        by_cases he : j=135 <;> simp (disch := omega_arith) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega_arith) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end

/-! ### `MlDsa.AArch64.Sign.CommitTailHashRun`, which only this module used -/

section

/-! ## From `CommitTailHashPadding.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3
open VG.Proof.Sha3

theorem xorWord_byte (A : Spec.Sha3.State) (j k : Nat) (b : Byte) (w : BitVec 64)
    (hk : k<8) (hw : ∀r<8,w.extractLsb' (8*r) 8=if r=k then b else 0) :
    xorWord A j w=xorByte A (8*j+k) b := by
  apply ext_bytes
  intro i hi
  rw [byteOf_xorByte _ _ _ hi]
  simp only [byteOf,xorWord_get _ _ _ _ (by omega_using [hi] : i/8<25)]
  by_cases he : i/8=j
  · rw [ite_eq_left he,BitVec.extractLsb'_xor,hw _ (by omega_using [])]
    by_cases hr : i%8=k
    · rw [ite_eq_left hr,ite_eq_left (by omega_using [he, hr] : i=8*j+k)]
    · rw [ite_eq_right hr,ite_eq_right (by omega_using [hk, hr] : i≠8*j+k)]
      exact BitVec.xor_zero
  · rw [ite_eq_right he,ite_eq_right (by omega_using [hk, he] : i≠8*j+k)]

theorem xorWord_suffix (A : Spec.Sha3.State) (j : Nat) :
    xorWord A j 0x1f=xorByte A (8*j) 0x1f := by
  simpa only [Nat.add_zero] using xorWord_byte A j 0 0x1f 0x1f (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega_using [hr]) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem xorWord_terminal (A : Spec.Sha3.State) :
    xorWord A 16 0x8000000000000000=xorByte A 135 0x80 := by
  exact xorWord_byte A 16 7 0x80 0x8000000000000000 (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega_using [hr]) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem paddedState_bytes (A : Spec.Sha3.State) (j : Nat) :
    paddedState A j=xorByte (xorByte A (8*j) 0x1f) 135 0x80 := by
  rw [paddedState,xorWord_suffix,xorWord_terminal]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailHashFirst.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3

theorem firstState_byte (m : Mem) (mu w1 : Addr) {j : Nat} (hj : j<200) :
    byteOf (firstState m mu w1) j=
      if j<64 then m (mu+BitVec.ofNat 64 j)
      else if j<136 then m (w1+BitVec.ofNat 64 (j-64)) else 0 := by
  rw [byteOf_eq' _ hj]
  simp only [firstState,Vector.getElem_ofFn]
  by_cases h64 : j<64
  · rw [ite_eq_left (by omega_using [h64] : j/8<8),ite_eq_left h64]
    simp only [Mem.readW,BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read _ _ (by omega_using [] : j%8<64/8)]
    simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega_using []]
  · rw [ite_eq_right (by omega_using [h64] : ¬j/8<8),ite_eq_right h64]
    by_cases h136 : j<136
    · rw [ite_eq_left (by omega_using [h136] : j/8<17),ite_eq_left h136]
      simp only [Mem.readW,BitVec.setWidth_eq]
      rw [Mem.extractLsb'_read _ _ (by omega_using [] : j%8<64/8)]
      simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8-8)+j%8=j-64 by omega_using [h64]]
    · rw [ite_eq_right (by omega_using [h136] : ¬j/8<17),ite_eq_right h136]
      exact BitVec.extractLsb'_zero

theorem firstState_eq (m : Mem) (mu w1 : Addr) :
    firstState m mu w1=xorBytes zero (bytesAt m mu 64++bytesAt m w1 72) := by
  apply ext_bytes
  intro j hj
  rw [firstState_byte m mu w1 hj,byteOf_xorBytes _ _ hj]
  obtain hz : byteOf zero j=0 := by
    rw [byteOf_eq' _ hj]
    simp [zero]
  rw [hz]
  change _=(0#8) ^^^ _
  rw [BitVec.zero_xor]
  by_cases h64 : j<64
  · rw [ite_eq_left h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map,List.getElem?_range h64,Option.map_some,Option.getD_some]
  · rw [ite_eq_right h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map]
    by_cases h136 : j<136
    · rw [ite_eq_left h136,List.getElem?_range (by omega_using [h136] : j-64<72)]
      rfl
    · rw [ite_eq_right h136,List.getElem?_eq_none (by simp;omega_using [h136])]
      rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailHashBlocks.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3
open VG.Proof.MlKem (bytesAt_take bytesAt_drop bytesAt_slice)

def hashMessage (m : Mem) (mu w1 : Addr) (wlen : Nat) : List Byte :=
  bytesAt m mu 64++bytesAt m w1 wlen

theorem hashMessage_length (m : Mem) (mu w1 : Addr) (wlen : Nat) :
    (hashMessage m mu w1 wlen).length=64+wlen := by simp [hashMessage,bytesAt]

theorem hashMessage_first (m : Mem) (mu w1 : Addr) {wlen : Nat} (hw : 72≤wlen) :
    block 136 (hashMessage m mu w1 wlen) 0=bytesAt m mu 64++bytesAt m w1 72 := by
  simp only [block,hashMessage,Nat.mul_zero,List.drop_zero,List.take_append]
  rw [List.take_of_length_le (by simp [bytesAt]),show (bytesAt m mu 64).length=64 by simp [bytesAt]]
  exact congrArg (bytesAt m mu 64++·) (bytesAt_take m w1 hw)

theorem hashMessage_block (m : Mem) (mu w1 : Addr) {wlen i : Nat}
    (hi : 136*(i+1)+136≤64+wlen) :
    block 136 (hashMessage m mu w1 wlen) (i+1)=
      bytesAt m (w1+BitVec.ofNat 64 (72+136*i)) 136 := by
  simp only [block,hashMessage,List.drop_append]
  rw [List.drop_eq_nil_of_le (by simp [bytesAt];omega_using []),List.nil_append,
    show (bytesAt m mu 64).length=64 by simp [bytesAt],
    bytesAt_slice m w1 (by omega_using [hi] : 136*(i+1)-64+136≤wlen),
    show 136*(i+1)-64=72+136*i by omega_using []]

theorem hashMessage_tail (m : Mem) (mu w1 : Addr) {wlen n : Nat} (hn : 0<n)
    (hle : 136*n≤64+wlen) :
    (hashMessage m mu w1 wlen).drop (136*n)=
      bytesAt m (w1+BitVec.ofNat 64 (136*n-64)) (64+wlen-136*n) := by
  simp only [hashMessage,List.drop_append]
  rw [List.drop_eq_nil_of_le (by simp [bytesAt];omega_using [hn]),List.nil_append,
    show (bytesAt m mu 64).length=64 by simp [bytesAt],
    bytesAt_drop m w1 (by omega_using [hle] : 136*n-64≤wlen)]
  congr 1
  omega_using [hn]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailHashRun.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords_eq)

theorem lowRun_full (m : Mem) (mu w1 : Addr) {wlen : Nat} (hw : 72≤wlen)
    {i : Nat} (hi : i<(64+wlen)/136) :
    keccakF (lowRun wlen m w1 (firstState m mu w1) i)=
      absorbN 136 (hashMessage m mu w1 wlen) (i+1) := by
  induction i with
  | zero =>
    rw [lowRun,absorbN_succ,hashMessage_first m mu w1 hw,firstState_eq]
    rfl
  | succ i ih =>
    rw [lowRun,absorbAfter,ite_eq_left (by omega_using [hi] : i<(64+wlen)/136-1),xorWords_eq,
      ih (by omega_using [hi]),absorbN_succ 136 (hashMessage m mu w1 wlen) (i+1),
      hashMessage_block m mu w1 (wlen:=wlen) (i:=i) (by omega_using [hi])]

theorem lowRun_pad65 (m : Mem) (mu w1 : Addr) :
    lowRun 768 m w1 (firstState m mu w1) 7=
      absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 768)) := by
  obtain hf := lowRun_full m mu w1 (wlen:=768) (by decide) (i:=5) (by decide)
  obtain hr : Rep 136 (hashMessage m mu w1 768)=
      VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords (absorbN 136 (hashMessage m mu w1 768) 6)
        m (w1+752) 2 := by
    rw [Rep,absorb_eq,hashMessage_length,hashMessage_tail m mu w1 (n:=6) (by decide) (by decide),xorWords_eq]
    rfl
  rw [absorb_pad (by decide : 1<136) (by decide : 136≤200),hashMessage_length,hr]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(6:Nat)<(64+768)/136-1),
    ite_eq_right (by decide : ¬(6:Nat)=(64+768)/136-1)]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(5:Nat)<(64+768)/136-1),
    ite_eq_left (by decide : (5:Nat)=(64+768)/136-1),ite_eq_left rfl,hf,paddedState_bytes]
  rfl

theorem lowRun_pad87 (m : Mem) (mu w1 : Addr) :
    lowRun 1024 m w1 (firstState m mu w1) 9=
      absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 1024)) := by
  obtain hf := lowRun_full m mu w1 (wlen:=1024) (by decide) (i:=7) (by decide)
  obtain hr : Rep 136 (hashMessage m mu w1 1024)=absorbN 136 (hashMessage m mu w1 1024) 8 := by
    rw [Rep,absorb_eq,hashMessage_length,hashMessage_tail m mu w1 (n:=8) (by decide) (by decide)]
    exact xorBytes_nil _
  rw [absorb_pad (by decide : 1<136) (by decide : 136≤200),hashMessage_length,hr]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(8:Nat)<(64+1024)/136-1),
    ite_eq_right (by decide : ¬(8:Nat)=(64+1024)/136-1)]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(7:Nat)<(64+1024)/136-1),
    ite_eq_left (by decide : (7:Nat)=(64+1024)/136-1),ite_eq_right (by decide : (1024:Nat)≠768),hf,paddedState_bytes]
  rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

end

end

/-! ## From `CommitTailSponge.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CommitTailOutput.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (RatePairs)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem zip1_low (a b : BitVec 128) :
    VPermOp.eval .zip1 .d2 a b=ofVDwords (vdword a 0) (vdword b 0) :=
by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceDiv]
  simp only [List.range_succ,List.range_zero,List.nil_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.getD_cons_zero,List.getD_cons_succ]
  congr 1 <;> rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

private theorem pair_ok {s : State} {A B : Spec.Sha3.State} {p : Addr} {i : Nat}
    (hi : 2*i+1<25) (hp : Pairs s A B) (hptr : s.gpr .x2=p)
    (hout : InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block [.vop (.perm .zip1 .d2 .v25 (vreg (2*i)) (vreg (2*i+1))),
      .strq .v25 .x2 (16*i)]) s fun t => RegKeep [] s t ∧ Pairs t A B ∧
      t.mem=s.mem.write (p+BitVec.ofNat 64 (16*i)) 16 (ofVDwords A[2*i]! A[2*i+1]!) := by
  refine wp_vop (d:=.v25) rfl fun a ha =>
    wp_strq ⟨by omega,by omega⟩ (by rw [ha.gpr,hptr]) (by rw [ha.wr]; exact hout)
      fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨((RegKeep.vupd ha).trans (RegKeep.vmem ht)).mono (by simp),?_,?_⟩
  · intro j hj
    obtain hj25 : vreg j≠.v25 := by
      change vreg j≠vreg 25
      rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]; omega
    rw [ht.v,ha.get _ hj25]
    exact hp j hj
  · rw [ht.mem,ha.v,ha.mem,zip1_low,hp _ (by omega),hp _ hi,
      vdword_ofVDwords_0,vdword_ofVDwords_0]

/-- The first-lane digest is copied directly to its caller output. -/
theorem output_ok {s : State} {A B : Spec.Sha3.State} {p : Addr} (n : Nat)
    (hn : n≤12) (hp : Pairs s A B) (hptr : s.gpr .x2=p)
    (hout : ∀i<n, InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (output (16*n))) s fun t =>
      RegKeep [] s t ∧ Pairs t A B ∧ RatePairs t.mem p n A ∧ Frame [⟨p,16*n⟩] s.mem t.mem := by
  unfold output
  rw [show 16*n/16=n by omega]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ Pairs t A B ∧ RatePairs t.mem p k A ∧ Frame [⟨p,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,hp,fun _ h => by omega,Frame.refl _ _⟩
  refine WP.mono (pair_ok (by omega) ht.2.1 ((ht.1.gpr .x2 (by simp)).trans hptr)
    (by rw [ht.1.wr]; exact hout k hk)) fun u hu => ?_
  refine ⟨(ht.1.trans hu.1).mono (by simp),hu.2.1,?_,?_⟩
  · intro i hi
    rw [hu.2.2]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep p (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.1 i (by omega)
  · rw [hu.2.2]
    exact ht.2.2.2.write (r:=⟨p,16*n⟩) (by simp) _
      (Offset.contains_base p (by omega) (by omega))

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CommitTailHash.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3

theorem squeeze_small (A : Spec.Sha3.State) {d : Nat} (hd : d≤136) :
    squeeze 136 A d=(toBytes A).take d := by
  by_cases hz : d=0
  · subst d; simp [squeeze]
  · rw [squeeze,show (d+136-1)/136=1 by omega,squeezeBlocks,squeezeBlocks,List.append_nil,
      List.take_take,Nat.min_eq_left hd]

theorem lowRun_hash (m : Mem) (mu w1 : Addr) {wlen d : Nat}
    (hw : wlen=768 ∨ wlen=1024) (hd : d≤136) :
    (toBytes (lowRun wlen m w1 (firstState m mu w1) ((64+wlen)/136+1))).take d=
      Spec.MlDsa.H (bytesAt m mu 64++bytesAt m w1 wlen) d := by
  change _=squeeze 136 (absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 wlen))) d
  rw [squeeze_small _ hd]
  rcases hw with rfl|rfl
  · rw [show (64+768)/136+1=7 by decide,lowRun_pad65]
  · rw [show (64+1024)/136+1=9 by decide,lowRun_pad87]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CommitTailSaved.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64

theorem Saved.keep {σ : State} {m n : Mem} {W : List Region}
    (hs : Saved σ m) (hf : Frame W m n)
    (hd : ∀r∈W,(Region.mk (σ.gpr .x3) 160).Disjoint r) : Saved σ n := by
  constructor
  · intro i hi
    rw [hf.read (r:=⟨σ.gpr .x3,160⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact hs.vec i hi
  · intro i hi
    rw [hf.readW (r:=⟨σ.gpr .x3,160⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact hs.regs i hi

theorem Saved.keep_core {σ : State} {m n : Mem}
    (hs : Saved σ m) (hf : Frame [bufferRegion (σ.gpr .x3)] m n) : Saved σ n := by
  apply hs.keep hf
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact (Offset.disjoint_base (σ.gpr .x3) (d:=256) (n:=680) (k:=160)
    (by decide) (by decide)).symm

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def spongeRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x11,.x12,.x13,.x16]

theorem sponge_ok {s : State} {wlen : Nat} (hc : CoreConfig s wlen (s.gpr .x1) (s.gpr .x19))
    (hmu : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hseed : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.seq (.block (first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s fun t =>
      RegKeep spongeRegs s t ∧ Frame [bufferRegion (s.gpr .x19)] s.mem t.mem ∧
      Pairs t (lowRun wlen s.mem (s.gpr .x1) (firstState s.mem (s.gpr .x0) (s.gpr .x1))
        ((64+wlen)/136+1))
        (Optimized.Resident.permuted (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) ((64+wlen)/136+1)) ∧
      Spec.Sha3.bytesAt t.mem (bufferBase (s.gpr .x19)) 640 =
        Spec.MlDsa.H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640 := by
  obtain hw : 768≤wlen := by rcases hc.length with rfl|rfl <;> decide
  rw [WP.seq_iff]
  refine WP.mono (initial_ok hmu (fun j hj => hc.readable _ _ (by omega_using [hw, hj]))
    (hc.readable 64 8 (by omega_using [hw])) hseed) ?_
  intro a ⟨ha,hma,h5,hp⟩
  obtain hca : CoreConfig a wlen (s.gpr .x1) (s.gpr .x19) := by
    refine ⟨hc.length,ha.gpr .x19 (by decide),?_,?_,hc.separate⟩
    · intro d n hn; rw [ha.rd,ha.wr]; exact hc.readable d n hn
    · intro d n hn; rw [ha.wr]; exact hc.writable d n hn
  obtain hstart : CoreState a wlen (s.gpr .x1) (s.gpr .x19)
      (firstState s.mem (s.gpr .x0) (s.gpr .x1))
      (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) 0 a := by
    refine ⟨⟨RegKeep.refl _ _,Frame.refl _ _,?_,fun _ hi => by omega⟩,hp⟩
    simp only [inputPtr,fullCount,Nat.zero_min,Nat.mul_zero,Nat.add_zero]
    exact h5
  refine WP.mono (core_ok hca hstart) fun t ht => ?_
  refine ⟨(ha.trans ht.keep).mono (by simp [coreRegs,spongeRegs]),?_,?_,?_⟩
  · simpa only [hma] using ht.frame
  · simpa only [hma] using ht.pairs
  · have ho := ht.output
    obtain hn : min ((64+wlen)/136+1) 5=5 := by rcases hc.length with rfl|rfl <;> decide
    rw [hn,seedNonceState_A0] at ho
    exact Optimized.ResidentMask.stream_mask_bytes (d:=20) (Or.inr rfl)
      (seedBytes_length _ _ _) ho

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailDecode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Proof.MlDsa.AArch64.Pack VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Only Keep wp_movImm wp_nil)
open VG.Spec.MlDsa

def decodeRegs : List Reg := [.x0,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]

theorem decodeWidth_ok {s a : State}
    (ha : Only [.x9,.x13] s a)
    (h13 : a.gpr .x13=BitVec.ofNat 64 q)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (buWidth 524288 20 2 5) a fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun b hb h12 => wp_nil ?_
  refine WP.mono (unpackLoop_ok (buFin_ok 524288 20)
    (show Shape 20 2 5 from ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩)
    (v:=s.gpr .x0) (p:=s.gpr .x4) (s₀:=s) hin hout hsep
    (by rw [hb.get .x0,ha.get .x0]) (by rw [hb.get .x4,ha.get .x4]) h12
    (by rw [hb.get .x13,h13]) (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.mem.trans ha.mem))
    fun t ⟨hv,hf,hk⟩ => ⟨hv,hf,((ha.keep.trans hb.keep).trans hk).mono⟩

theorem decode_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  unfold VG.Impl.MlDsa.AArch64.Pack.bitUnpack
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun a ha h13 => wp_nil ?_
  refine sel_ok (by decide) (fun b hb h => ?_) (fun b hb _ => ?_)
  · rw [ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun c hc h => ?_) (fun c hc _ => ?_)
  · rw [hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun d hd h => ?_) (fun d hd _ => ?_)
  · rw [hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun e he h => ?_) (fun e he _ => ?_)
  · rw [hd.get .x1,hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  exact decodeWidth_ok (((((ha.trans hb).trans hc).trans hd).trans he).mono (by decide))
    (by rw [he.get .x13,hd.get .x13,hc.get .x13,hb.get .x13,h13]; rfl) hin hout hsep


theorem decode_access_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  let a := s.withRegions [⟨s.gpr .x0,640⟩] [polyRegion (s.gpr .x4)]
  obtain ⟨tr,t,he,hv,hf,hk⟩ := decode_ok (s:=a) h1 (by simp [a]) (by simp [a]) hsep
  obtain hw := VG.AArch64.Exec.widen he (rd:=s.rd) (wr:=s.wr)
    (Covers.append_left (Covers.one hin) (Covers.right (Covers.one hout))) (Covers.one hout)
  change Exec isa _ s tr (t.withRegions s.rd s.wr) at hw
  exact ⟨tr,_,hw,hv,hf,⟨hk.gpr,rfl,rfl,hk.sp,hk.vcs⟩⟩


theorem decode_poly {m n : Mem} {a out : Addr}
    (hc : ∀i<256,coeffAt n out i=buWord 524288 (inNum m a 20 /2^(20*i)%2^20)) :
    PolyIs n out (toRq (bitUnpack (Spec.Sha3.bytesAt m a 640) 524287 524288)) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hq : q=8380417 := rfl
  obtain hy := field_lt (inNum m a 20) 20 i (by decide)
  have hy' := hy
  unfold inNum at hy'
  rw [hc i hi,buWord,BitVec.toNat_setWidth,subModQ_toNat (by decide) (by omega_using [hq]),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 0<q by decide)) (by decide)),
    toRq,Vector.getElem_map,bitUnpack_get _ _ _ hi]
  change _=(ofInt ((524288:Nat) -
    ((VG.Proof.MlKem.digits 8 ((Spec.Sha3.bytesAt m a 640).map BitVec.toNat) /2^(20*i)%2^20 : Nat) : Int))).val
  rw [ofInt_sub (by omega_using [hq])]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailOutputBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident

theorem ratePairs_word {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {i : Nat} (hi : i<2*n) :
    m.readW (a+BitVec.ofNat 64 (8*i)) 64=A[i]! := by
  obtain hp := h (i/2) (by omega_using [hi])
  obtain hv := congrArg (fun v => vdword v (i%2)) hp
  rw [vdword_read16 _ _ (by omega_using [])] at hv
  rcases (show i%2=0 ∨ i%2=1 by omega_using []) with hm|hm
  · rw [hm,vdword_ofVDwords_0] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*0=8*i by omega_using [hm],show 2*(i/2)=i by omega_using [hm]] using hv
  · rw [hm,vdword_ofVDwords_1] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*1=8*i by omega_using [hm],show 2*(i/2)+1=i by omega_using [hm]] using hv

theorem ratePairs_byte {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {j : Nat} (hj : j<16*n) :
    m (a+BitVec.ofNat 64 j)=Proof.Sha3.byteOf A j := by
  obtain hw := ratePairs_word h (i:=j/8) (by omega_using [hj])
  obtain he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (a+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8=_ at he
  rw [Mem.extractLsb'_read m _ (by omega_using [])] at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega_using []] at he
  exact he

theorem ratePairs_bytes {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) (hn : n≤12) :
    Spec.Sha3.bytesAt m a (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  apply List.ext_getElem
  · rw [Proof.Sha3.bytesAt_length,List.length_take,Proof.Sha3.length_toBytes]
    omega_using [hn]
  · intro j hj hj'
    rw [Proof.Sha3.bytesAt_length] at hj
    rw [Proof.MlKem.bytesAt_getElem,List.getElem_take,Proof.Sha3.toBytes_getElem _ (by omega_using [hn, hj])]
    exact ratePairs_byte h hj

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailParse.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_movz)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack (polyRegion)

def parseRegs : List Reg := .x1::decodeRegs

theorem parse_ok {s : State}
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack) s fun t =>
      RegKeep parseRegs s t ∧ Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧
      PolyIs t.mem (s.gpr .x4) (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 640) 524287 524288)) := by
  rw [WP.seq_iff]
  refine wp_movz fun a ha => WP.block_nil_iff.mpr ?_
  refine WP.mono (decode_access_ok (s:=a) ha.gpr
    (by rw [ha.rd,ha.wr,ha.other .x0 (by decide)]; exact hin)
    (by rw [ha.wr,ha.other .x4 (by decide)]; exact hout)
    (by rw [ha.other .x0 (by decide),ha.other .x4 (by decide)]; exact hsep))
    fun t ⟨hc,hf,hk⟩ => ?_
  simp only [ha.mem,ha.other .x0 (by decide),ha.other .x4 (by decide)] at hc hf
  refine ⟨?_,hf,decode_poly hc⟩
  obtain hb : RegKeep decodeRegs a t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  exact ((RegKeep.upd ha).trans hb).mono (by simp [parseRegs])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailFront.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def frontRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x11,.x12,.x13,.x16,.x19,.x20,.x21]

structure FrontPre (wlen : Nat) (s : State) : Prop where
  length : wlen=768 ∨ wlen=1024
  mu : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 d) n
  packed : ∀d n,d+n≤wlen→InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 d) n
  seed : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 d) n
  work : ∀d n,d+n≤2048→InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 d) n
  muSep : (Region.mk (s.gpr .x0) 64).Disjoint ⟨s.gpr .x3,2048⟩
  packedSep : (Region.mk (s.gpr .x1) wlen).Disjoint ⟨s.gpr .x3,2048⟩
  seedSep : (Region.mk (s.gpr .x4) 64).Disjoint ⟨s.gpr .x3,2048⟩

def FrontPost (wlen : Nat) (σ s : State) : Prop :=
  RegKeep frontRegs σ s ∧ Saved σ s.mem ∧ Frame [⟨σ.gpr .x3,2048⟩] σ.mem s.mem ∧
  s.gpr .x19=σ.gpr .x3 ∧ s.gpr .x20=σ.gpr .x6 ∧ s.gpr .x21=σ.gpr .x2 ∧
  ∃A B,Pairs s A B ∧
    (∀d,d≤136→(Spec.Sha3.toBytes A).take d=Spec.MlDsa.H
      (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) d) ∧
    Spec.Sha3.bytesAt s.mem (bufferBase (σ.gpr .x3)) 640=
      Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640

theorem front_ok {s : State} {wlen : Nat} (hp : FrontPre wlen s) :
    WP isa (.seq (.block (pro++first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s (FrontPost wlen s) := by
  rw [WP.seq_iff,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok (fun i hi => hp.work _ _ (by omega_using [hi]))
    (fun i hi => hp.work _ _ (by omega_using [hi]))) fun a ⟨ha,hva,hsa,hfa,h19,h20,h21⟩ => ?_
  obtain hsub : (Region.mk (s.gpr .x3) 160).Sub ⟨s.gpr .x3,2048⟩ := by
    simpa using Offset.sub_base (s.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)
  obtain hconfig : CoreConfig a wlen (a.gpr .x1) (a.gpr .x19) := by
    refine ⟨hp.length,rfl,?_,?_,?_⟩
    · intro d n hn; rw [ha.rd,ha.wr,ha.gpr .x1 (by decide)]; exact hp.packed d n hn
    · intro d n hn; rw [ha.wr,h19]; exact hp.work d n hn
    · rw [ha.gpr .x1 (by decide),h19]
      exact hp.packedSep.sub_right (Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide))
  rw [← WP.seq_iff,← List.append_assoc]
  refine WP.mono (sponge_ok hconfig (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x0 (by decide)]; exact hp.mu _ _ (by omega_using [hi])) (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x4 (by decide)]; exact hp.seed _ _ (by omega_using [hi])))
    fun t ⟨ht,hft,hpt,hbytes⟩ => ?_
  rw [h19] at hft hbytes
  obtain hmu : Spec.Sha3.bytesAt a.mem (s.gpr .x0) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64 := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.muSep.sub_right hsub
  obtain hpw : Spec.Sha3.bytesAt a.mem (s.gpr .x1) wlen=Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by rcases hp.length with rfl|rfl <;> decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.packedSep.sub_right hsub
  obtain hseed : seedBytes a.mem (s.gpr .x4) (s.gpr .x5)=seedBytes s.mem (s.gpr .x4) (s.gpr .x5) := by
    obtain hb : Spec.Sha3.bytesAt a.mem (s.gpr .x4) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x4) 64 :=
      Proof.MlKem.bytesAt_frame hfa (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact hp.seedSep.sub_right hsub) (by decide)
    unfold seedBytes
    rw [hb]
  refine ⟨(ha.trans ht).mono (by simp [frontRegs,spongeRegs]),hsa.keep_core hft,?_,
    (ht.gpr .x19 (by decide)).trans h19,(ht.gpr .x20 (by decide)).trans h20,
    (ht.gpr .x21 (by decide)).trans h21,_,_,hpt,?_,?_⟩
  · apply Frame.trans
    · exact hfa.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,hsub⟩)
    · exact hft.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide)⟩)
  · intro d hd
    rw [lowRun_hash a.mem (a.gpr .x0) (a.gpr .x1) hp.length hd,
      ha.gpr .x0 (by decide),ha.gpr .x1 (by decide),hmu,hpw]
  · rw [ha.gpr .x4 (by decide),ha.gpr .x5 (by decide),hseed] at hbytes
    exact hbytes

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailOutputStage.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov WP.cons)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.MlKem.AArch64 (mov)

def outputStage (olen : Nat) : List Instr :=
  [mov .x2 .x21]++output olen++[.addImm .x .x0 .x19 256,mov .x4 .x20]

theorem outputStage_ok {s : State} {A B : Spec.Sha3.State} {n : Nat}
    (hn : n≤12) (hp : Pairs s A B)
    (hout : ∀i<n,InRegions s.wr (s.gpr .x21+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (outputStage (16*n))) s fun t =>
      RegKeep [.x0,.x2,.x4] s t ∧ Frame [⟨s.gpr .x21,16*n⟩] s.mem t.mem ∧
      t.gpr .x0=s.gpr .x19+256 ∧ t.gpr .x4=s.gpr .x20 ∧
      Spec.Sha3.bytesAt t.mem (s.gpr .x21) (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  unfold outputStage
  rw [List.append_assoc,WP.block_append_iff]
  refine wp_mov fun a ha => WP.block_nil_iff.mpr ?_
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (s:=a) (A:=A) (B:=B) (p:=s.gpr .x21) n hn (by intro i hi; rw [ha.vec]; exact hp i hi)
    ha.gpr (by intro i hi; rw [ha.wr]; exact hout i hi)) fun b ⟨hb,hpb,hbytes,hf⟩ => ?_
  obtain hfb : Frame [⟨s.gpr .x21,16*n⟩] s.mem b.mem := by simpa only [ha.mem] using hf
  refine WP.cons rfl (wp_mov fun t ht => WP.block_nil_iff.mpr ?_)
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨fun r hr => ?_,ht.rd.trans hb.rd |>.trans ha.rd,
      ht.wr.trans hb.wr |>.trans ha.wr,ht.sp.trans hb.sp |>.trans ha.sp⟩
    obtain h4 : r≠.x4 := fun e => hr (by simp [e])
    obtain h0 : r≠.x0 := fun e => hr (by simp [e])
    rw [ht.other r h4,RegUpd.gpr_write,ite_eq_right h0,hb.gpr r (by simp),ha.other r (by
      intro e; apply hr; simp [e])]
  · rw [ht.mem]; exact hfb
  · rw [ht.other .x0 (by decide),RegUpd.gpr_write_self]
    change b.gpr .x19+256=s.gpr .x19+256
    rw [hb.gpr .x19 (by simp),ha.other .x19 (by decide)]
  · rw [ht.gpr,RegUpd.gpr_write,ite_eq_right (by decide : ¬ Reg.x20=Reg.x0),
      hb.gpr .x20 (by simp),ha.other .x20 (by decide)]
  · rw [ht.mem]
    exact ratePairs_bytes hbytes hn

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.Pack (polyRegion)
open VG.Spec.MlDsa

structure Pre (wlen olen : Nat) (s : State) : Prop extends FrontPre wlen s where
  outLength : olen=48 ∨ olen=64
  output : ∀d n,d+n≤olen→InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 d) n
  cache : InRegions s.wr (s.gpr .x6) 1024
  readWork : ∀d n,d+n≤2048→InRegions (s.rd++s.wr) (s.gpr .x3+BitVec.ofNat 64 d) n
  outWork : (Region.mk (s.gpr .x2) olen).Disjoint ⟨s.gpr .x3,2048⟩
  cacheWork : (polyRegion (s.gpr .x6)).Disjoint ⟨s.gpr .x3,2048⟩
  outCache : (Region.mk (s.gpr .x2) olen).Disjoint (polyRegion (s.gpr .x6))

def bodyRegs : List Reg := [.x0,.x1,.x2,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x19,.x20,.x21]
def writes (s : State) (olen : Nat) : List Region :=
  [⟨s.gpr .x3,2048⟩,⟨s.gpr .x2,olen⟩,polyRegion (s.gpr .x6)]

def BodyPost (wlen olen : Nat) (σ s : State) : Prop :=
  RegKeep bodyRegs σ s ∧ Saved σ s.mem ∧ Frame (writes σ olen) σ.mem s.mem ∧ s.gpr .x19=σ.gpr .x3 ∧
  Spec.Sha3.bytesAt s.mem (σ.gpr .x2) olen=H
    (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
  PolyIs s.mem (σ.gpr .x6) (toRq (bitUnpack (H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288))

theorem body_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ) (hs : FrontPost wlen σ s) :
    WP isa (.seq (.block (outputStage olen))
      (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack)) s (BodyPost wlen olen σ) := by
  obtain ⟨hk,hsv,hf,h19,h20,h21,A,B,hpAB,hhash,hbytes⟩ := hs
  obtain hmul : 16*(olen/16)=olen := by rcases hp.outLength with rfl|rfl <;> decide
  obtain hn : olen/16≤12 := by rcases hp.outLength with rfl|rfl <;> decide
  rw [WP.seq_iff,← hmul]
  refine WP.mono (outputStage_ok hn hpAB (fun i hi => by
    rw [hk.wr,h21]; exact hp.output _ _ (by omega_using [hi]))) fun a ⟨ha,hfa,h0,h4,hout⟩ => ?_
  rw [hmul]
  rw [hmul,h21] at hfa hout
  rw [h19] at h0
  rw [h20] at h4
  obtain hasv : Saved σ a.mem := hsv.keep hfa (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.outWork.symm.sub_left (by
      simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  obtain habytes : Spec.Sha3.bytesAt a.mem (bufferBase (σ.gpr .x3)) 640=
      H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640 := by
    rw [Proof.MlKem.bytesAt_frame hfa (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))) (by decide)]
    exact hbytes
  obtain hahash := hhash olen (by rcases hp.outLength with rfl|rfl <;> decide)
  rw [hahash] at hout
  refine WP.mono (parse_ok (s:=a) (by
    rw [ha.rd,ha.wr,hk.rd,hk.wr,h0]; exact hp.readWork 256 640 (by decide)) (by
    rw [ha.wr,hk.wr,h4]; exact hp.cache) (by
    rw [h0,h4]
    exact hp.cacheWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))))
    fun t ⟨ht,hft,hpoly⟩ => ?_
  rw [h4] at hft hpoly
  change Spec.Sha3.bytesAt a.mem (σ.gpr .x3+256) 640=_ at habytes
  rw [h0,habytes] at hpoly
  refine ⟨((hk.trans ha).trans ht).mono (by simp [frontRegs,parseRegs,decodeRegs,bodyRegs]),?_,?_,?_,?_,hpoly⟩
  · exact hasv.keep hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.cacheWork.symm.sub_left (by
        simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  · apply Frame.trans (hf.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    apply Frame.trans (hfa.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    exact hft.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩)
  · exact (ht.gpr .x19 (by decide)).trans ((ha.gpr .x19 (by decide)).trans h19)
  · rw [Proof.MlKem.bytesAt_frame hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outCache) (by rcases hp.outLength with rfl|rfl <;> decide)]
    exact hout

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

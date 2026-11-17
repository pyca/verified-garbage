module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch

/-! ### `MlDsa.AArch64.Optimized.ResidentRejLastProgress`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResidentRejLastPair`, which only this module used -/

section

/-! ## From `ResidentRejPair.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (RateBlock originalCore)

/-- The registers the sixth block's pair changes. -/
def blockRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7]

/-- The adaptive sixth block: a call, the states loaded back, and the same vector
serialization as the resident path. -/
theorem pair_ok {s : State} {p a b w : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp=p) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (hw : s.gpr .x19+BitVec.ofNat 64 Impl.MlDsa.AArch64.Sample.Rej4.oX2=w)
    (hp1 : rp≠.x1) (hpc : rp∉X2.clobbered) (hac : ra∉X2.clobbered) (hbc : rb∉X2.clobbered)
    (ha6 : ra≠.x6) (ha7 : ra≠.x7) (hb6 : rb≠.x6) (hb7 : rb≠.x7)
    (hpair : PairAt s.mem p A B)
    (hin : ∀i<25,InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀i<10,InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀i<10,InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 160) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 160) 8)
    (hd : (Region.mk a 168).Disjoint ⟨b,168⟩)
    (hpa : (pairR p).Disjoint ⟨a,168⟩) (hpb : (pairR p).Disjoint ⟨b,168⟩)
    (hpw : (pairR p).Disjoint (X2.callR w)) (hcov : Covers [pairR p,X2.callR w] s.wr) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      RegKeep blockRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateBlock t.mem a 10 (Spec.Sha3.keccakF A) ∧
      RateBlock t.mem b 10 (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,⟨a,168⟩,⟨b,168⟩,X2.callR w] s.mem t.mem := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.pair
  refine WP.seq (WP.mono (X2.call_ok (by decide) hp1 hp hw hpw hpair hcov) fun t ⟨hk,hf,hpt⟩ => ?_)
  have hkt : RegKeep X2.clobbered s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  rw [WP.block_append_iff]
  refine WP.mono (load_ok ((hkt.gpr _ hpc).trans hp) hpt (fun i hi => by rw [hk.rd,hk.wr]; exact hin i hi))
    fun s1 ⟨h1,hpair1⟩ => ?_
  refine WP.mono (Resident.squeeze_ok (n := 10) (by decide)
    (A := Spec.Sha3.keccakF A) (B := Spec.Sha3.keccakF B) hpair1
    (by rw [h1.gpr,hkt.gpr _ hac,ha]) (by rw [h1.gpr,hkt.gpr _ hbc,hb]) ha6 ha7 hb6 hb7 hd
    (fun i hi => by rw [h1.wr,hk.wr]; exact hwa i hi)
    (fun i hi => by rw [h1.wr,hk.wr]; exact hwb i hi)
    (by rw [h1.wr,hk.wr]; exact hwal)
    (by rw [h1.wr,hk.wr]; exact hwbl)) fun u ⟨h4,_,hra,hrb,hf4⟩ => ?_
  have hku : RegKeep [.x6,.x7] t u := ⟨fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      rw [h4.gpr r hr.1 hr.2,h1.gpr],
    h4.rd.trans h1.rd,h4.wr.trans h1.wr,h4.sp.trans h1.sp⟩
  have hf4' : Frame [⟨a,168⟩,⟨b,168⟩] t.mem u.mem := by rw [← h1.mem]; exact hf4
  refine ⟨(hkt.trans hku).mono (by decide),fun i hi => ?_,hra,hrb,?_⟩
  · rw [hf4'.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hpa
      · exact hpb) (by decide)]
    exact hpt i hi
  · exact (hf.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
      (hf4'.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejLastPair.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted RateBlock)

def lastPtr (σ : State) (k : Nat) : Addr := bufP σ k+BitVec.ofNat 64 840

/-- `vg_keccak_f1600_x2_sha3`'s working space, and the return address during its calls. -/
def x2R (σ : State) : Region := X2.callR (scr σ+BitVec.ofNat 64 Impl.MlDsa.AArch64.Sample.Rej4.oX2)

def lastWrites (σ : State) (p : Nat) : List Region :=
  [pairR (stateP σ p),⟨lastPtr σ (2*p),168⟩,⟨lastPtr σ (2*p+1),168⟩,x2R σ]

theorem lastWrites_low {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈lastWrites σ p,Region.Sub r (lowR σ) := by
  intro r hr
  simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega_using [hp])
  · change Region.Sub ⟨(scr σ+BitVec.ofNat 64 (840+1008*(2*p)))+BitVec.ofNat 64 840,168⟩ (lowR σ)
    rw [Offset.add_add]
    exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega_using [hp])
  · change Region.Sub ⟨(scr σ+BitVec.ofNat 64 (840+1008*(2*p+1)))+BitVec.ofNat 64 840,168⟩ (lowR σ)
    rw [Offset.add_add]
    exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega_using [hp])
  · exact Offset.sub_base (scr σ) (by decide)

theorem lastPtr_eq (σ : State) (k : Nat) : lastPtr σ k=scr σ+BitVec.ofNat 64 (1680+1008*k) := by
  change (scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 840=_
  rw [Offset.add_add,show 840+1008*k+840=1680+1008*k by omega_using []]

/-- The registers of a pair's call: not those the call changes. -/
def CallRegs (rp ra rb : Reg) : Prop := rp≠.x1 ∧ rp∉X2.clobbered ∧ ra∉X2.clobbered ∧ rb∉X2.clobbered

theorem callRegs0 : CallRegs .x22 .x24 .x25 := by unfold CallRegs; decide
theorem callRegs1 : CallRegs .x23 .x26 .x27 := by unfold CallRegs; decide

theorem lastPair_ok {v p : Nat} {σ s : State} {rp ra rb : Reg}
    (hp : Pre v σ) (he : Env v σ s) (hpn : 2*p+1<v) (hr : FiveRegisters rp ra rb)
    (hreg : CallRegs rp ra rb)
    (hpair : PairAt s.mem (stateP σ p) (permuted (A0 σ (2*p)) 5) (permuted (A0 σ (2*p+1)) 5))
    (hrp : s.gpr rp=stateP σ p) (ha : s.gpr ra=lastPtr σ (2*p))
    (hb : s.gpr rb=lastPtr σ (2*p+1)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      Env v σ t ∧
      PairAt t.mem (stateP σ p) (permuted (A0 σ (2*p)) 6) (permuted (A0 σ (2*p+1)) 6) ∧
      RateBlock t.mem (lastPtr σ (2*p)) 10 (permuted (A0 σ (2*p)) 6) ∧
      RateBlock t.mem (lastPtr σ (2*p+1)) 10 (permuted (A0 σ (2*p+1)) 6) ∧
      Frame (lastWrites σ p) s.mem t.mem ∧ RegKeep blockRegs s t := by
  have hp2 : p<2 := by have:=hp.streams; omega_using [hpn, this]
  have hword (i : Nat) (hi : i<25) : InRegions s.wr (wordAddr (stateP σ p) i) 16 := by
    change InRegions s.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*i)) 16
    rw [Offset.add_add]
    exact in_scr hp he.wr (by omega_using [hp2, hi])
  have hbuf (k : Nat) (hk : k<4) (d n : Nat) (hd : d+n≤168) :
      InRegions s.wr (lastPtr σ k+BitVec.ofNat 64 d) n := by
    rw [lastPtr_eq,Offset.add_add]
    exact in_scr hp he.wr (by omega_using [hk, hd])
  have hsw : s.wr = [aR v σ,scrR σ] := he.wr.trans hp.wr
  refine WP.mono (pair_ok hrp ha hb (by rw [he.x19]) hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2
    hr.a6 hr.a7 hr.b6 hr.b7 hpair
    (fun i hi => by obtain ⟨r,hr,hc⟩ := hword i hi; exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩)
    (fun i hi => hbuf (2*p) (by omega_using [hp2]) (16*i) 16 (by omega_using [hi]))
    (fun i hi => hbuf (2*p+1) (by omega_using [hp2]) (16*i) 16 (by omega_using [hi]))
    (hbuf (2*p) (by omega_using [hp2]) 160 8 (by decide)) (hbuf (2*p+1) (by omega_using [hp2]) 160 8 (by decide))
    (by
      rw [lastPtr_eq,lastPtr_eq]
      exact Offset.disjoint (scr σ)
        (d := 1680+1008*(2*p)) (e := 1680+1008*(2*p+1)) (n := 168) (k := 168)
        (by omega_using []) (by omega_using [hp2]) (by omega_using [hp2]))
    (by
      rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*p)
        (e := 1680+1008*(2*p)) (n := 400) (k := 168) (by omega_using []) (by omega_using [hp2]) (by omega_using [hp2]))
    (by
      rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*p)
        (e := 1680+1008*(2*p+1)) (n := 400) (k := 168) (by omega_using []) (by omega_using [hp2]) (by omega_using [hp2]))
    (Offset.disjoint (scr σ) (d := 400*p) (e := 4880) (n := 400) (k := 136)
      (by omega_using [hp2]) (by omega_using [hp2]) (by decide))
    (by
      rw [hsw]
      refine Covers.of_sub fun r hr => ⟨scrR σ,by simp,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨400*p,rfl,by change 400*p+400 ≤ 8192; omega_using [hp2]⟩
      · exact ⟨4880,rfl,by change 4880+136 ≤ 8192; decide⟩))
    fun t ⟨ht,hpt,ha,hb,hf⟩ => ?_
  refine ⟨he.lowStep hf (lastWrites_low hp2) ht.rd ht.wr ht.sp ?_,hpt,ha,hb,hf,ht⟩
  intro r hm
  apply ht.gpr r; simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

end


/-! ## From `ResidentRejLastFrame.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

theorem lastWrites_count {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈lastWrites σ p,(countR σ).Disjoint r := by
  intro r hr
  simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (pair_count_disjoint σ hp).symm
  · rw [lastPtr_eq]
    exact Offset.disjoint (scr σ) (d := 7904) (e := 1680+1008*(2*p))
      (n := 32) (k := 168) (by omega_using []) (by decide) (by omega_using [hp])
  · rw [lastPtr_eq]
    exact Offset.disjoint (scr σ) (d := 7904) (e := 1680+1008*(2*p+1))
      (n := 32) (k := 168) (by omega_using []) (by decide) (by omega_using [hp])
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 4880) (n := 32) (k := 136)
      (by decide) (by decide) (by decide)

theorem last_count_keep {σ : State} {p k : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hf : Frame (lastWrites σ p) s.mem t.mem) :
    t.mem.readW (countP σ k) 64=s.mem.readW (countP σ k) 64 := by
  apply hf.readW
  · exact Offset.contains (scr σ) (d := 7904+8*k) (e := 7904) (n := 8) (k := 32)
      (by omega_using []) (by omega_using [hk]) (by decide)
  · exact lastWrites_count hp
  · decide

theorem last_pair_keep {σ : State} {p q : Nat} {s t : State} {A B : Spec.Sha3.State}
    (hp : p<2) (hq : q<2) (hne : p≠q) (hf : Frame (lastWrites σ p) s.mem t.mem)
    (hpair : PairAt s.mem (stateP σ q) A B) : PairAt t.mem (stateP σ q) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ q) hi) (by
    intro r hr
    simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint (scr σ) (d := 400*q) (e := 400*p) (n := 400) (k := 400)
        (by omega_using [hne]) (by omega_using [hq]) (by omega_using [hp])
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p)) (n := 400) (k := 168)
        (by omega_using [hq]) (by omega_using [hq]) (by omega_using [hp])
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p+1)) (n := 400) (k := 168)
        (by omega_using [hq]) (by omega_using [hq]) (by omega_using [hp])
    · exact Offset.disjoint (scr σ) (d := 400*q) (e := 4880) (n := 400) (k := 136)
        (by omega_using [hq]) (by omega_using [hq]) (by decide)) (by decide)]
  exact hpair i hi

theorem last_buffer_keep {σ : State} {p k j n : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hn : n≤1008) (hj : j<n)
    (h0 : k=2*p → n≤840) (h1 : k=2*p+1 → n≤840)
    (hf : Frame (lastWrites σ p) s.mem t.mem) :
    t.mem (bufP σ k+BitVec.ofNat 64 j)=s.mem (bufP σ k+BitVec.ofNat 64 j) := by
  apply hf
  intro r hr
  have hd : (Region.mk (bufP σ k) n).Disjoint r := by
    simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 400*p) (n := n) (k := 400)
        (by omega_using [hp]) (by omega_using [hk, hn]) (by omega_using [hp])
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p)) (n := n) (k := 168)
        (by omega_using [hn, h0]) (by omega_using [hk, hn]) (by omega_using [hp])
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p+1)) (n := n) (k := 168)
        (by omega_using [hn, h1]) (by omega_using [hk, hn]) (by omega_using [hp])
    · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 4880) (n := n) (k := 136)
        (by omega_using [hk, hn]) (by omega_using [hk, hn]) (by decide)
  exact hd _ (Offset.contains_base (bufP σ k) (by omega_using [hj]) (by omega_using [hn, hj]))

theorem last_stored_keep {v p k : Nat} {σ s t : State} {L : List Zq}
    (hp : Pre v σ) (hp2 : p<2) (hk : k<v) (hL : L.length≤256)
    (hf : Frame (lastWrites σ p) s.mem t.mem) (hs : Stored s.mem (polyP σ k) L) :
    Stored t.mem (polyP σ k) L := by
  apply stored_frame hf _ hs hL
  intro r hr
  exact (hp.a_scr.sub_left (poly_sub hk)).sub_right
    (fun x hx => (Region.sub_prefix (by decide : 7968≤8192)) x (lastWrites_low hp2 r hr x hx))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejLastProgress.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F F_block)
open VG.Proof.Sha3.AArch64.Neon (PairAt)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted RateBlock)
open VG.Spec.MlDsa (Zq)

structure LastProgress (v : Nat) (σ : State) (L : Nat → List Zq) (phase : Nat) (s : State) : Prop where
  env : Env v σ s
  pairs : ∀p,2*p+1<v → PairAt s.mem (stateP σ p)
    (permuted (A0 σ (2*p)) (if p<phase then 6 else 5))
    (permuted (A0 σ (2*p+1)) (if p<phase then 6 else 5))
  bytes : ∀k<v,∀j<(if k<2*phase then 1008 else 840),
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j
  length : ∀k<v,(L k).length≤256
  counts : ∀k<v,(s.mem.readW (countP σ k) 64).toNat=256-(L k).length
  stored : ∀k<v,Stored s.mem (polyP σ k) (L k)

theorem Rows.lastProgress {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 5 σ L s) : LastProgress v σ L 0 s := by
  refine ⟨h.env,?_,?_,h.length,h.counts,h.stored⟩
  · simpa only [Nat.not_lt_zero,ite_false] using h.pairs
  · simpa only [Nat.mul_zero,Nat.not_lt_zero,ite_false] using h.bytes

theorem LastProgress.rows {v phase : Nat} {σ s : State} {L : Nat → List Zq}
    (h : LastProgress v σ L phase s) (hn : v≤2*phase) : Rows v 6 σ L s := by
  refine ⟨h.env,by decide,?_,?_,h.length,h.counts,h.stored⟩
  · intro p hp
    simpa only [ite_eq_left (by omega_using [hn, hp] : p<phase)] using h.pairs p hp
  · intro k hk
    simpa only [ite_eq_left (by omega_using [hn, hk] : k<2*phase)] using h.bytes k hk

theorem lastRate_byte {σ t : State} {k j : Nat} (hj : 840≤j) (hn : j<1008)
    (h : RateBlock t.mem (lastPtr σ k) 10 (permuted (A0 σ k) 6)) :
    t.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j := by
  have hx := h.byte (j := j-840) (by omega_using [hn])
  change t.mem ((bufP σ k+BitVec.ofNat 64 840)+BitVec.ofNat 64 (j-840))=_ at hx
  rw [Offset.add_add,show 840+(j-840)=j by omega_using [hj],Resident.permuted_eq_iterF] at hx
  rw [hx]
  have hf := F_block σ k (n := 5) (j := j-840) (by decide) (by omega_using [hn])
  simpa only [show 168*5+(j-840)=j by omega_using [hj]] using hf.symm

theorem LastProgress.next {v p : Nat} {σ s t : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : LastProgress v σ L p s) (hpv : 2*p+1<v)
    (he : Env v σ t) (hf : Frame (lastWrites σ p) s.mem t.mem)
    (hpair : PairAt t.mem (stateP σ p) (permuted (A0 σ (2*p)) 6) (permuted (A0 σ (2*p+1)) 6))
    (ha : RateBlock t.mem (lastPtr σ (2*p)) 10 (permuted (A0 σ (2*p)) 6))
    (hb : RateBlock t.mem (lastPtr σ (2*p+1)) 10 (permuted (A0 σ (2*p+1)) 6)) :
    LastProgress v σ L (p+1) t := by
  have hp2 : p<2 := by have:=hp.streams; omega_using [hpv, this]
  refine ⟨he,?_,?_,h.length,?_,?_⟩
  · intro q hq
    by_cases heq : q=p
    · subst q
      simpa only [ite_eq_left (Nat.lt_succ_self p)] using hpair
    · have hi : (q<p+1)↔(q<p) := by omega_using [heq]
      simpa only [hi] using last_pair_keep hp2 (by have:=hp.streams; omega_using [hq, this]) (Ne.symm heq) hf (h.pairs q hq)
  · intro k hk j hj
    have hk4 : k<4 := by have:=hp.streams; omega_using [hk, this]
    by_cases haeq : k=2*p
    · subst k
      have hjn : j<1008 := by simpa only [ite_eq_left (by omega_using [] : 2*p<2*(p+1))] using hj
      by_cases hj0 : j<840
      · rw [last_buffer_keep hp2 hk4 (n := 840) (by decide) hj0 (by omega_using []) (by omega_using []) hf]
        exact h.bytes (2*p) hk j (by simpa only [Nat.lt_irrefl,ite_false])
      · exact lastRate_byte (by omega_using [hj0]) hjn ha
    · by_cases hbeq : k=2*p+1
      · subst k
        have hjn : j<1008 := by simpa only [ite_eq_left (by omega_using [] : 2*p+1<2*(p+1))] using hj
        by_cases hj0 : j<840
        · rw [last_buffer_keep hp2 hk4 (n := 840) (by decide) hj0 (by omega_using []) (by omega_using []) hf]
          exact h.bytes (2*p+1) hk j (by simpa only [ite_eq_right (by omega_using [] : ¬2*p+1<2*p)])
        · exact lastRate_byte (by omega_using [hj0]) hjn hb
      · have hi : (k<2*(p+1))↔(k<2*p) := by omega_using [haeq, hbeq]
        have hold : j<(if k<2*p then 1008 else 840) := by simpa only [hi] using hj
        rw [last_buffer_keep hp2 hk4 (n := if k<2*p then 1008 else 840)
          (by split <;> omega_using []) hold (fun heq => False.elim (haeq heq))
          (fun heq => False.elim (hbeq heq)) hf]
        exact h.bytes k hk j hold
  · intro k hk
    rw [last_count_keep hp2 (by have:=hp.streams; omega_using [hk, this]) hf]
    exact h.counts k hk
  · intro k hk
    exact last_stored_keep hp hp2 hk (h.length k hk) hf (h.stored k hk)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

end


/-! ## From `ResidentRejParseFive.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

private theorem afterFirst {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 0 168 []) s) :
    Rows v 5 σ (fun k => prefixRow σ k 504) s := h.congr (fun _ _ => rfl)

private theorem afterSecond {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 504 112 (prefixRow σ k 504)) s) :
    Rows v 5 σ (fun k => prefixRow σ k 840) s :=
  h.congr (fun k _ => rowResult_prefix σ k 504 112 (by decide))

theorem parseFiveFour_ok {σ s : State} (hp : Pre 4 σ) (h : FirstBlocks 4 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 504 112)) s
      (Rows 4 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchFour_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchFour_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseFiveTwo_ok {σ s : State} (hp : Pre 2 σ) (h : FirstBlocks 2 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 504 112)) s
      (Rows 2 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchTwo_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchTwo_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseSixthFour_ok {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56) s
      (Rows 4 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchFour_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

theorem parseSixthTwo_ok {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56) s
      (Rows 2 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchTwo_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejLastStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (RegKeep)
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Spec.MlDsa (Zq)

theorem lastProgress_ok {v p : Nat} {σ s : State} {L : Nat → List Zq} {rp ra rb : Reg}
    (hp : Pre v σ) (h : LastProgress v σ L p s) (hpv : 2*p+1<v)
    (hr : FiveRegisters rp ra rb) (hreg : CallRegs rp ra rb) (hrp : s.gpr rp=stateP σ p)
    (ha : s.gpr ra=lastPtr σ (2*p)) (hb : s.gpr rb=lastPtr σ (2*p+1)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      LastProgress v σ L (p+1) t ∧ RegKeep blockRegs s t := by
  refine WP.mono (lastPair_ok hp h.env hpv hr hreg
    (by simpa only [Nat.lt_irrefl,ite_false] using h.pairs p hpv) hrp ha hb)
    fun t ⟨he,hs,oa,ob,hf,hg⟩ => ⟨h.next hp hpv he hf hs oa ob,hg⟩

theorem lastAdvance_ok {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 6 σ L s) (h28 : s.gpr .x28=1) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.advance) s fun t =>
      Rows v 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.advance_ok s)
    fun t ⟨ht,_,hcount⟩ => ⟨h.of_control ht ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [eval_nonzero,hcount,h28]
    rfl

theorem lastFour_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0) (h23 : s.gpr .x23=stateP σ 1)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h26 : s.gpr .x26=lastPtr σ 2) (h27 : s.gpr .x27=lastPtr σ 3)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.step s fun t =>
      Rows 4 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<4)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  apply WP.seq
  refine WP.mono (lastProgress_ok hp ha (by decide : 2*1+1<4) fiveRegisters1 callRegs1
    (by rw [hga.gpr .x23 (by decide)]; exact h23)
    (by rw [hga.gpr .x26 (by decide)]; exact h26)
    (by rw [hga.gpr .x27 (by decide)]; exact h27)) fun b ⟨hb,hgb⟩ => ?_
  exact lastAdvance_ok (hb.rows (by decide)) (by
    rw [hgb.gpr .x28 (by decide),
      hga.gpr .x28 (by decide),h28])

theorem lastTwo_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step s fun t =>
      Rows 2 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<2)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  exact lastAdvance_ok (ha.rows (by decide)) (by
    rw [hga.gpr .x28 (by decide),h28])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSixthSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_addImm wp_movz)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Four (squeezeSetup)

def sixthOffsets : List Instr :=
  [.addImm .x .x24 .x24 840,.addImm .x .x25 .x25 840,
   .addImm .x .x26 .x26 840,.addImm .x .x27 .x27 840,.movz .x .x28 1 0]

theorem sixthOffsets_ok (s : State) : WP isa (.block sixthOffsets) s fun t =>
    Only [.x24,.x25,.x26,.x27,.x28] s t ∧
      (∀k<4,t.gpr (bReg k)=s.gpr (bReg k)+840) ∧ t.gpr .x28=1 := by
  unfold sixthOffsets
  refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun c hc ec => wp_addImm (by decide) fun d hd ed =>
      wp_movz fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((((ha.trans hb).trans hc).trans hd).trans ht).mono (by simp)
  · intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · change t.gpr .x24=s.gpr .x24+840
      rw [ht.get .x24,hd.get .x24,hc.get .x24,hb.get .x24,ea]; rfl
    · change t.gpr .x25=s.gpr .x25+840
      rw [ht.get .x25,hd.get .x25,hc.get .x25,eb,ha.get .x25]; rfl
    · change t.gpr .x26=s.gpr .x26+840
      rw [ht.get .x26,hd.get .x26,ec,hb.get .x26,ha.get .x26]; rfl
    · change t.gpr .x27=s.gpr .x27+840
      rw [ht.get .x27,ed,hc.get .x27,hb.get .x27,ha.get .x27]; rfl
  · rw [et]; rfl

theorem sixthSetup_ok (s : State) : WP isa (.block (squeezeSetup 840 1)) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧
      t.gpr .x22=s.gpr .x19 ∧ t.gpr .x23=s.gpr .x19+400 ∧
      (∀k<4,t.gpr (bReg k)=s.gpr .x19+BitVec.ofNat 64 (840+1008*k+840)) ∧
      t.gpr .x28=1 := by
  rw [show squeezeSetup 840 1=(squeezeSetup 0 0).take 6++sixthOffsets from rfl,
    WP.block_append_iff]
  refine WP.mono (squeezePointers_ok s) fun a ⟨ha,h22,h23,hbuf⟩ => ?_
  refine WP.mono (sixthOffsets_ok a) fun t ⟨ht,hptr,h28⟩ => ?_
  refine ⟨(ha.trans ht).mono (by simp),?_,?_,?_,h28⟩
  · rw [ht.get .x22,h22]
  · rw [ht.get .x23,h23]; rfl
  · intro k hk
    rw [hptr k hk,hbuf k hk]
    change (s.gpr .x19+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 840=_
    rw [Offset.add_add]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSixth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)

private theorem sixthSetup_rows {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 5 σ L s) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeSetup 840 1)) s fun t =>
      Rows v 5 σ L t ∧ t.gpr .x22=stateP σ 0 ∧ t.gpr .x23=stateP σ 1 ∧
      (∀k<4,t.gpr (bReg k)=lastPtr σ k) ∧ t.gpr .x28=1 := by
  refine WP.mono (sixthSetup_ok s) fun t ⟨ht,h22,h23,hbuf,h28⟩ => ?_
  refine ⟨h.of_control ht ?_,?_,?_,?_,h28⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [h22,h.env.x19]
    change scr σ=scr σ+BitVec.ofNat 64 0
    simp
  · rw [h23,h.env.x19]; rfl
  · intro k hk
    rw [hbuf k hk,h.env.x19,lastPtr_eq]
    congr 2
    omega_using []

theorem sixthFour_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1) s (Rows 4 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,h23,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastFour_step_ok hp ha h22 h23
    (hbuf 0 (by decide)) (hbuf 1 (by decide)) (hbuf 2 (by decide)) (hbuf 3 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

theorem sixthTwo_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1) s (Rows 2 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,_,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastTwo_step_ok hp ha h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejAdaptive.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

/-- The selected adaptive branch either has all rows already full or consumes exactly one final rate block. -/
theorem adaptiveFour_ok {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 4 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56) (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.flags)))) s (Done 4 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil (h.early_done hf hz)
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthFour_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthFour_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ => ht.done hft

/-- The selected adaptive branch either has all rows already full or consumes exactly one final rate block. -/
theorem adaptiveTwo_ok {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 5 σ (fun k => prefixRow σ k 840) s)
    (hf : Flags 2 (fun k => prefixRow σ k 840) s) :
    WP isa (.ite (.zero .x .x27) (.block [])
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1)
        (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56) (.block Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.flags)))) s (Done 2 σ) := by
  by_cases hz : s.gpr .x27=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil (h.early_done hf hz)
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (s.gpr .x27==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (sixthTwo_ok hp h) fun a ha => ?_
    apply WP.seq
    refine WP.mono (parseSixthTwo_ok hp ha) fun b hb => ?_
    exact WP.mono (flagsSemantic_ok hp hb) fun _ ⟨ht,hft⟩ => ht.done hft

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFive

/-! ## From `ResidentRejPair.lean` -/

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
  refine WP.seq (WP.mono (X2.call_ok true (by decide) hp1 hp hw hpw hpair hcov) fun t ⟨hk,hf,hpt⟩ => ?_)
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
  · exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega)
  · change Region.Sub ⟨(scr σ+BitVec.ofNat 64 (840+1008*(2*p)))+BitVec.ofNat 64 840,168⟩ (lowR σ)
    rw [Offset.add_add]
    exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega)
  · change Region.Sub ⟨(scr σ+BitVec.ofNat 64 (840+1008*(2*p+1)))+BitVec.ofNat 64 840,168⟩ (lowR σ)
    rw [Offset.add_add]
    exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave; omega)
  · exact Offset.sub_base (scr σ) (by decide)

theorem lastPtr_eq (σ : State) (k : Nat) : lastPtr σ k=scr σ+BitVec.ofNat 64 (1680+1008*k) := by
  change (scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 840=_
  rw [Offset.add_add,show 840+1008*k+840=1680+1008*k by omega]

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
  have hp2 : p<2 := by have:=hp.streams; omega
  have hword (i : Nat) (hi : i<25) : InRegions s.wr (wordAddr (stateP σ p) i) 16 := by
    change InRegions s.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*i)) 16
    rw [Offset.add_add]
    exact in_scr hp he.wr (by omega)
  have hbuf (k : Nat) (hk : k<4) (d n : Nat) (hd : d+n≤168) :
      InRegions s.wr (lastPtr σ k+BitVec.ofNat 64 d) n := by
    rw [lastPtr_eq,Offset.add_add]
    exact in_scr hp he.wr (by omega)
  have hsw : s.wr = [aR v σ,scrR σ] := he.wr.trans hp.wr
  refine WP.mono (pair_ok hrp ha hb (by rw [he.x19]) hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2
    hr.a6 hr.a7 hr.b6 hr.b7 hpair
    (fun i hi => by obtain ⟨r,hr,hc⟩ := hword i hi; exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩)
    (fun i hi => hbuf (2*p) (by omega) (16*i) 16 (by omega))
    (fun i hi => hbuf (2*p+1) (by omega) (16*i) 16 (by omega))
    (hbuf (2*p) (by omega) 160 8 (by decide)) (hbuf (2*p+1) (by omega) 160 8 (by decide))
    (by
      rw [lastPtr_eq,lastPtr_eq]
      exact Offset.disjoint (scr σ)
        (d := 1680+1008*(2*p)) (e := 1680+1008*(2*p+1)) (n := 168) (k := 168)
        (by omega) (by omega) (by omega))
    (by
      rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*p)
        (e := 1680+1008*(2*p)) (n := 400) (k := 168) (by omega) (by omega) (by omega))
    (by
      rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*p)
        (e := 1680+1008*(2*p+1)) (n := 400) (k := 168) (by omega) (by omega) (by omega))
    (Offset.disjoint (scr σ) (d := 400*p) (e := 4880) (n := 400) (k := 136)
      (by omega) (by omega) (by decide))
    (by
      rw [hsw]
      refine Covers.of_sub fun r hr => ⟨scrR σ,by simp,?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨400*p,rfl,by change 400*p+400 ≤ 8192; omega⟩
      · exact ⟨4880,rfl,by change 4880+136 ≤ 8192; decide⟩))
    fun t ⟨ht,hpt,ha,hb,hf⟩ => ?_
  refine ⟨he.lowStep hf (lastWrites_low hp2) ht.rd ht.wr ht.sp ?_,hpt,ha,hb,hf,ht⟩
  intro r hm
  apply ht.gpr r; simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

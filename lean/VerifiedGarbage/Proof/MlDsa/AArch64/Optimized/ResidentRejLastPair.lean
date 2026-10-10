import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPair

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

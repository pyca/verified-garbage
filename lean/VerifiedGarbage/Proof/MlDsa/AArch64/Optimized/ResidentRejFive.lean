import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFiveFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted StreamOutput)

/-- Register assignment for either resident pair; all public wrapper pointers survive. -/
structure FiveRegisters (rp ra rb : Reg) : Prop where
  pa : rp≠ra
  pb : rp≠rb
  p28 : rp≠.x28
  p6 : rp≠.x6
  p7 : rp≠.x7
  p16 : rp≠.x16
  a6 : ra≠.x6
  a7 : ra≠.x7
  a16 : ra≠.x16
  a28 : ra≠.x28
  b6 : rb≠.x6
  b7 : rb≠.x7
  b16 : rb≠.x16
  b28 : rb≠.x28
  ab : ra≠rb
  safe : ∀r∈[Reg.x19,.x20,.x21,.x30],r≠ra ∧ r≠rb

theorem fiveRegisters0 : FiveRegisters .x22 .x24 .x25 := by
  constructor <;> decide

theorem fiveRegisters1 : FiveRegisters .x23 .x26 .x27 := by
  constructor <;> decide

theorem fiveEnv_ok {v p : Nat} {σ s : State} {rp ra rb : Reg}
    (hp : Pre v σ) (he : Env v σ s) (hpn : 2*p+1<v) (hr : FiveRegisters rp ra rb)
    (hpair : PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hrp : s.gpr rp=stateP σ p) (ha : s.gpr ra=bufP σ (2*p))
    (hb : s.gpr rb=bufP σ (2*p+1)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.five rp ra rb) s fun t =>
      Env v σ t ∧
      PairAt t.mem (stateP σ p) (permuted (A0 σ (2*p)) 5) (permuted (A0 σ (2*p+1)) 5) ∧
      StreamOutput t.mem (bufP σ (2*p)) 10 5 (A0 σ (2*p)) ∧
      StreamOutput t.mem (bufP σ (2*p+1)) 10 5 (A0 σ (2*p+1)) ∧
      Frame (fiveWrites σ p) s.mem t.mem ∧
      (∀r,r≠ra → r≠rb → r≠.x28 → r≠.x6 → r≠.x7 → r≠.x16 → t.gpr r=s.gpr r) := by
  have hp2 : p<2 := by have:=hp.streams; omega
  have hword (i : Nat) (hi : i<25) :
      InRegions s.wr (wordAddr (stateP σ p) i) 16 := by
    change InRegions s.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*i)) 16
    rw [Offset.add_add]
    exact in_scr hp he.wr (by omega)
  have hbuf (k : Nat) (hk : k<4) (j d n : Nat) (hj : j<5) (hd : d+n≤168) :
      InRegions s.wr ((bufP σ k+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 d) n := by
    change InRegions s.wr (((scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 (168*j))+
      BitVec.ofNat 64 d) n
    rw [Offset.add_add,Offset.add_add]
    exact in_scr hp he.wr (by omega)
  refine WP.mono (five_ok hpair hrp ha hb hr.pa hr.pb hr.p28 hr.p6 hr.p7 hr.p16
    hr.a6 hr.a7 hr.a16 hr.a28 hr.b6 hr.b7 hr.b16 hr.b28 hr.ab
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p)) (e := 840+1008*(2*p+1))
      (n := 840) (k := 840) (by omega) (by omega) (by omega))
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p)) (e := 400*p)
      (n := 840) (k := 400) (by omega) (by omega) (by omega))
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p+1)) (e := 400*p)
      (n := 840) (k := 400) (by omega) (by omega) (by omega))
    (fun i hi => by
      obtain ⟨r,hr,hc⟩ := hword i hi
      exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩) hword
    (fun j hj i hi => hbuf (2*p) (by omega) j (16*i) 16 hj (by omega))
    (fun j hj i hi => hbuf (2*p+1) (by omega) j (16*i) 16 hj (by omega))
    (fun j hj => hbuf (2*p) (by omega) j 160 8 hj (by decide))
    (fun j hj => hbuf (2*p+1) (by omega) j 160 8 hj (by decide)))
    fun t ⟨ht,oa,ob,hf,hg,hrd,hwr,hsp⟩ => ?_
  refine ⟨he.lowStep hf (fiveWrites_low hp2) hrd hwr hsp ?_,ht,oa,ob,hf,hg⟩
  intro r hrmem
  obtain ⟨hra,hrb⟩ := hr.safe r hrmem
  apply hg r hra hrb <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hrmem <;>
    rcases hrmem with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

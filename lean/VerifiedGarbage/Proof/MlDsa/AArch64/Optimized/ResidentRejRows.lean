module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqBlock
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejCounts
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze

/-! ### `MlDsa.AArch64.Optimized.ResidentRejFive`, which this module and modules that import it used -/

section

/-! ## From `ResidentRejFiveFrame.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Exact writes of one resident five-block pair, excluding other streams and counts. -/
def fiveWrites (σ : State) (p : Nat) : List Region :=
  [⟨bufP σ (2*p),840⟩,⟨bufP σ (2*p+1),840⟩,pairR (stateP σ p),⟨scr σ+BitVec.ofNat 64 7296,384⟩]

theorem fiveWrites_low {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈fiveWrites σ p,Region.Sub r (lowR σ) := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega_arith)
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega_arith)
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega_arith)
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega_arith)

theorem fiveWrites_count {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈fiveWrites σ p,(countR σ).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 840+1008*(2*p))
      (n := 32) (k := 840) (by omega_arith) (by decide) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 840+1008*(2*p+1))
      (n := 32) (k := 840) (by omega_arith) (by decide) (by omega_arith)
  · exact (pair_count_disjoint σ hp).symm
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 7296)
      (n := 32) (k := 384) (by omega_arith) (by decide) (by decide)

theorem fiveWrites_other {σ : State} {p q : Nat} (hp : p<2) (hq : q<2) (hne : p≠q) :
    ∀r∈fiveWrites σ p,(pairR (stateP σ q)).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 840+1008*(2*p))
      (n := 400) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 840+1008*(2*p+1))
      (n := 400) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 400*p)
      (n := 400) (k := 400) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 7296)
      (n := 400) (k := 384) (by omega_arith) (by omega_arith) (by omega_arith)

theorem fiveWrites_buffer {σ : State} {p k : Nat} (hp : p<2) (hk : k<4)
    (h0 : k≠2*p) (h1 : k≠2*p+1) :
    ∀r∈fiveWrites σ p,(Region.mk (bufP σ k) 840).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 840+1008*(2*p))
      (n := 840) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 840+1008*(2*p+1))
      (n := 840) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 400*p)
      (n := 840) (k := 400) (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 7296)
      (n := 840) (k := 384) (by omega_arith) (by omega_arith) (by omega_arith)

theorem five_pair_keep {σ : State} {p q : Nat} {s t : State} {A B : Spec.Sha3.State}
    (hp : p<2) (hq : q<2) (hne : p≠q) (hf : Frame (fiveWrites σ p) s.mem t.mem)
    (hpair : PairAt s.mem (stateP σ q) A B) : PairAt t.mem (stateP σ q) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ q) hi) (fiveWrites_other hp hq hne) (by decide)]
  exact hpair i hi

theorem five_count_keep {σ : State} {p k : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hf : Frame (fiveWrites σ p) s.mem t.mem) :
    t.mem.readW (countP σ k) 64=s.mem.readW (countP σ k) 64 := by
  apply hf.readW
  · exact Offset.contains (scr σ) (d := 7904+8*k) (e := 7904) (n := 8) (k := 32)
      (by omega_arith) (by omega_arith) (by decide)
  · exact fiveWrites_count hp
  · decide

theorem five_stream_keep {σ : State} {p k : Nat} {s t : State} {A : Spec.Sha3.State}
    (hp : p<2) (hk : k<4) (h0 : k≠2*p) (h1 : k≠2*p+1)
    (hf : Frame (fiveWrites σ p) s.mem t.mem)
    (hs : Resident.StreamOutput s.mem (bufP σ k) 10 5 A) :
    Resident.StreamOutput t.mem (bufP σ k) 10 5 A := by
  intro i hi
  refine (hs i hi).keep (by decide) hf ?_
  intro r hr
  exact (fiveWrites_buffer hp hk h0 h1 r hr).sub_left (Offset.sub_base (bufP σ k) (by omega_arith))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFive.lean` -/

section

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
  p15 : rp≠.x15
  a15 : ra≠.x15
  b15 : rb≠.x15
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
      (∀r,r≠ra → r≠rb → r≠.x28 → r≠.x6 → r≠.x7 → r≠.x16 → r≠.x15 → t.gpr r=s.gpr r) := by
  have hp2 : p<2 := by have:=hp.streams; omega_arith
  have hword (i : Nat) (hi : i<25) :
      InRegions s.wr (wordAddr (stateP σ p) i) 16 := by
    change InRegions s.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*i)) 16
    rw [Offset.add_add]
    exact in_scr hp he.wr (by omega_arith)
  have hbuf (k : Nat) (hk : k<4) (j d n : Nat) (hj : j<5) (hd : d+n≤168) :
      InRegions s.wr ((bufP σ k+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 d) n := by
    change InRegions s.wr (((scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 (168*j))+
      BitVec.ofNat 64 d) n
    rw [Offset.add_add,Offset.add_add]
    exact in_scr hp he.wr (by omega_arith)
  refine WP.mono (fiveWith_ok Resident.originalCore hpair hrp ha hb hr.pa hr.pb hr.p28 hr.p6 hr.p7 hr.p16
    hr.a6 hr.a7 hr.a16 hr.a28 hr.b6 hr.b7 hr.b16 hr.b28 hr.ab
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p)) (e := 840+1008*(2*p+1))
      (n := 840) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith))
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p)) (e := 400*p)
      (n := 840) (k := 400) (by omega_arith) (by omega_arith) (by omega_arith))
    (Offset.disjoint (scr σ) (d := 840+1008*(2*p+1)) (e := 400*p)
      (n := 840) (k := 400) (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi => by
      obtain ⟨r,hr,hc⟩ := hword i hi
      exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩) hword
    (fun j hj i hi => hbuf (2*p) (by omega_arith) j (16*i) 16 hj (by omega_arith))
    (fun j hj i hi => hbuf (2*p+1) (by omega_arith) j (16*i) 16 hj (by omega_arith))
    (fun j hj => hbuf (2*p) (by omega_arith) j 160 8 hj (by decide))
    (fun j hj => hbuf (2*p+1) (by omega_arith) j 160 8 hj (by decide))
    hr.p15 hr.a15 hr.b15 (by decide) (by rw [he.x19])
    (fun i hi => by rw [Offset.add_add]; exact in_scr hp he.wr (by omega_arith))
    (fun r hr => by rw [Offset.add_add]; exact in_scr hp he.wr (by omega_arith))
    (Offset.disjoint (scr σ) (d := 7296) (e := 840+1008*(2*p))
      (n := 384) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith))
    (Offset.disjoint (scr σ) (d := 7296) (e := 840+1008*(2*p+1))
      (n := 384) (k := 840) (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t ⟨ht,oa,ob,hf,hg,hrd,hwr,hsp⟩ => ?_
  refine ⟨he.lowStep hf (fiveWrites_low hp2) hrd hwr hsp ?_,ht,oa,ob,hf,hg⟩
  intro r hrmem
  obtain ⟨hra,hrb⟩ := hr.safe r hrmem
  apply hg r hra hrb <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hrmem <;>
    rcases hrmem with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

end

end

/-! ## From `ResidentRejFirstBytes.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResidentRejFirstBlocks.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted StreamOutput)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)

structure FirstBlocks (v : Nat) (σ t : State) : Prop where
  env : Env v σ t
  pairs : ∀p,2*p+1<v → PairAt t.mem (stateP σ p)
    (permuted (A0 σ (2*p)) 5) (permuted (A0 σ (2*p+1)) 5)
  bytes : ∀k<v,StreamOutput t.mem (bufP σ k) 10 5 (A0 σ k)
  counts : ∀k<v,t.mem.readW (countP σ k) 64=256

theorem firstFour_ok {σ s : State} (hp : Pre 4 σ) (he : Env 4 σ s)
    (hs : ∀p,2*p+1<4 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<4,s.mem.readW (countP σ k) 64=256)
    (h22 : s.gpr .x22=stateP σ 0) (h23 : s.gpr .x23=stateP σ 1)
    (hbuf : ∀k<4,s.gpr (bReg k)=bufP σ k) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x23 .x26 .x27)) s (FirstBlocks 4 σ) := by
  apply WP.seq
  refine WP.mono (fiveEnv_ok hp he (by decide : 2*0+1<4) fiveRegisters0
    (hs 0 (by decide)) h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)))
    fun u ⟨heu,hpu,hu0,hu1,hfu,hgu⟩ => ?_
  refine WP.mono (fiveEnv_ok hp heu (by decide : 2*1+1<4) fiveRegisters1
    (five_pair_keep (by decide : 0<2) (by decide : 1<2) (by decide) hfu (hs 1 (by decide)))
    (by rw [hgu .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h23)
    (by rw [hgu .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbuf 2 (by decide))
    (by rw [hgu .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbuf 3 (by decide)))
    fun t ⟨het,hpt,ht2,ht3,hft,_⟩ => ?_
  refine ⟨het,?_,?_,?_⟩
  · intro p hpn
    rcases (show p=0 ∨ p=1 by omega_using [hpn]) with rfl | rfl
    · exact five_pair_keep (by decide : 1<2) (by decide : 0<2) (by decide) hft hpu
    · exact hpt
  · intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · exact five_stream_keep (by decide : 1<2) (by decide : 0<4) (by decide) (by decide) hft hu0
    · exact five_stream_keep (by decide : 1<2) (by decide : 1<4) (by decide) (by decide) hft hu1
    · exact ht2
    · exact ht3
  · intro k hk
    rw [five_count_keep (by decide : 1<2) hk hft,five_count_keep (by decide : 0<2) hk hfu]
    exact hc k hk

theorem firstTwo_ok {σ s : State} (hp : Pre 2 σ) (he : Env 2 σ s)
    (hs : ∀p,2*p+1<2 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<2,s.mem.readW (countP σ k) 64=256)
    (h22 : s.gpr .x22=stateP σ 0)
    (hbuf : ∀k<2,s.gpr (bReg k)=bufP σ k) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25) s (FirstBlocks 2 σ) := by
  refine WP.mono (fiveEnv_ok hp he (by decide : 2*0+1<2) fiveRegisters0
    (hs 0 (by decide)) h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)))
    fun t ⟨het,hpt,ht0,ht1,hft,_⟩ => ?_
  refine ⟨het,?_,?_,?_⟩
  · intro p hpn
    have : p=0 := by omega_using [hpn]
    subst p; exact hpt
  · intro k hk
    rcases (show k=0 ∨ k=1 by omega_using [hk]) with rfl | rfl
    · exact ht0
    · exact ht1
  · intro k hk
    rw [five_count_keep (by decide : 0<2) (by omega_using [hk] : k<4) hft]
    exact hc k hk

theorem firstFour_setup_ok {σ s : State} (hp : Pre 4 σ) (he : Env 4 σ s)
    (hs : ∀p,2*p+1<4 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<4,s.mem.readW (countP σ k) 64=256) :
    WP isa (.seq (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeSetup 0 5))
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)
        (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x23 .x26 .x27))) s (FirstBlocks 4 σ) := by
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env he) fun t ⟨het,hm,h22,h23,hbuf⟩ => ?_
  exact firstFour_ok hp het (by simpa only [hm] using hs) (by simpa only [hm] using hc) h22 h23 hbuf

theorem firstTwo_setup_ok {σ s : State} (hp : Pre 2 σ) (he : Env 2 σ s)
    (hs : ∀p,2*p+1<2 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<2,s.mem.readW (countP σ k) 64=256) :
    WP isa (.seq (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeSetup 0 5))
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)) s (FirstBlocks 2 σ) := by
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env he) fun t ⟨het,hm,h22,_,hbuf⟩ => ?_
  exact firstTwo_ok hp het (by simpa only [hm] using hs) (by simpa only [hm] using hc)
    h22 (fun k hk => hbuf k (by omega_using [hk]))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F F_block)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (StreamOutput)

theorem firstStream_byte {σ s : State} {k : Nat}
    (h : StreamOutput s.mem (bufP σ k) 10 5 (A0 σ k)) {j : Nat} (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j := by
  have hb := (h (j/168) (by omega_arith)).byte (j := j%168) (by omega_arith)
  change s.mem ((bufP σ k+BitVec.ofNat 64 (168*(j/168)))+BitVec.ofNat 64 (j%168)) = _ at hb
  rw [Offset.add_add,Nat.div_add_mod] at hb
  rw [hb,Resident.permuted_eq_iterF]
  exact (F_block σ k (by omega_arith : j/168<6) (by omega_arith : j%168<168)).symm.trans
    (congrArg (F σ k) (Nat.div_add_mod j 168))

theorem FirstBlocks.byte {v : Nat} {σ s : State} (h : FirstBlocks v σ s)
    {k j : Nat} (hk : k<v) (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j :=
  firstStream_byte (h.bytes k hk) hj

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentEnv.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

def segmentWrites (σ : State) (k : Nat) : List Region :=
  [polyR (polyP σ k),⟨countP σ k,8⟩]

theorem segmentWrites_sub {v k : Nat} {σ : State} (hk : k<v) (hv : v≤4) :
    ∀r∈segmentWrites σ k,∃R∈[aR v σ,scrR σ],Region.Sub r R := by
  intro r hr
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨aR v σ,by simp,poly_sub hk⟩
  · exact ⟨scrR σ,by simp,Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega_arith)⟩

theorem segmentWrites_save {v k : Nat} {σ : State} (hp : Pre v σ) (hk : k<v) :
    ∀r∈segmentWrites σ k,(saveR σ).Disjoint r := by
  intro r hr
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.a_scr.sub_left (poly_sub hk)).symm).sub_left
      (Offset.sub_base (scr σ) (by decide))
  · exact Offset.disjoint (scr σ) (d := 7968) (e := 7904+8*k) (n := 144) (k := 8)
      (by have:=hp.streams; omega_arith) (by decide) (by have:=hp.streams; omega_arith)

/-- The segment loop's pointers at stream `k`: its input (at offset `off`),
output and count slot. -/
def Ptrs (σ : State) (off k : Nat) (s : State) : Prop :=
  s.gpr .x24=bufP σ k+BitVec.ofNat 64 off ∧ s.gpr .x25=polyP σ k ∧ s.gpr .x26=countP σ k

theorem Ptrs.next {σ t : State} {off k : Nat}
    (h24 : t.gpr .x24=(bufP σ k+BitVec.ofNat 64 off)+BitVec.ofNat 64 1008)
    (h25 : t.gpr .x25=polyP σ k+BitVec.ofNat 64 1024)
    (h26 : t.gpr .x26=countP σ k+BitVec.ofNat 64 8) : Ptrs σ off (k+1) t := by
  refine ⟨?_,?_,?_⟩
  · rw [h24]
    change ((scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 off)+BitVec.ofNat 64 1008=
      (scr σ+BitVec.ofNat 64 (840+1008*(k+1)))+BitVec.ofNat 64 off
    rw [Offset.add_add,Offset.add_add,Offset.add_add]
    exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by omega_arith)
  · rw [h25]
    change (aP σ+BitVec.ofNat 64 (1024*k))+BitVec.ofNat 64 1024=aP σ+BitVec.ofNat 64 (1024*(k+1))
    rw [Offset.add_add]
    exact congrArg (fun d => aP σ+BitVec.ofNat 64 d) (by omega_arith)
  · rw [h26]
    change (scr σ+BitVec.ofNat 64 (Impl.MlDsa.AArch64.Optimized.ResidentRej.counts+8*k))+
      BitVec.ofNat 64 8=
      scr σ+BitVec.ofNat 64 (Impl.MlDsa.AArch64.Optimized.ResidentRej.counts+8*(k+1))
    rw [Offset.add_add]
    exact congrArg (fun d => scr σ+BitVec.ofNat 64 d) (by omega_arith)

theorem segmentEnv_ok {streams k off n : Nat} {σ s : State} {L : List Zq}
    (hp : Pre streams σ) (he : Env streams σ s) (hk : k<streams) (hptr : Ptrs σ off k s)
    (hn : off+3*n≤1008) (hmod : n%4=0) (hL : L.length≤256)
    (hc : (s.mem.readW (countP σ k) 64).toNat=256-L.length)
    (hs : Stored s.mem (polyP σ k) L) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.segment variant n) s fun t =>
      Env streams σ t ∧ Frame (segmentWrites σ k) s.mem t.mem ∧
      (t.mem.readW (countP σ k) 64).toNat=
        256-(segmentResult s (bufP σ k+BitVec.ofNat 64 off) n L).length ∧
      Stored t.mem (polyP σ k) (segmentResult s (bufP σ k+BitVec.ofNat 64 off) n L) ∧
      Ptrs σ off (k+1) t ∧ t.gpr .x27=s.gpr .x27-BitVec.ofNat 64 1 := by
  have hcount : InRegions s.wr (countP σ k) 8 :=
    in_scr hp he.wr (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega_arith)
  have hread : InRegions (s.rd++s.wr) (countP σ k) 8 := by
    obtain ⟨r,hr,hc⟩ := hcount
    exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩
  have hl := segment_layout hp he hk hn
  rw [segment_input_eq he,segment_output_eq he] at hl
  refine WP.mono (segment_ok variant n (by omega_arith) hL hmod hptr.1 hptr.2.1 hptr.2.2
    hl hread hcount hc hs (by
      exact (hp.a_scr.sub_left (poly_sub hk)).sub_right
        (Offset.sub_base (scr σ) (by
          unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega_arith))))
    fun t ⟨ht,h24,h25,h26,h27,hf,hc,hs⟩ => ?_
  refine ⟨he.frameStep hf (segmentWrites_sub hk (by have:=hp.streams; omega_arith))
    (segmentWrites_save hp hk) ht.rd ht.wr ht.sp ?_,hf,hc,hs,Ptrs.next h24 h25 h26,h27⟩
  intro r hr
  exact ht.get r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

theorem segmentWrites_scratch {v k : Nat} {σ : State} {r : Region}
    (hp : Pre v σ) (hk : k<v) (hr : Region.Sub r (scrR σ))
    (hc : r.Disjoint ⟨countP σ k,8⟩) :
    ∀w∈segmentWrites σ k,r.Disjoint w := by
  intro w hw
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact ((hp.a_scr.sub_left (poly_sub hk)).symm).sub_left hr
  · exact hc

theorem segmentWrites_other_poly {v k j : Nat} {σ : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k) :
    ∀w∈segmentWrites σ k,(polyR (polyP σ j)).Disjoint w := by
  intro w hw
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact Offset.disjoint (aP σ) (d := 1024*j) (e := 1024*k) (n := 1024) (k := 1024)
      (by omega_arith) (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith)
  · exact (hp.a_scr.sub_left (poly_sub hj)).sub_right
      (Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega_arith))

theorem segment_count_keep {v k j : Nat} {σ s t : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) :
    t.mem.readW (countP σ j) 64=s.mem.readW (countP σ j) 64 := by
  apply hf.readW (r := ⟨countP σ j,8⟩) (Region.contains_self _ _) _ (by decide)
  apply segmentWrites_scratch hp hk
  · exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega_arith)
  · exact Offset.disjoint (scr σ) (d := 7904+8*j) (e := 7904+8*k) (n := 8) (k := 8)
      (by omega_arith) (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith)

theorem segment_stored_keep {v k j : Nat} {σ s t : State} {L : List Zq}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) (hL : L.length≤256)
    (hs : Stored s.mem (polyP σ j) L) : Stored t.mem (polyP σ j) L :=
  stored_frame hf (segmentWrites_other_poly hp hk hj hne) hs hL

theorem segment_buffer_keep {v k j d : Nat} {σ s t : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hd : d<1008)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) :
    t.mem (bufP σ j+BitVec.ofNat 64 d)=s.mem (bufP σ j+BitVec.ofNat 64 d) := by
  apply hf
  intro r hr
  apply (segmentWrites_scratch hp hk (r := ⟨bufP σ j,1008⟩)
    (Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf; have:=hp.streams; omega_arith))
    (Offset.disjoint (scr σ) (d := 840+1008*j) (e := 7904+8*k) (n := 1008) (k := 8)
      (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith)) r hr)
  exact Offset.contains_base (bufP σ j) (by omega_arith) (by omega_arith)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejRows.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr pair_contains)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted)
open VG.Spec.MlDsa (Zq)

/-- Per-stream rejection state after a fixed public number of SHAKE blocks. -/
structure Rows (v blocks : Nat) (σ : State) (L : Nat → List Zq) (s : State) : Prop where
  env : Env v σ s
  blockBound : blocks≤6
  pairs : ∀p,2*p+1<v → PairAt s.mem (stateP σ p)
    (permuted (A0 σ (2*p)) blocks) (permuted (A0 σ (2*p+1)) blocks)
  bytes : ∀k<v,∀j<168*blocks,s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j
  length : ∀k<v,(L k).length≤256
  counts : ∀k<v,(s.mem.readW (countP σ k) 64).toNat=256-(L k).length
  stored : ∀k<v,Stored s.mem (polyP σ k) (L k)

theorem FirstBlocks.rows {v : Nat} {σ s : State} (h : FirstBlocks v σ s) :
    Rows v 5 σ (fun _ => []) s := by
  refine ⟨h.env,by decide,h.pairs,fun k hk j hj => h.byte hk hj,by simp,?_,?_⟩
  · intro k hk
    rw [h.counts k hk]
    rfl
  · intro k hk i hi
    simp at hi

def streamBytes (σ : State) (k off n : Nat) : List Byte :=
  (List.range n).map fun j => F σ k (off+j)

def rowResult (σ : State) (k off n : Nat) (L : List Zq) : List Zq :=
  rnFold L (streamBytes σ k off (3*n))

theorem segmentResult_rows {v blocks k off n : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v blocks σ L s) (hk : k<v) (hn : off+3*n≤168*blocks) :
    segmentResult s (bufP σ k+BitVec.ofNat 64 off) n (L k)=rowResult σ k off n (L k) := by
  unfold segmentResult rowResult
  congr 1
  unfold Spec.Sha3.bytesAt streamBytes
  apply List.map_congr_left
  intro j hj
  have hjn : j<3*n := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h.bytes k hk (off+j) (by omega_arith)

theorem segment_pair_keep {v k p : Nat} {σ s t : State} {A B : Spec.Sha3.State}
    (hp : Pre v σ) (hk : k<v) (hpv : 2*p+1<v)
    (hf : Frame (segmentWrites σ k) s.mem t.mem)
    (hs : PairAt s.mem (stateP σ p) A B) : PairAt t.mem (stateP σ p) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (segmentWrites_scratch hp hk
    (Offset.sub_base (scr σ) (by have:=hp.streams; omega_arith))
    (Offset.disjoint (scr σ) (d := 400*p) (e := 7904+8*k) (n := 400) (k := 8)
      (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith) (by have:=hp.streams; omega_arith))) (by decide)]
  exact hs i hi

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLastPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows

/-! ## From `ResidentRejLastFrame.lean` -/

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
      (n := 32) (k := 168) (by omega) (by decide) (by omega)
  · rw [lastPtr_eq]
    exact Offset.disjoint (scr σ) (d := 7904) (e := 1680+1008*(2*p+1))
      (n := 32) (k := 168) (by omega) (by decide) (by omega)
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 4880) (n := 32) (k := 136)
      (by decide) (by decide) (by decide)

theorem last_count_keep {σ : State} {p k : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hf : Frame (lastWrites σ p) s.mem t.mem) :
    t.mem.readW (countP σ k) 64=s.mem.readW (countP σ k) 64 := by
  apply hf.readW
  · exact Offset.contains (scr σ) (d := 7904+8*k) (e := 7904) (n := 8) (k := 32)
      (by omega) (by omega) (by decide)
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
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p)) (n := 400) (k := 168)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p+1)) (n := 400) (k := 168)
        (by omega) (by omega) (by omega)
    · exact Offset.disjoint (scr σ) (d := 400*q) (e := 4880) (n := 400) (k := 136)
        (by omega) (by omega) (by decide)) (by decide)]
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
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p)) (n := n) (k := 168)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p+1)) (n := n) (k := 168)
        (by omega) (by omega) (by omega)
    · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 4880) (n := n) (k := 136)
        (by omega) (by omega) (by decide)
  exact hd _ (Offset.contains_base (bufP σ k) (by omega) (by omega))

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
    simpa only [ite_eq_left (by omega : p<phase)] using h.pairs p hp
  · intro k hk
    simpa only [ite_eq_left (by omega : k<2*phase)] using h.bytes k hk

theorem lastRate_byte {σ t : State} {k j : Nat} (hj : 840≤j) (hn : j<1008)
    (h : RateBlock t.mem (lastPtr σ k) 10 (permuted (A0 σ k) 6)) :
    t.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j := by
  have hx := h.byte (j := j-840) (by omega)
  change t.mem ((bufP σ k+BitVec.ofNat 64 840)+BitVec.ofNat 64 (j-840))=_ at hx
  rw [Offset.add_add,show 840+(j-840)=j by omega,Resident.permuted_eq_iterF] at hx
  rw [hx]
  have hf := F_block σ k (n := 5) (j := j-840) (by decide) (by omega)
  simpa only [show 168*5+(j-840)=j by omega] using hf.symm

theorem LastProgress.next {v p : Nat} {σ s t : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : LastProgress v σ L p s) (hpv : 2*p+1<v)
    (he : Env v σ t) (hf : Frame (lastWrites σ p) s.mem t.mem)
    (hpair : PairAt t.mem (stateP σ p) (permuted (A0 σ (2*p)) 6) (permuted (A0 σ (2*p+1)) 6))
    (ha : RateBlock t.mem (lastPtr σ (2*p)) 10 (permuted (A0 σ (2*p)) 6))
    (hb : RateBlock t.mem (lastPtr σ (2*p+1)) 10 (permuted (A0 σ (2*p+1)) 6)) :
    LastProgress v σ L (p+1) t := by
  have hp2 : p<2 := by have:=hp.streams; omega
  refine ⟨he,?_,?_,h.length,?_,?_⟩
  · intro q hq
    by_cases heq : q=p
    · subst q
      simpa only [ite_eq_left (Nat.lt_succ_self p)] using hpair
    · have hi : (q<p+1)↔(q<p) := by omega
      simpa only [hi] using last_pair_keep hp2 (by have:=hp.streams; omega) (Ne.symm heq) hf (h.pairs q hq)
  · intro k hk j hj
    have hk4 : k<4 := by have:=hp.streams; omega
    by_cases haeq : k=2*p
    · subst k
      have hjn : j<1008 := by simpa only [ite_eq_left (by omega : 2*p<2*(p+1))] using hj
      by_cases hj0 : j<840
      · rw [last_buffer_keep hp2 hk4 (n := 840) (by decide) hj0 (by omega) (by omega) hf]
        exact h.bytes (2*p) hk j (by simpa only [Nat.lt_irrefl,ite_false])
      · exact lastRate_byte (by omega) hjn ha
    · by_cases hbeq : k=2*p+1
      · subst k
        have hjn : j<1008 := by simpa only [ite_eq_left (by omega : 2*p+1<2*(p+1))] using hj
        by_cases hj0 : j<840
        · rw [last_buffer_keep hp2 hk4 (n := 840) (by decide) hj0 (by omega) (by omega) hf]
          exact h.bytes (2*p+1) hk j (by simpa only [ite_eq_right (by omega : ¬2*p+1<2*p)])
        · exact lastRate_byte (by omega) hjn hb
      · have hi : (k<2*(p+1))↔(k<2*p) := by omega
        have hold : j<(if k<2*p then 1008 else 840) := by simpa only [hi] using hj
        rw [last_buffer_keep hp2 hk4 (n := if k<2*p then 1008 else 840)
          (by split <;> omega) hold (fun heq => False.elim (haeq heq))
          (fun heq => False.elim (hbeq heq)) hf]
        exact h.bytes k hk j hold
  · intro k hk
    rw [last_count_keep hp2 (by have:=hp.streams; omega) hf]
    exact h.counts k hk
  · intro k hk
    exact last_stored_keep hp hp2 hk (h.length k hk) hf (h.stored k hk)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Round
public import VerifiedGarbage.Proof.Camellia.Words
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Fl
import VerifiedGarbage.Proof.Framework.Interleave

/-! # Six-round groups using the existing word-oriented Camellia model -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64
open VG.Impl.Camellia.AArch64.Serial

def written : List Reg := [.x6,.x7,.x8,.x10,.x11,.x12,.x16,.x17]

def halves (s : State) : BitVec 64 × BitVec 64 := (s.gpr .x6,s.gpr .x7)

def keyWord (s : State) (j : Nat) : BitVec 64 :=
  rev64 (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 64)

theorem pair_run (s : State) (k : Nat) (hk : k+1 < 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (roundPair k) s = some t ∧
      halves t = VG.Proof.Camellia.pair (keyWord s k) (keyWord s (k+1)) (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨u,ue,uv,uc,um,ut,ug,umem,urd,uwr,usp⟩ :=
    f_run (a := .x6) (b := .x7) (Or.inl rfl) (Or.inr rfl) (by omega) hc hm ht (hr k (by omega))
  have ur : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*(k+1))) 8 := by
    rw [urd,uwr,ug .x5 (by decide) (by decide)]
    exact hr (k+1) hk
  obtain ⟨v,ve,vv,vc,vm,vt,vg,vmem,vrd,vwr,vsp⟩ :=
    f_run (a := .x7) (b := .x6) (Or.inr rfl) (Or.inl rfl) hk uc um ut ur
  refine ⟨v,?_,?_,vc,vm,vt,?_,vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
  · rw [roundPair,VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
  · simp only [halves,VG.Proof.Camellia.pair,keyWord]
    rw [vv,vg .x7 (by decide) (by decide),uv,ug .x6 (by decide) (by decide),
      umem,ug .x5 (by decide) (by decide)]
  · intro r hr
    have h6 : r ≠ .x6 := fun h => hr (h ▸ (by decide : Reg.x6 ∈ written))
    have h7 : r ≠ .x7 := fun h => hr (h ▸ (by decide : Reg.x7 ∈ written))
    have hrest : r ∉ [.x8,.x10,.x11,.x12,.x16,.x17] := by
      intro h
      apply hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    exact (vg r h6 hrest).trans (ug r h7 hrest)

def pairs (K : Nat → BitVec 64) (k n : Nat) (d : BitVec 64 × BitVec 64) :
    BitVec 64 × BitVec 64 :=
  (List.range n).foldl (fun d i => VG.Proof.Camellia.pair (K (k+2*i)) (K (k+2*i+1)) d) d

theorem pairs_succ (K : Nat → BitVec 64) (k n : Nat) (d : BitVec 64 × BitVec 64) :
    pairs K k (n+1) d = VG.Proof.Camellia.pair (K (k+2*n)) (K (k+2*n+1)) (pairs K k n d) := by
  simp only [pairs,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem pairs_run (s : State) (k n : Nat) (hk : k+2*n ≤ 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa ((List.range n).flatMap fun j => roundPair (k+2*j)) s = some t ∧
      halves t = pairs (keyWord s) k n (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s,rfl,rfl,hc,hm,ht,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨u,ue,uv,uc,um,ut,ug,umem,urd,uwr,usp⟩ := ih (by omega)
    have ur : ∀ j < 34, InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8 := by
      intro j hj
      rw [urd,uwr,ug .x5 (by decide)]
      exact hr j hj
    obtain ⟨v,ve,vv,vc,vm,vt,vg,vmem,vrd,vwr,vsp⟩ := pair_run u (k+2*n) (by omega) uc um ut ur
    refine ⟨v,?_,?_,vc,vm,vt,fun r h => (vg r h).trans (ug r h),
      vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
    · rw [vv,pairs_succ,uv]
      simp only [keyWord,umem,ug .x5 (by decide),Nat.add_assoc]

theorem six_run (s : State) (k : Nat) (hk : k+6 ≤ 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (six k) s = some t ∧
      halves t = pairs (keyWord s) k 3 (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  pairs_run s k 3 hk hc hm ht hr

theorem flPair_run (s : State) (k : Nat) (hk : k+1 < 34)
    (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hr : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+8*j)) 8) :
    ∃ t, runBlock isa (flPair k) s = some t ∧
      halves t = (Spec.Camellia.fl (s.gpr .x6) (keyWord s k),
        Spec.Camellia.flinv (s.gpr .x7) (keyWord s (k+1))) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨u,ue,uv,ug,umem,urd,uwr,usp,uvec⟩ :=
    fl_run false (r := .x6) (Or.inl rfl) (by omega) (hr k (by omega))
  have ur : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 (256+8*(k+1))) 8 := by
    rw [urd,uwr,ug .x5 (by decide) (by decide)]
    exact hr (k+1) hk
  obtain ⟨v,ve,vv,vg,vmem,vrd,vwr,vsp,vvec⟩ :=
    fl_run true (r := .x7) (Or.inr rfl) hk ur
  have other : ∀ r, r ∉ written → v.gpr r = s.gpr r := by
    intro r hr
    have h6 : r ≠ .x6 := fun h => hr (h ▸ (by decide : Reg.x6 ∈ written))
    have h7 : r ≠ .x7 := fun h => hr (h ▸ (by decide : Reg.x7 ∈ written))
    have hrest : r ∉ [.x8,.x10,.x11,.x12,.x16] := by
      simp only [written,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1⟩
    exact (vg r h7 hrest).trans (ug r h6 hrest)
  have tv : v.v = s.v := vvec.trans uvec
  refine ⟨v,?_,?_,?_,?_,?_,other,vmem.trans umem,vrd.trans urd,vwr.trans uwr,vsp.trans usp⟩
  · rw [flPair,VG.Interleave.runBlock_append,ue,Option.bind_some,ve]
  · simp only [halves]
    rw [vg .x6 (by decide) (by decide),uv,vv,ug .x7 (by decide) (by decide),
      umem,ug .x5 (by decide) (by decide)]
    rfl
  · simpa only [Constants,tv] using hc
  · refine ⟨by rw [tv]; exact hm.1,?_,?_⟩
    · rw [other .x13 (by decide)]; exact hm.2.1
    · rw [other .x14 (by decide)]; exact hm.2.2
  · simpa only [Table,tv] using ht

def partialRounds (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let d := pairs E 2 3 d
  let d := (Spec.Camellia.fl d.1 (E 8),Spec.Camellia.flinv d.2 (E 9))
  let d := pairs E 10 3 d
  let d := (Spec.Camellia.fl d.1 (E 16),Spec.Camellia.flinv d.2 (E 17))
  pairs E 18 3 d

def lastRounds (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  pairs E 26 3 (Spec.Camellia.fl d.1 (E 24),Spec.Camellia.flinv d.2 (E 25))

theorem partialRounds_eq (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    partialRounds E d = VG.Proof.Camellia.groups 3 E d := by
  simp only [partialRounds,pairs,VG.Proof.Camellia.groups,VG.Proof.Camellia.group,
    List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.nil_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]

theorem lastRounds_eq (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) :
    lastRounds E (partialRounds E d) = VG.Proof.Camellia.groups 4 E d := by
  simp only [lastRounds,partialRounds,pairs,VG.Proof.Camellia.groups,VG.Proof.Camellia.group,
    List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,
    List.nil_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]

end VG.Proof.Camellia.AArch64.Serial

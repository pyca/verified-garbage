module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Save
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Sha3.AArch64.Sha3.Vector.ResidentBoundary`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt bytesAt rates)
open VG.Proof.Sha3 (Rep)

abbrev rate (b : State) : Nat := (b.gpr .x6).toNat
abbrev st (b : State) : Addr := b.gpr .x0
abbrev data (b : State) : Addr := b.gpr .x3
abbrev len (b : State) : Nat := (b.gpr .x4).toNat
abbrev scratch (b : State) : Addr := b.gpr .x1
abbrev stateR (b : State) : Region := ⟨st b, 200⟩
abbrev dataR (b : State) : Region := ⟨data b, len b⟩
abbrev scratchR (b : State) : Region := ⟨scratch b, 640⟩

/-- The call-free resident prefix starts at an aligned sponge position with
at least one complete block. `x1` and `x5` both name its scratch buffer. -/
structure BulkPre (b : State) : Prop where
  rd : b.rd = [dataR b]
  wr : b.wr = [stateR b, scratchR b]
  st_scr : (stateR b).Disjoint (scratchR b)
  d_st : (dataR b).Disjoint (stateR b)
  d_scr : (dataR b).Disjoint (scratchR b)
  rate_mem : rate b ∈ rates
  enough : rate b ≤ len b
  len_upper : len b < 2^63 + rate b
  x2 : b.gpr .x2 = 0
  x5 : b.gpr .x5 = scratch b

/-- Complete blocks have been consumed, and the usual memory sponge
representation is restored before the generic streaming tail runs. -/
structure BulkResult (b : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ len b
  aligned : consumed % rate b = 0
  abi : abiPreserved b s
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  frame : Frame [stateR b, scratchR b] b.mem s.mem
  x0 : s.gpr .x0 = b.gpr .x0
  x1 : s.gpr .x1 = b.gpr .x1
  x2 : s.gpr .x2 = b.gpr .x2
  x3 : s.gpr .x3 = data b + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (len b - consumed)
  x5 : s.gpr .x5 = b.gpr .x5
  x6 : s.gpr .x6 = b.gpr .x6
  repr : ∀ msg, stateAt b.mem (st b) = Rep (rate b) msg →
    msg.length % rate b = 0 →
    stateAt s.mem (st b) = Rep (rate b) (msg ++ bytesAt b.mem (data b) consumed)

def BulkPost (b s : State) : Prop := ∃ consumed, BulkResult b consumed s

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

end

/-! ### `Sha3.AArch64.Sha3.Vector.ResidentSetup`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Spec.Sha3 (stateAt bytesAt)

structure Setup (b s : State) : Prop where
  gpr : ∀ r ∈ [.x0,.x1,.x3,.x4,.x6], s.gpr r = b.gpr r
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  sp : s.sp = b.sp
  frame : Frame [stateR b,scratchR b] b.mem s.mem
  saved : Saved b s.mem
  lanes : Lanes s (stateAt b.mem (st b))

theorem save_gpr : ∀ r, ∀ i ∈ save, clobbers i r = false := by intro r; cases r <;> decide +kernel

theorem bulk_save (b : State) (hp : BulkPre b) :
    WP isa (.block save) b fun s =>
      (∀ r, s.gpr r = b.gpr r) ∧ s.rd = b.rd ∧ s.wr = b.wr ∧ s.sp = b.sp ∧
      Frame [stateR b,scratchR b] b.mem s.mem ∧ Saved b s.mem ∧
      stateAt s.mem (st b) = stateAt b.mem (st b) := by
  let q := b.withRegions [] [stateR b,⟨scratch b,512⟩]
  have hpq : VG.Proof.Sha3.AArch64.Pre q :=
    ⟨rfl,rfl,hp.st_scr.sub_right (Region.sub_prefix (by decide))⟩
  obtain ⟨t,s,he,hptr,hv,hf,hs⟩ := save_ok q hpq
  have hw : Covers q.wr b.wr := by
    rw [hp.wr]
    apply Covers.of_sub
    intro r hr
    change r ∈ [stateR b,⟨scratch b,512⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stateR b,by simp,0,by simp,by simp⟩
    · exact ⟨scratchR b,by simp,0,by simp,by change 512 ≤ 640; decide⟩
  have hc : Covers (q.rd ++ q.wr) (b.rd ++ b.wr) := by
    change Covers q.wr (b.rd ++ b.wr)
    intro p n hi
    obtain ⟨r,hr,hc⟩ := hw p n hi
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have he' := Exec.widen he hc hw
  simp only [q,State.withRegions_withRegions,State.withRegions_self] at he'
  have hh := Exec.regions he' (by rfl)
  refine ⟨t,s.withRegions b.rd b.wr,he',fun r => Exec.gpr (c := .block save) (r := r) (save_gpr r) he' (.inl rfl),
    rfl,rfl,hh.2.2.1,?_,hs,?_⟩
  · simpa only [hp.wr] using hh.2.2.2
  · have h := state_frame q s hpq hptr.x0 hf
    simpa only [q,State.withRegions_gpr,State.withRegions_mem,hptr.x0] using h

theorem setup_ok (b : State) (hp : BulkPre b) :
    WP isa (.block (save ++ load)) b (Setup b) := by
  rw [WP.block_append_iff]
  refine (bulk_save b hp).mono fun s ⟨hg,hr,hw,hsp,hf,hs,ha⟩ => ?_
  have hl := WP.gprs (load_ok s (fun i hi => ?_) ?_)
    (rs := [.x0,.x1,.x3,.x4,.x6])
    (by decide +kernel) rfl
  · refine hl.mono fun s' ⟨⟨hptr,hm,hA⟩,hreg⟩ => ?_
    refine ⟨fun r hr => (hreg r hr).trans (hg r),hptr.rd.trans hr,hptr.wr.trans hw,hptr.sp.trans hsp,?_,?_,?_⟩
    · rwa [hm]
    · rwa [hm]
    · rw [hg .x0,ha] at hA
      exact hA
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨stateR b,by simp,state_pair_contains b hi⟩
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨stateR b,by simp,VG.Proof.Sha3.lane_contains _ (by decide : 24 < 25)⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep)

theorem rate_bounds {b : State} (hp : BulkPre b) : 0 < rate b ∧ rate b ≤ 168 := by
  have h := hp.rate_mem
  simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> omega_using [h]

theorem input_bytes (b : State) (hp : BulkPre b) (m : Mem)
    (hf : Frame [stateR b,scratchR b] b.mem m) (c n : Nat) (hcn : c+n ≤ len b) :
    bytesAt m (data b + BitVec.ofNat 64 c) n = bytesAt b.mem (data b + BitVec.ofNat 64 c) n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc,← BitVec.ofNat_add]
  exact hf.bytes (R := dataR b) (by simpa using ⟨hp.d_st,hp.d_scr⟩)
    (Nat.le_of_lt (BitVec.isLt _)) (by change c+i < len b; omega_using [hcn, hi])

theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c+n) = bytesAt m p c ++ bytesAt m (p+BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n+1 => by
    rw [← Nat.add_assoc,VG.Proof.Sha3.bytesAt_succ,bytesAt_add m p c n,
      VG.Proof.Sha3.bytesAt_succ,List.append_assoc,BitVec.add_assoc,← BitVec.ofNat_add]

structure LoopState (b : State) (m : Mem) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ len b
  aligned : c % rate b = 0
  mem : s.mem = m
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  x3 : s.gpr .x3 = data b + BitVec.ofNat 64 c
  x4 : s.gpr .x4 = BitVec.ofNat 64 (len b-c)
  x6 : s.gpr .x6 = b.gpr .x6
  lanes : Lanes s A
  repr : ∀ msg, stateAt b.mem (st b) = Rep (rate b) msg → msg.length % rate b = 0 →
    A = Rep (rate b) (msg ++ bytesAt b.mem (data b) c)

theorem LoopState.input {b s : State} {m : Mem} {c : Nat} {A : Spec.Sha3.State}
    (hp : BulkPre b) (h : LoopState b m c A s) (hc : c+rate b ≤ len b) :
    Covers [⟨s.gpr .x3,rate b⟩] (s.rd ++ s.wr) := by
  rw [h.rd,h.wr,h.x3,hp.rd]
  apply Covers.of_sub
  intro r hr
  have he := List.mem_singleton.mp hr
  subst r
  exact ⟨dataR b,by simp,c,rfl,hc⟩

theorem body_ok (b : State) (hp : BulkPre b) (m : Mem)
    (hf : Frame [stateR b,scratchR b] b.mem m)
    (c : Nat) (A : Spec.Sha3.State) (s : State) (h : LoopState b m c A s)
    (hc : c+rate b ≤ len b) :
    WP isa body s fun s' => ∃ A', LoopState b m (c+rate b) A' s' ∧
      isa.eval (.zero .x .x7) s' = some (decide (rate b ≤ len b-(c+rate b))) := by
  unfold body
  apply WP.seq
  refine (xorRate_ok s A h.lanes (rate b) hp.rate_mem ?_ (h.input hp hc)).mono fun t ⟨hk,hl⟩ => ?_
  · rw [h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [WP.block_append_iff,WP.block_append_iff]
    refine (rounds_ok t _ hl).mono fun u ⟨hu,hA⟩ => ?_
    have h3 : u.gpr .x3 = data b + BitVec.ofNat 64 c :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x3)
    have h4 : u.gpr .x4 = BitVec.ofNat 64 (len b-c) :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x4)
    have h6 : u.gpr .x6 = BitVec.ofNat 64 (rate b) := by
      rw [hu.gpr _ (by decide),hk.gpr _ (by decide) (by decide),h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have ctl := advance_test_ok u (data b+BitVec.ofNat 64 c) (len b-c) (rate b)
      (by have hlen : len b < 2^64 := BitVec.isLt _; omega_using [hlen]) (by omega_using [hc]) (rate_bounds hp).2
      (by have := hp.len_upper; omega_using [this]) h3 h4 h6
    rw [← WP.block_append_iff]
    refine ctl.mono fun v ⟨hm,hr,hw,hsp,hv,h3',h4',h6',he⟩ => ?_
    refine ⟨Spec.Sha3.keccakF (Spec.Sha3.xorBytes A (bytesAt s.mem (s.gpr .x3) (rate b))),⟨by omega_using [hc],?_,hm.trans (hu.mem.trans (hk.mem.trans h.mem)),
      hr.trans (hu.rd.trans (hk.rd.trans h.rd)),hw.trans (hu.wr.trans (hk.wr.trans h.wr)),
      ?_,?_,?_,?_,?_⟩,?_⟩
    · rw [Nat.add_mod,h.aligned,Nat.mod_self,Nat.zero_add,Nat.zero_mod]
    · simpa only [BitVec.add_assoc,← BitVec.ofNat_add] using h3'
    · simpa only [Nat.sub_sub] using h4'
    · exact h6'.trans ((hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x6))
    · intro j hj
      change vdword (v.v (vreg j)) 0 = _
      rw [hv]
      exact hA j hj
    · intro msg hmsg halign
      rw [h.mem,h.x3,input_bytes b hp m hf c (rate b) hc,h.repr msg hmsg halign]
      have hal : (msg ++ bytesAt b.mem (data b) c).length % rate b = 0 := by
        simp only [List.length_append,VG.Proof.Sha3.bytesAt_length,Nat.add_mod,halign,
          h.aligned,Nat.zero_add,Nat.zero_mod]
      rw [← rep_whole (rate_bounds hp).1 (by have := (rate_bounds hp).2; omega_using [this])
        _ _ hal (VG.Proof.Sha3.bytesAt_length _ _ _),List.append_assoc,← bytesAt_add]
    · simpa only [Nat.sub_sub] using he

/-- The public remaining-byte count strictly decreases on each repeated body. -/
theorem loop_ok (b : State) (hp : BulkPre b) (s₀ : State) (hs : Setup b s₀) :
    WP isa (.loop body (.zero .x .x7)) s₀ fun s =>
      ∃ c A, LoopState b s₀.mem c A s := by
  let Inv : Nat → State → Prop := fun n s => ∃ c A, LoopState b s₀.mem c A s ∧
    n = len b-c ∧ c+rate b ≤ len b
  refine WP.loop (M := isa) Inv (fun n s ⟨c,A,h,hn,hc⟩ => ?_) (len b) s₀ ?_
  · refine (body_ok b hp s₀.mem hs.frame c A s h hc).mono fun s' ⟨A',h',he⟩ => ?_
    by_cases hk : rate b ≤ len b-(c+rate b)
    · right
      refine ⟨?_,len b-(c+rate b),?_,c+rate b,A',h',rfl,?_⟩
      · simpa only [hk,decide_true] using he
      · have := (rate_bounds hp).1
        omega_using [hn, hc, this]
      · omega_using [hc, hk]
    · left
      exact ⟨by simpa only [hk,decide_false] using he,c+rate b,A',h'⟩
  · refine ⟨0,stateAt b.mem (st b),⟨by omega_using [],by simp,rfl,hs.rd,hs.wr,?_,?_,?_,hs.lanes,?_⟩,
      by omega_using [],?_⟩
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hs.gpr .x3 (by simp)
    · simpa only [Nat.sub_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using hs.gpr .x4 (by simp)
    · exact hs.gpr .x6 (by simp)
    · intro msg hm _
      simpa only [bytesAt,List.range_zero,List.map_nil,List.append_nil] using hm
    · simpa only [Nat.zero_add] using hp.enough

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

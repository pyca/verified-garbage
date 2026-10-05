import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Framework.Omega

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBoundary`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt bytesAt rates)
open VG.Proof.Sha3 (Rep)

abbrev rate (b : State) : Nat := (b.gpr .x6).toNat
abbrev st (b : State) : Addr := b.gpr .x0
abbrev data (b : State) : Addr := b.gpr .x3
abbrev len (b : State) : Nat := (b.gpr .x4).toNat
abbrev scratch (b : State) : Addr := b.gpr .x1
abbrev stateR (b : State) : Region := ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b, 200⟩
abbrev dataR (b : State) : Region := ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b⟩
abbrev scratchR (b : State) : Region := ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratch b, 640⟩

/-- The call-free resident prefix starts at an aligned sponge position with
at least one complete block. `x1` and `x5` both name its scratch buffer. -/
structure BulkPre (b : State) : Prop where
  rd : b.rd = [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.dataR b]
  wr : b.wr = [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b]
  st_scr : (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b).Disjoint (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b)
  d_st : (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.dataR b).Disjoint (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b)
  d_scr : (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.dataR b).Disjoint (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b)
  rate_mem : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ∈ rates
  enough : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b
  len_upper : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b < 2^63 + VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b
  x2 : b.gpr .x2 = 0
  x5 : b.gpr .x5 = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratch b

/-- Complete blocks have been consumed, and the usual memory sponge
representation is restored before the generic streaming tail runs. -/
structure BulkResult (b : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b
  aligned : consumed % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0
  abi : abiPreserved b s
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  frame : Frame [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b] b.mem s.mem
  x0 : s.gpr .x0 = b.gpr .x0
  x1 : s.gpr .x1 = b.gpr .x1
  x2 : s.gpr .x2 = b.gpr .x2
  x3 : s.gpr .x3 = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b - consumed)
  x5 : s.gpr .x5 = b.gpr .x5
  x6 : s.gpr .x6 = b.gpr .x6
  repr : ∀ msg, stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) msg →
    msg.length % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0 →
    stateAt s.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) (msg ++ bytesAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b) consumed)

def BulkPost (b s : State) : Prop := ∃ consumed, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkResult b consumed s

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSetup`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Spec.Sha3 (stateAt bytesAt)

structure Setup (b s : State) : Prop where
  gpr : ∀ r ∈ [.x0,.x1,.x3,.x4,.x6], s.gpr r = b.gpr r
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  sp : s.sp = b.sp
  frame : Frame [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b] b.mem s.mem
  saved : Saved b s.mem
  lanes : Lanes s (stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b))

theorem save_gpr : ∀ r, ∀ i ∈ save, dstOf i ≠ some r := by intro r; cases r <;> decide +kernel

theorem bulk_save (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) :
    WP isa (.block save) b fun s =>
      (∀ r, s.gpr r = b.gpr r) ∧ s.rd = b.rd ∧ s.wr = b.wr ∧ s.sp = b.sp ∧
      Frame [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b] b.mem s.mem ∧ Saved b s.mem ∧
      stateAt s.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) := by
  let q := b.withRegions [] [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratch b,512⟩]
  have hpq : VG.Proof.Sha3.AArch64.Pre q :=
    ⟨rfl,rfl,hp.st_scr.sub_right (Region.sub_prefix (by decide))⟩
  obtain ⟨t,s,he,hptr,hv,hf,hs⟩ := save_ok q hpq
  have hw : Covers q.wr b.wr := by
    rw [hp.wr]
    apply Covers.of_sub
    intro r hr
    change r ∈ [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratch b,512⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,by simp,0,by simp,by simp⟩
    · exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b,by simp,0,by simp,by change 512 ≤ 640; decide⟩
  have hc : Covers (q.rd ++ q.wr) (b.rd ++ b.wr) := by
    change Covers q.wr (b.rd ++ b.wr)
    intro p n hi
    obtain ⟨r,hr,hc⟩ := hw p n hi
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have he' := Exec.widen he hc hw
  simp only [q,State.withRegions_withRegions,State.withRegions_self] at he'
  have hh := Exec.regions he' (by rfl)
  refine ⟨t,s.withRegions b.rd b.wr,he',fun r => Exec.gpr (c := .block save) (r := r) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.save_gpr r) he' (.inl rfl),
    rfl,rfl,hh.2.2.1,?_,hs,?_⟩
  · simpa only [hp.wr] using hh.2.2.2
  · have h := state_frame q s hpq hptr.x0 hf
    simpa only [q,State.withRegions_gpr,State.withRegions_mem,hptr.x0] using h

theorem setup_ok (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) :
    WP isa (.block (save ++ load)) b (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.Setup b) := by
  rw [WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bulk_save b hp).mono fun s ⟨hg,hr,hw,hsp,hf,hs,ha⟩ => ?_
  have hl := VG.AArch64.WP.gprs (load_ok s (fun i hi => ?_) ?_)
    (rs := [.x0,.x1,.x3,.x4,.x6])
    (by decide +kernel) rfl
  · refine hl.mono fun s' ⟨⟨hptr,hm,hA⟩,hreg⟩ => ?_
    refine ⟨fun r hr => (hreg r hr).trans (hg r),hptr.rd.trans hr,hptr.wr.trans hw,hptr.sp.trans hsp,?_,?_,?_⟩
    · rwa [hm]
    · rwa [hm]
    · rw [hg .x0,ha] at hA
      exact hA
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,by simp,state_pair_contains b hi⟩
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,by simp,VG.Proof.Sha3.lane_contains _ (by decide : 24 < 25)⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentSelect`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

structure RateKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x17 → r ≠ .x7 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem RateKeep.trans {s t u : State} (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s t) (k : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep t u) : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s u :=
  ⟨fun r h₁ h₂ => (k.gpr r h₁ h₂).trans (h.gpr r h₁ h₂),k.mem.trans h.mem,
    k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem BlockKeep.rate {s t : State} (h : BlockKeep s t) : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s t :=
  ⟨fun r hr _ => h.gpr r hr,h.mem,h.rd,h.wr,h.sp⟩
theorem RateKeep.write7 (s : State) (v : BitVec 64) : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s (s.write .x .x7 v) := by
  refine ⟨fun r _ hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [RegUpd.gpr_write,hr,ite_false]

def select (rs : List Nat) : Prog isa :=
  rs.foldr (fun r rest => .seq (.block [.subImm .x .x7 .x6 r])
    (.ite (.zero .x .x7) (.block (absorbBlock r)) rest)) (.block (absorbBlock 168))

theorem select_ok (rs : List Nat) (hsmall : ∀ r ∈ rs, r < 4096)
    (s : State) (A : Spec.Sha3.State) (hA : Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hrs : r ∈ rs ++ [168])
    (hv : s.gpr .x6 = BitVec.ofNat 64 r)
    (hin : Covers [⟨s.gpr .x3,r⟩] (s.rd ++ s.wr)) :
    WP isa (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.select rs) s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s s' ∧
      Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) r)) := by
  induction rs generalizing s with
  | nil =>
    have he : r = 168 := by simpa only [List.nil_append,List.mem_singleton] using hrs
    subst r
    exact (absorbBlock_ok s A hA 168 hr hin).mono fun _ h => ⟨BlockKeep.rate h.1,h.2⟩
  | cons x xs ih =>
    change WP isa (.seq (.block [.subImm .x .x7 .x6 x]) (.ite (.zero .x .x7) _ _)) s _
    apply WP.seq
    refine WP.cons (exec_subImm_x (hsmall x (by simp))) (wp_nil ?_)
    let t := s.write .x .x7 (s.read .x .x6 - BitVec.ofNat 64 x)
    have hvt : t.gpr .x6 = BitVec.ofNat 64 r := by
      simpa only [t,RegUpd.gpr_write,reduceCtorEq,ite_false] using hv
    have htA : Lanes t A := hA
    have htin : Covers [⟨t.gpr .x3,r⟩] (t.rd ++ t.wr) := hin
    have hk : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s t := RateKeep.write7 _ _
    by_cases he : r = x
    · subst x
      refine WP.ite true ?_ (fun _ => ?_) (fun h => by contradiction)
      · simp only [VG.Proof.Sha3.AArch64.eval_zero, RegUpd.gpr_write_self, State.read, Size.bits,
          BitVec.setWidth_eq,hv,BitVec.sub_self]
        rfl
      · exact (absorbBlock_ok t A htA r hr htin).mono fun _ h => ⟨hk.trans (BlockKeep.rate h.1),h.2⟩
    · refine WP.ite false ?_ (fun h => by contradiction) (fun _ => ?_)
      · have hn : BitVec.ofNat 64 r - BitVec.ofNat 64 x ≠ 0 := by
          intro h
          have h' := BitVec.sub_eq_iff_eq_add.mp h
          have h : BitVec.ofNat 64 r = BitVec.ofNat 64 x := h'.trans (BitVec.zero_add _)
          have hrb : r < 4096 := by
            simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at hr
            rcases hr with rfl|rfl|rfl|rfl|rfl <;> omega
          have hx := hsmall x (by simp)
          have hh := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r < 2^64),
            Nat.mod_eq_of_lt (by omega : x < 2^64)] at hh
          exact he hh
        simpa only [VG.Proof.Sha3.AArch64.eval_zero,t,RegUpd.gpr_write_self,State.read,Size.bits,
          BitVec.setWidth_eq,hv,beq_eq_false_iff_ne] using congrArg some (beq_eq_false_iff_ne.mpr hn)
      · have hrs' : r ∈ xs ++ [168] := by simpa only [List.cons_append,List.mem_cons,he,false_or] using hrs
        exact (ih (fun y hy => hsmall y (by simp [hy])) t htA hrs' hvt htin).mono
          fun _ h => ⟨hk.trans h.1,h.2⟩

theorem xorRate_ok (s : State) (A : Spec.Sha3.State) (hA : Lanes s A)
    (r : Nat) (hr : r ∈ Spec.Sha3.rates) (hv : s.gpr .x6 = BitVec.ofNat 64 r)
    (hin : Covers [⟨s.gpr .x3,r⟩] (s.rd ++ s.wr)) :
    WP isa xorRate s fun s' => VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.RateKeep s s' ∧
      Lanes s' (Spec.Sha3.xorBytes A (Spec.Sha3.bytesAt s.mem (s.gpr .x3) r)) :=
  VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.select_ok [72,104,136,144] (by decide) s A hA r hr (by change r ∈ Spec.Sha3.rates; exact hr) hv hin

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.Spec.Sha3 VG.Proof.Sha3

/-- The subtract-and-sign-bit guard admits only complete blocks. Its upper
bound lets the same inexpensive guard terminate the resident loop. -/
theorem enough_iff (n rate : Nat) (hn : n < 2^64) (hr : rate ≤ 168) :
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 rate) >>> 63 = 0) ↔
      rate ≤ n ∧ n < 2^63 + rate := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat,
    show BitVec.toNat (0 : BitVec 64) = 0 from rfl,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : rate < 2^64)]
  omega

/-- A whole rate block is XORed into lanes before the next permutation. -/
theorem xorAt_zero (A : Spec.Sha3.State) (bs : List Byte) :
    xorAt A 0 bs = xorBytes A bs := by
  apply ext_bytes
  intro j hj
  rw [byteOf_xorAt A 0 bs hj, byteOf_xorBytes A bs hj]
  simp only [Nat.zero_le,Nat.zero_add,true_and,Nat.sub_zero]
  by_cases h : j < bs.length
  · simp [h,List.getD]
  · simp [h,List.getD]

/-- An aligned sponge can absorb a complete block entirely in registers. -/
theorem rep_whole {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200)
    (msg bs : List Byte) (ha : msg.length % rate = 0) (hb : bs.length = rate) :
    Rep rate (msg ++ bs) = keccakF (xorBytes (Rep rate msg) bs) := by
  rw [rep_append hr hr' msg bs (by omega) (by omega),ha,hb]
  simp only [Nat.zero_add,ite_true,VG.Proof.Sha3.AArch64.Sha3.Vector.xorAt_zero]

/-- Consuming a complete rate block retains the aligned position. -/
theorem append_whole_aligned {rate : Nat} (msg bs : List Byte)
    (ha : msg.length % rate = 0) (hb : bs.length = rate) :
    (msg ++ bs).length % rate = 0 := by
  simp only [List.length_append,hb,Nat.add_mod,Nat.mod_self,Nat.add_zero,ha,Nat.zero_mod]

end VG.Proof.Sha3.AArch64.Sha3.Vector

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentControl`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

theorem advance_test_ok (s : State) (p : Addr) (n r : Nat)
    (_hn : n < 2^64) (hr : r ≤ n) (hrb : r ≤ 168) (hu : n < 2^63+r)
    (h3 : s.gpr .x3 = p) (h4 : s.gpr .x4 = BitVec.ofNat 64 n)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 r) :
    WP isa (.block (advance ++ test)) s fun s' =>
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.v = s.v ∧
      s'.gpr .x3 = p + BitVec.ofNat 64 r ∧
      s'.gpr .x4 = BitVec.ofNat 64 (n-r) ∧ s'.gpr .x6 = s.gpr .x6 ∧
      isa.eval (.zero .x .x7) s' = some (decide (r ≤ n-r)) := by
  unfold advance test
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons (exec_lsr_x (by decide)) (wp_nil ?_))))
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 r = BitVec.ofNat 64 (n-r) :=
    VG.Proof.Sha3.sub_ofNat hr
  simp only [reduceCtorEq, ↓reduceIte,
    RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write,RegUpd.v_write,
    RegUpd.gpr_write,State.read,Size.bits,BitVec.setWidth_eq,h3,h4,h6,hsub,
    true_and]
  simp only [VG.Proof.Sha3.AArch64.eval_zero,RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,decide_eq_true_eq,VG.Proof.Sha3.AArch64.Sha3.Vector.enough_iff (n-r) r (by omega) hrb]
  exact and_iff_left (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep)

theorem rate_bounds {b : State} (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) : 0 < VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ∧ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ 168 := by
  have h := hp.rate_mem
  simp only [Spec.Sha3.rates,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> omega

theorem input_bytes (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) (m : Mem)
    (hf : Frame [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b] b.mem m) (c n : Nat) (hcn : c+n ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b) :
    bytesAt m (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 c) n = bytesAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 c) n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc,← BitVec.ofNat_add]
  exact hf.bytes (R := VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.dataR b) (by simpa using ⟨hp.d_st,hp.d_scr⟩)
    (Nat.le_of_lt (BitVec.isLt _)) (by change c+i < VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b; omega)

theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c+n) = bytesAt m p c ++ bytesAt m (p+BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n+1 => by
    rw [← Nat.add_assoc,VG.Proof.Sha3.bytesAt_succ,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bytesAt_add m p c n,
      VG.Proof.Sha3.bytesAt_succ,List.append_assoc,BitVec.add_assoc,← BitVec.ofNat_add]

structure LoopState (b : State) (m : Mem) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b
  aligned : c % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0
  mem : s.mem = m
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  x3 : s.gpr .x3 = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 c
  x4 : s.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-c)
  x6 : s.gpr .x6 = b.gpr .x6
  lanes : Lanes s A
  repr : ∀ msg, stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) msg → msg.length % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0 →
    A = Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) (msg ++ bytesAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b) c)

theorem LoopState.input {b s : State} {m : Mem} {c : Nat} {A : Spec.Sha3.State}
    (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b m c A s) (hc : c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b) :
    Covers [⟨s.gpr .x3,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b⟩] (s.rd ++ s.wr) := by
  rw [h.rd,h.wr,h.x3,hp.rd]
  apply Covers.of_sub
  intro r hr
  have he := List.mem_singleton.mp hr
  subst r
  exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.dataR b,by simp,c,rfl,hc⟩

theorem body_ok (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) (m : Mem)
    (hf : Frame [VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b] b.mem m)
    (c : Nat) (A : Spec.Sha3.State) (s : State) (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b m c A s)
    (hc : c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b) :
    WP isa body s fun s' => ∃ A', VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b m (c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) A' s' ∧
      isa.eval (.zero .x .x7) s' = some (decide (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-(c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b))) := by
  unfold body
  apply WP.seq
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.xorRate_ok s A h.lanes (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) hp.rate_mem ?_ (h.input hp hc)).mono fun t ⟨hk,hl⟩ => ?_
  · rw [h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · rw [WP.block_append_iff,WP.block_append_iff]
    refine (rounds_ok t _ hl).mono fun u ⟨hu,hA⟩ => ?_
    have h3 : u.gpr .x3 = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 c :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x3)
    have h4 : u.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-c) :=
      (hu.gpr _ (by decide)).trans ((hk.gpr _ (by decide) (by decide)).trans h.x4)
    have h6 : u.gpr .x6 = BitVec.ofNat 64 (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) := by
      rw [hu.gpr _ (by decide),hk.gpr _ (by decide) (by decide),h.x6,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have ctl := VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.advance_test_ok u (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b+BitVec.ofNat 64 c) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-c) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b)
      (by have hlen : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b < 2^64 := BitVec.isLt _; omega) (by omega) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate_bounds hp).2
      (by have := hp.len_upper; omega) h3 h4 h6
    rw [← WP.block_append_iff]
    refine ctl.mono fun v ⟨hm,hr,hw,hsp,hv,h3',h4',h6',he⟩ => ?_
    refine ⟨Spec.Sha3.keccakF (Spec.Sha3.xorBytes A (bytesAt s.mem (s.gpr .x3) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b))),⟨by omega,?_,hm.trans (hu.mem.trans (hk.mem.trans h.mem)),
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
      rw [h.mem,h.x3,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.input_bytes b hp m hf c (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) hc,h.repr msg hmsg halign]
      have hal : (msg ++ bytesAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b) c).length % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0 := by
        simp only [List.length_append,VG.Proof.Sha3.bytesAt_length,Nat.add_mod,halign,
          h.aligned,Nat.zero_add,Nat.zero_mod]
      rw [← VG.Proof.Sha3.AArch64.Sha3.Vector.rep_whole (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate_bounds hp).1 (by have := (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate_bounds hp).2; omega)
        _ _ hal (VG.Proof.Sha3.bytesAt_length _ _ _),List.append_assoc,← VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bytesAt_add]
    · simpa only [Nat.sub_sub] using he

/-- The public remaining-byte count strictly decreases on each repeated body. -/
theorem loop_ok (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) (s₀ : State) (hs : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.Setup b s₀) :
    WP isa (.loop body (.zero .x .x7)) s₀ fun s =>
      ∃ c A, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b s₀.mem c A s := by
  let Inv : Nat → State → Prop := fun n s => ∃ c A, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b s₀.mem c A s ∧
    n = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-c ∧ c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b
  refine WP.loop (M := isa) Inv (fun n s ⟨c,A,h,hn,hc⟩ => ?_) (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b) s₀ ?_
  · refine (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.body_ok b hp s₀.mem hs.frame c A s h hc).mono fun s' ⟨A',h',he⟩ => ?_
    by_cases hk : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-(c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b)
    · right
      refine ⟨?_,VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-(c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b),?_,c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b,A',h',rfl,?_⟩
      · simpa only [hk,decide_true] using he
      · have := (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate_bounds hp).1
        omega
      · omega
    · left
      exact ⟨by simpa only [hk,decide_false] using he,c+VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b,A',h'⟩
  · refine ⟨0,stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b),⟨by omega,by simp,rfl,hs.rd,hs.wr,?_,?_,?_,hs.lanes,?_⟩,
      by omega,?_⟩
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hs.gpr .x3 (by simp)
    · simpa only [Nat.sub_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq] using hs.gpr .x4 (by simp)
    · exact hs.gpr .x6 (by simp)
    · intro msg hm _
      simpa only [bytesAt,List.range_zero,List.map_nil,List.append_nil] using hm
    · simpa only [Nat.zero_add] using hp.enough

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit`. -/
section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
materialize_code bulk
materialize_code body
end VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBulk`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
open VG.Spec.Sha3 (stateAt)

structure FinishedAt (b : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b
  aligned : consumed % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0
  x3 : s.gpr .x3 = VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.len b-consumed)
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (b.v r).extractLsb' 0 64
  repr : ∀ msg, stateAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = VG.Proof.Sha3.Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) msg → msg.length % VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b = 0 →
    stateAt s.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.st b) = VG.Proof.Sha3.Rep (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.rate b) (msg ++ Spec.Sha3.bytesAt b.mem (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.data b) consumed)

def Finished (b s : State) : Prop := ∃ c, VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.FinishedAt b c s

theorem finish_ok (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) (s₀ : State) (hs : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.Setup b s₀)
    (c : Nat) (A : Spec.Sha3.State) (s : State) (h : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.LoopState b s₀.mem c A s)
    (h0 : s.gpr .x0 = b.gpr .x0) (h1 : s.gpr .x1 = b.gpr .x1) :
    WP isa (.block (store ++ restore)) s (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.Finished b) := by
  rw [WP.block_append_iff]
  have hout : ∀ i < 12, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16 := by
    intro i hi
    rw [h.wr,hp.wr,h0]
    exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,by simp,state_pair_contains b hi⟩
  have hlast : InRegions s.wr (VG.Proof.Sha3.laneAddr (s.gpr .x0) 24) 8 := by
    rw [h.wr,hp.wr,h0]
    exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.stateR b,by simp,VG.Proof.Sha3.lane_contains _ (by decide : 24<25)⟩
  refine (VG.AArch64.WP.gprs (store_ok s A h.lanes hout hlast) (rs := [.x3,.x4])
    (by decide +kernel) rfl).mono fun t ⟨⟨hp',hf,ha⟩,hg⟩ => ?_
  have saved : Saved b t.mem := by
    intro i hi
    rw [hf.read (scratch_contains b hi) ?_ (by decide),h.mem]
    · exact hs.saved i hi
    · intro r hr
      have he := List.mem_singleton.mp hr
      subst r
      rw [h0]
      exact (hp.st_scr.sub_right (Region.sub_prefix (by decide))).symm
  refine (restore_ok b t saved (hp'.x1.trans h1) (fun i hi => ?_)).mono fun u ⟨hk,hv⟩ => ?_
  · rw [hp'.rd,hp'.wr,h.rd,h.wr,hp.rd,hp.wr,hp'.x1,h1]
    exact ⟨VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.scratchR b,by simp,Offset.contains_base _ (by change 16*i+16 ≤ 640; omega) (by omega)⟩
  · refine ⟨c,⟨h.c_le,h.aligned,?_,?_,hv,?_⟩⟩
    · exact (congrFun hk.gpr .x3).trans ((hg .x3 (by simp)).trans h.x3)
    · exact (congrFun hk.gpr .x4).trans ((hg .x4 (by simp)).trans h.x4)
    · intro msg hm hal
      rw [hk.mem]
      rw [h0] at ha
      exact ha.trans (h.repr msg hm hal)

theorem functional (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) : WP isa bulk b (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.Finished b) := by
  unfold bulk
  apply WP.seq
  refine (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.setup_ok b hp).mono fun s₀ hs => ?_
  apply WP.seq
  have loop := VG.AArch64.WP.gprs (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.loop_ok b hp s₀ hs) (rs := [.x0,.x1]) ?_ rfl
  · exact loop.mono fun s ⟨⟨c,A,h⟩,hg⟩ => VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.finish_ok b hp s₀ hs c A s h
      ((hg .x0 (by simp)).trans (hs.gpr .x0 (by simp)))
      ((hg .x1 (by simp)).trans (hs.gpr .x1 (by simp)))
  · change body.allInstrs (fun i => [.x0,.x1].all fun r => dstOf i != some r) = true
    lit_decide

theorem bulk_correct (b : State) (hp : VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPre b) : WP isa bulk b (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.BulkPost b) := by
  have hc : bulk.allInstrs (fun i => (VG.AArch64.preserved ++ [Reg.x0,Reg.x1,Reg.x2,Reg.x5,Reg.x6]).all
      fun r => dstOf i != some r) = true := by lit_decide
  obtain ⟨t,s,he,⟨c,hf⟩,hg⟩ := VG.AArch64.WP.gprs (VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.functional b hp) hc (by lit_decide)
  have hh := Exec.regions he (by lit_decide)
  refine ⟨t,s,he,c,⟨hf.c_le,hf.aligned,⟨fun r hr => hg r (by simp [hr]),hh.2.2.1,hf.vcs⟩,
    hh.1,hh.2.1,?_,hg .x0 (by simp),hg .x1 (by simp),hg .x2 (by simp),hf.x3,hf.x4,
    hg .x5 (by simp),hg .x6 (by simp),hf.repr⟩⟩
  simpa only [hp.wr] using hh.2.2.2

#assert_standard_axioms VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bulk_correct

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident`. -/
section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The general absorber can run with wider ambient memory regions, including
its existing stack frame. Narrowing changes permissions only, not registers,
SIMD state, memory, or the trace. -/
theorem generic_widen (v : Proof.Sha3.AArch64.Permutation) (s : State)
    (rd wr : List Region)
    (hp : Proof.Sha3.absorbAArch64.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun s' =>
      abiPreserved s s' ∧ Proof.Sha3.absorbAArch64.post
        (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, q, he, ha, hq⟩ :=
    Stream.Absorb.correct v (Stream.Absorb.pre_of hp).1 (Stream.Absorb.pre_of hp).2
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) hc hw
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  obtain ⟨hr, hw', _⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hw'
  have eq : (q.withRegions s.rd s.wr).withRegions rd wr = q := by
    rw [State.withRegions_withRegions, ← hr, ← hw']
    rfl
  exact ⟨t, q.withRegions s.rd s.wr, he', ha, by rw [eq]; exact hq⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.Sha3 (Rep)
open VG.Proof.Sha3.AArch64.Stream.Absorb

/-- An aligned prefix has advanced the input arguments while retaining the
original sponge's meaning, permissions, and preserved registers. -/
structure Tail (a : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ Stream.Absorb.len a
  aligned : consumed % rt a = 0
  abi : abiPreserved a s
  rd : s.rd = a.rd
  wr : s.wr = a.wr
  frame : Frame [stR a, scR a] a.mem s.mem
  x0 : s.gpr .x0 = a.gpr .x0
  x1 : s.gpr .x1 = a.gpr .x1
  x2 : s.gpr .x2 = a.gpr .x2
  x3 : s.gpr .x3 = dp a + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (Stream.Absorb.len a - consumed)
  x5 : s.gpr .x5 = a.gpr .x5
  repr : ∀ msg, Msg a msg →
    stateAt s.mem (Stream.Absorb.st a) = Rep (rt a) (msg ++ Stream.Absorb.D a consumed)

/-- The ordinary streaming implementation finishes a resident prefix without
losing the original message contract or imposing syntactic SIMD restrictions. -/
theorem finish (v : Proof.Sha3.AArch64.Permutation) {a s : State} {c : Nat}
    (hp : Stream.Absorb.Pre a) (hs : Stack a) (hz : a.gpr .x2 = 0) (h : Tail a c s) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun s' =>
      abiPreserved a s' ∧ Proof.Sha3.absorbAArch64.post a s' := by
  have hpos : (a.gpr .x2).toNat = 0 := congrArg BitVec.toNat hz
  let tail : Region := ⟨dp a + BitVec.ofNat 64 c, Stream.Absorb.len a - c⟩
  have hsub : Region.Sub tail (dR a) := Offset.sub_base _ (by omega_using [h.c_le])
  have hlen : (s.gpr .x4).toNat = Stream.Absorb.len a - c := by
    rw [h.x4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (len_lt a)
  have pre : Proof.Sha3.absorbAArch64.pre (s.withRegions [tail] s.wr) := by
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, h.x0, h.x1, h.x2, h.x3, hlen,
      h.x5, h.wr, hp.wr, h.abi.2.1]
    exact ⟨rfl, trivial, hp.st_scr, hp.d_st.sub_left hsub, hp.d_scr.sub_left hsub,
      hs.sp16, hs.st, hs.d.sub_right hsub, hs.scr, hp.rate, hp.pos_lt⟩
  have hcov : Covers [tail] s.rd := by
    rw [h.rd, hp.rd]
    apply Covers.of_sub
    intro r hr
    have er : r = tail := List.mem_singleton.mp hr
    subst r
    exact ⟨dR a, by simp, c, rfl, by exact Nat.le_of_eq (Nat.add_sub_of_le h.c_le)⟩
  refine WP.mono (generic_widen v s [tail] s.wr pre
    (Covers.append hcov (fun _ _ hx => hx)) (fun _ _ hx => hx)) ?_
  intro q ⟨ha, hq⟩
  refine ⟨⟨fun r hr => (ha.1 r hr).trans (h.abi.1 r hr),
    ha.2.1.trans h.abi.2.1, fun r hr => (ha.2.2 r hr).trans (h.abi.2.2 r hr)⟩, ?_⟩
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr,
    State.withRegions_mem, h.x0, h.x1, h.x2, h.x3, hlen] at hq
  constructor
  · intro msg hm hmpos
    have hm' : Msg a msg := ⟨hm, hmpos⟩
    have haligned : (msg ++ Stream.Absorb.D a c).length % rt a = 0 := by
      change (msg ++ bytesAt a.mem (dp a) c).length % rt a = 0
      rw [List.length_append, VG.Proof.Sha3.bytesAt_length, Nat.add_mod,
        ← hmpos, hpos, h.aligned]
      rfl
    have hd : bytesAt s.mem (dp a + BitVec.ofNat 64 c) (Stream.Absorb.len a - c) =
        bytesAt a.mem (dp a + BitVec.ofNat 64 c) (Stream.Absorb.len a - c) := by
      apply VG.Proof.Sha3.AArch64.bytesAt_congr
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact h.frame.bytes (R := dR a) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt (len_lt a)) (by change c + i < Stream.Absorb.len a; omega_using [h.c_le, hi])
    have out := hq.1 (msg ++ Stream.Absorb.D a c) (h.repr msg hm') (by
      exact hpos.trans haligned.symm)
    rw [hd, List.append_assoc, ← VG.Proof.Sha3.AArch64.Sha3.Vector.Resident.bytesAt_add, Nat.add_sub_of_le h.c_le] at out
    exact out
  · have heq : (Stream.Absorb.len a - c) % rt a = Stream.Absorb.len a % rt a := by
      have eq := Nat.add_mod c (Stream.Absorb.len a - c) (rt a)
      rw [Nat.add_sub_of_le h.c_le, h.aligned, Nat.zero_add, Nat.mod_mod] at eq
      exact eq.symm
    change (q.gpr .x0).toNat = ((a.gpr .x2).toNat + Stream.Absorb.len a) % rt a
    rw [hpos, Nat.zero_add]
    simpa only [hpos, Nat.zero_add, heq] using hq.2

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64

structure Entry (a s : State) : Prop where
  args : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5], s.gpr r = a.gpr r
  abi : abiPreserved a s
  mem : s.mem = a.mem
  rd : s.rd = a.rd
  wr : s.wr = a.wr

theorem Entry.refl (a : State) : Entry a a :=
  ⟨fun _ _ => rfl, ⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩,rfl,rfl,rfl⟩

theorem Entry.upd {a s q : State} (h : Entry a s) {r : Reg} {v : BitVec 64}
    (u : Upd s q r v) (hr : r = .x6 ∨ r = .x7) : Entry a q := by
  have args : ∀ k ∈ [Reg.x0,.x1,.x2,.x3,.x4,.x5], k ≠ r := by
    rcases hr with rfl | rfl <;> decide +kernel
  have kept : ∀ k ∈ preserved, k ≠ r := by
    rcases hr with rfl | rfl <;> decide +kernel
  exact ⟨fun k hk => (u.other k (args k hk)).trans (h.args k hk),
    ⟨fun k hk => (u.other k (kept k hk)).trans (h.abi.1 k hk),
      u.sp.trans h.abi.2.1,fun k hk => by rw [u.vec]; exact h.abi.2.2 k hk⟩,
    u.mem.trans h.mem,u.rd.trans h.rd,u.wr.trans h.wr⟩

theorem Entry.pre {a s : State} (h : Entry a s) (hp : Proof.Sha3.absorbAArch64.pre a) :
    Proof.Sha3.absorbAArch64.pre s := by
  simp only [Proof.Sha3.absorbAArch64,h.args .x0 (by decide),h.args .x1 (by decide),h.args .x2 (by decide),h.args .x3 (by decide),h.args .x4 (by decide),h.args .x5 (by decide),h.rd,h.wr,h.abi.2.1]
  exact hp

theorem Entry.post {a s q : State} (h : Entry a s)
    (hp : Proof.Sha3.absorbAArch64.post s q) : Proof.Sha3.absorbAArch64.post a q := by
  simpa only [Proof.Sha3.absorbAArch64,h.args .x0 (by decide),h.args .x1 (by decide),h.args .x2 (by decide),h.args .x3 (by decide),h.args .x4 (by decide),h.args .x5 (by decide),h.mem] using hp

theorem generic_entry (v : Permutation) {a s : State} (hp : Proof.Sha3.absorbAArch64.pre a)
    (h : Entry a s) :
    WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) s fun q =>
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  refine WP.mono (Stream.Absorb.correct v (Stream.Absorb.pre_of (h.pre hp)).1
    (Stream.Absorb.pre_of (h.pre hp)).2) ?_
  intro q ⟨ha,hq⟩
  exact ⟨⟨fun r hr => (ha.1 r hr).trans (h.abi.1 r hr),
    ha.2.1.trans h.abi.2.1,fun r hr => (ha.2.2 r hr).trans (h.abi.2.2 r hr)⟩,h.post hq⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64
open VG.Proof.Sha3.AArch64.Stream.Absorb

private theorem upd_abi {a s : State} {r : Reg} {x : BitVec 64} (h : Upd a s r x)
    (hr : r ∉ preserved) : abiPreserved a s :=
  ⟨fun k hk => h.other k (fun e => hr (e ▸ hk)),h.sp,fun _ _ => by rw [h.vec]⟩

private theorem abi_trans {a b c : State} (h : abiPreserved a b) (k : abiPreserved b c) :
    abiPreserved a c :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr),k.2.1.trans h.2.1,
    fun r hr => (k.2.2 r hr).trans (h.2.2 r hr)⟩

private theorem bulk_tail (v : Permutation) (whole : Prog isa)
    (hb : ∀ b, BulkPre b → WP isa whole b (BulkPost b))
    {a b : State} (hp : Proof.Sha3.absorbAArch64.pre a) (he : Entry a b)
    (hz : a.gpr .x2 = 0) (h6 : b.gpr .x6 = a.gpr .x1)
    (hen : rt a ≤ Stream.Absorb.len a) (hlt : Stream.Absorb.len a < 2^63 + rt a) :
    WP isa (.seq (.block [Impl.Sha3.AArch64.mov .x1 .x5])
      (.seq whole
        (.block [Impl.Sha3.AArch64.mov .x1 .x6]))) b fun r =>
      WP isa (Impl.Sha3.AArch64.Stream.absorbGenericWith v.callee) r fun q =>
        abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  obtain ⟨pa,sa⟩ := Stream.Absorb.pre_of hp
  refine WP.seq (wp_mov fun b' u => wp_nil ?_)
  have e0 : b'.gpr .x0 = a.gpr .x0 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e1 : b'.gpr .x1 = a.gpr .x5 := u.gpr.trans (he.args _ (by decide))
  have e2 : b'.gpr .x2 = a.gpr .x2 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e3 : b'.gpr .x3 = a.gpr .x3 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e4 : b'.gpr .x4 = a.gpr .x4 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e5 : b'.gpr .x5 = a.gpr .x5 := (u.other _ (by decide)).trans (he.args _ (by decide))
  have e6 : b'.gpr .x6 = a.gpr .x1 := (u.other _ (by decide)).trans h6
  have em : b'.mem = a.mem := u.mem.trans he.mem
  have er : b'.rd = a.rd := u.rd.trans he.rd
  have ew : b'.wr = a.wr := u.wr.trans he.wr
  have ba : abiPreserved a b' := abi_trans he.abi (upd_abi u (by decide))
  have bp : BulkPre b' := by
    constructor <;> simp only [dataR,data,len,stateR,st,scratchR,scratch,rate,
      e0,e1,e2,e3,e4,e5,e6,er,ew]
    · exact pa.rd
    · exact pa.wr
    · exact pa.st_scr
    · exact pa.d_st
    · exact pa.d_scr
    · exact pa.rate
    · exact hen
    · exact hlt
    · exact hz
  refine WP.seq (WP.mono (hb b' bp) fun q ⟨c,h⟩ => ?_)
  refine wp_mov fun r ur => wp_nil ?_
  apply finish v (c := c) pa sa hz
  refine ⟨?_,?_,abi_trans (abi_trans ba h.abi) (upd_abi ur (by decide)),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [len,e4] using h.c_le
  · simpa only [rate,e6] using h.aligned
  · exact ur.rd.trans (h.rd.trans er)
  · exact ur.wr.trans (h.wr.trans ew)
  · simpa only [ur.mem,stateR,st,scratchR,scratch,e0,e1,em] using h.frame
  · exact (ur.other _ (by decide)).trans (h.x0.trans e0)
  · exact ur.gpr.trans (h.x6.trans e6)
  · exact (ur.other _ (by decide)).trans (h.x2.trans e2)
  · simp only [ur.other .x3 (by decide),h.x3,data,e3]
  · simp only [ur.other .x4 (by decide),h.x4,len,e4]
  · exact (ur.other _ (by decide)).trans (h.x5.trans e5)
  · intro msg ⟨hm,hpos⟩
    have hzero : msg.length % rt a = 0 := hpos.symm.trans (congrArg BitVec.toNat hz)
    simpa only [ur.mem,st,rate,data,e0,e3,e6,em] using
      h.repr msg (by simpa only [st,rate,e0,e6,em] using hm)
        (by simpa only [rate,e6] using hzero)

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Proof.Sha3.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

/-- The public guards select either the proved resident prefix or the ordinary
streaming tail. Every branch retains the same scalar-compatible contract. -/
theorem correct (v : Permutation) (whole : Prog isa)
    (hb : ∀ b, BulkPre b → WP isa whole b (BulkPost b))
    (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    WP isa (absorbWith whole v.callee) a fun q =>
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q := by
  unfold absorbWith bulkPrefixWith
  refine WP.seq (WP.ite (a.gpr .x2 == 0) (VG.Proof.Sha3.AArch64.eval_zero _ _) (fun hz => ?_) (fun _ => ?_))
  · have hz' : a.gpr .x2 = 0 := eq_of_beq hz
    unfold test
    refine WP.seq (wp_mov fun a1 u1 => wp_sub fun a2 u2 =>
      wp_lsr (by decide) fun a3 u3 => wp_nil ?_)
    have he : Entry a a3 := ((Entry.refl a).upd u1 (.inl rfl)).upd u2 (.inr rfl) |>.upd u3 (.inr rfl)
    have h6 : a3.gpr .x6 = a.gpr .x1 := by
      rw [u3.other _ (by decide),u2.other _ (by decide),u1.gpr]
    have h7 : a3.gpr .x7 = (a.gpr .x4 - a.gpr .x1) >>> 63 := by
      rw [u3.gpr,u2.gpr,u1.other _ (by decide),u1.gpr]
    refine WP.ite (a3.gpr .x7 == 0) (VG.Proof.Sha3.AArch64.eval_zero _ _) (fun hen => ?_) (fun _ => ?_)
    · have heq : (a.gpr .x4 - a.gpr .x1) >>> 63 = 0 := h7.symm.trans (eq_of_beq hen)
      have hr := (Stream.Absorb.pre_of hp).1.rt_pos
      have hn := (enough_iff (a.gpr .x4).toNat (a.gpr .x1).toNat
        (a.gpr .x4).isLt hr.2).mp (by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using heq)
      exact bulk_tail v whole hb hp he hz' h6 hn.1 hn.2
    · exact wp_nil (generic_entry v hp he)
  · exact wp_nil (generic_entry v hp (Entry.refl a))

theorem absorb_correct (v : Permutation) (whole : Prog isa)
    (hb : ∀ b, BulkPre b → WP isa whole b (BulkPost b))
    (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (absorbWith whole v.callee) a t q ∧ abiPreserved a q ∧
      Proof.Sha3.absorbAArch64.post a q := by
  obtain ⟨t,q,he,hq⟩ := correct v whole hb a hp
  exact ⟨t,q,he,hq⟩

theorem bulk_depth : bulk.aarch64Depth = 0 := by rfl

theorem absorb_depth (v : Permutation) (whole : Prog isa) (hw : whole.aarch64Depth = 0) :
    (absorbWith whole v.callee).aarch64Depth = 1 := by
  simp only [absorbWith, bulkPrefixWith, Impl.Sha3.AArch64.Stream.absorbGenericWith, Code.aarch64Depth,
    hw, v.absorbMain_depth, Instr.frameUnits]
  rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The selected hardware absorber branches only on public arguments. -/
theorem absorb_taint : ∃ h, (taint.check (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absorb_ct : ConstantTime isa Proof.Sha3.absorbAArch64.pre Proof.Sha3.absorbAArch64.pub
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) := by
  obtain ⟨h,hh⟩ := absorb_taint
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    (fun _ _ _ _ hp => Stream.Absorb.agree₀ hp) hh

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64

/-- The selected hardware absorber, with the actual resident-loop theorem
supplied to the generic outer composition proof. -/
theorem hardware_absorb_correct (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee) a t q ∧
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q :=
  absorb_correct Sha3.backend _ bulk_correct a hp

theorem hardware_absorb_depth :
    (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorb Sha3.callee).aarch64Depth = 1 :=
  absorb_depth Sha3.backend _ bulk_depth

#assert_standard_axioms hardware_absorb_correct

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident

end

import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Xor
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Advance
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop

/-!
# The scalar resident absorber: the loop over whole blocks

Each iteration XORs a block into the lanes, runs the unrolled rounds of the
permutation (`unrolled_rounds_ok`) and advances; the lanes then represent
the message followed by one more block (`rep_whole`).
-/

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre rate st data len dataR bytesAt_add)
open VG.Spec.Sha3 (stateAt bytesAt)

/-- The loop's invariant, after `c` bytes of data: the lanes are `A`, which
the message followed by those bytes represents, and v19–v21 hold the data
pointer, the length left and the rate. -/
structure Loop (b : State) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ len b
  aligned : c % rate b = 0
  core : CoreState b A s
  mem : s.mem = b.mem
  dp : vdword (s.v .v19) 0 = data b + BitVec.ofNat 64 c
  left : vdword (s.v .v20) 0 = BitVec.ofNat 64 (len b - c)
  rt : vdword (s.v .v21) 0 = BitVec.ofNat 64 (rate b)
  repr : ∀ msg, stateAt b.mem (st b) = VG.Proof.Sha3.Rep (rate b) msg → msg.length % rate b = 0 →
    A = VG.Proof.Sha3.Rep (rate b) (msg ++ bytesAt b.mem (data b) c)

theorem kept_not_temps : ∀ q ∈ [VReg.v19, .v20, .v21, .v30, .v31],
    q ≠ .v24 ∧ q ≠ .v25 ∧ q ≠ .v28 ∧ q ≠ .v29 := by decide

theorem savedVec_not_kept : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v19 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v20 := by decide

theorem preservedV_not_kept : ∀ q ∈ preservedV, q ≠ .v19 ∧ q ≠ .v20 := by decide

theorem rates_select {r : Nat} (hr : r ∈ Spec.Sha3.rates) : r ∈ [72, 104, 136, 144] ++ [168] := by
  simp only [Spec.Sha3.rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem body_ok (b : State) (hp : BulkPre b) (c : Nat) (A : Spec.Sha3.State) (s : State)
    (h : Loop b c A s) (hc : c + rate b ≤ len b) :
    WP isa body s fun s' => ∃ A', Loop b (c + rate b) A' s' ∧
      isa.eval (.zero .x .x26) s' = some (decide (rate b ≤ len b - (c + rate b))) := by
  have hrb := Sha3.Vector.Resident.rate_bounds hp
  unfold body xorBlock
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.cons (Sha3.Vector.exec_umov_low s .x27 .v19)
    (WP.cons (Sha3.Vector.exec_umov_low _ .x28 .v21) (wp_nil ?_))
  let s₁ := (s.write .x .x27 (vdword (s.v .v19) 0)).write .x .x28
    (vdword ((s.write .x .x27 (vdword (s.v .v19) 0)).v .v21) 0)
  have h27 : s₁.gpr .x27 = data b + BitVec.ofNat 64 c := by
    simp only [s₁, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Size.bits,
      BitVec.setWidth_eq, h.dp]
  have h28 : s₁.gpr .x28 = BitVec.ofNat 64 (rate b) := by
    simp only [s₁, RegUpd.gpr_write_self, RegUpd.v_write, Size.bits, BitVec.setWidth_eq, h.rt]
  have hl₁ : Boundary.Lanes s₁ A := fun i hi => by
    simp only [s₁, RegUpd.gpr_write, (scratch_not_lane .x27 (by simp) i hi),
      (scratch_not_lane .x28 (by simp) i hi), ite_false]
    exact h.core.lanes i hi
  have hin : Covers [⟨s₁.gpr .x27, rate b⟩] (s₁.rd ++ s₁.wr) := by
    change Covers [⟨s₁.gpr .x27, rate b⟩] (s.rd ++ s.wr)
    rw [h.core.keep.rd, h.core.keep.wr, h27, hp.rd]
    apply Covers.of_sub
    intro r hr
    have he := List.mem_singleton.mp hr
    subst r
    exact ⟨dataR b, by simp, c, rfl, hc⟩
  refine (select_ok [72, 104, 136, 144] (by decide) s₁ A hl₁ (rate b) hp.rate_mem
    (rates_select hp.rate_mem) h28 hin).mono fun t ⟨hk, hl⟩ => ?_
  rw [h27] at hl
  have hv : t.v = s.v := hk.v
  have hct : CoreState b (Spec.Sha3.xorBytes A (bytesAt s₁.mem (data b + BitVec.ofNat 64 c) (rate b))) t := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hl⟩
    · exact hk.rd.trans h.core.keep.rd
    · exact hk.wr.trans h.core.keep.wr
    · exact hk.sp.trans h.core.keep.sp
    · simpa only [Ptrs, hv] using h.core.ptrs
    · simpa only [SavedVector, hv] using h.core.saved
    · intro q hq; rw [hv]; exact h.core.vec q hq
  rw [WP.block_append_iff]
  refine (unrolled_rounds_ok b _ t hct).mono fun u ⟨hcu, hku⟩ => ?_
  have hvk : ∀ q ∈ [VReg.v19, .v20, .v21, .v30, .v31], u.v q = s.v q := fun q hq => by
    obtain ⟨a, b', c', d⟩ := kept_not_temps q hq
    rw [hku.v q a b' c' d, hv]
  refine (advance_ok u (data b + BitVec.ofNat 64 c) (len b - c) (rate b) (by omega) (by omega)
    (by have := hp.len_upper; omega) ?_ ?_ ?_).mono fun s' ⟨ha, h19, h20, he⟩ => ?_
  · rw [hvk .v19 (by simp)]; exact h.dp
  · rw [hvk .v20 (by simp)]; exact h.left
  · rw [hvk .v21 (by simp)]; exact h.rt
  refine ⟨Spec.Sha3.keccakF (Spec.Sha3.xorBytes A (bytesAt s₁.mem (data b + BitVec.ofNat 64 c) (rate b))),
    ⟨by omega, ?_, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Nat.add_mod, h.aligned, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
  · exact ha.rd.trans hcu.keep.rd
  · exact ha.wr.trans hcu.keep.wr
  · exact ha.sp.trans hcu.keep.sp
  · simpa only [Ptrs, ha.v .v30 (by decide) (by decide), ha.v .v31 (by decide) (by decide)] using hcu.ptrs
  · intro i hi
    have hn := savedVec_not_kept i hi
    change vdword (s'.v _) 0 = _
    rw [ha.v _ hn.1 hn.2]
    exact hcu.saved i hi
  · intro q hq
    have hn := preservedV_not_kept q hq
    rw [ha.v q hn.1 hn.2]
    exact hcu.vec q hq
  · intro i hi
    rw [ha.gpr _ (scratch_not_lane .x26 (by simp) i hi) (scratch_not_lane .x27 (by simp) i hi)
      (scratch_not_lane .x28 (by simp) i hi)]
    exact hcu.lanes i hi
  · exact ha.mem.trans (hku.mem.trans (hk.mem.trans h.mem))
  · rw [h19, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [h20, Nat.sub_sub]
  · rw [ha.v .v21 (by decide) (by decide), hvk .v21 (by simp)]; exact h.rt
  · intro msg hmsg halign
    have hm : s₁.mem = b.mem := h.mem
    rw [hm, h.repr msg hmsg halign]
    have hal : (msg ++ bytesAt b.mem (data b) c).length % rate b = 0 := by
      simp only [List.length_append, VG.Proof.Sha3.bytesAt_length, Nat.add_mod, halign,
        h.aligned, Nat.zero_add, Nat.zero_mod]
    rw [← Sha3.Vector.rep_whole hrb.1 (by omega) _ _ hal (VG.Proof.Sha3.bytesAt_length _ _ _),
      List.append_assoc, ← bytesAt_add]
  · simpa only [Nat.sub_sub] using he

/-- The loop absorbs whole blocks while at least one is left. -/
theorem loop_ok (b : State) (hp : BulkPre b) (A₀ : Spec.Sha3.State) (s₀ : State)
    (h₀ : Loop b 0 A₀ s₀) :
    WP isa (.loop body (.zero .x .x26)) s₀ fun s => ∃ c A, Loop b c A s := by
  let Inv : Nat → State → Prop := fun n s => ∃ c A, Loop b c A s ∧
    n = len b - c ∧ c + rate b ≤ len b
  refine WP.loop (M := isa) Inv (fun n s ⟨c, A, h, hn, hc⟩ => ?_) (len b) s₀ ?_
  · refine (body_ok b hp c A s h hc).mono fun s' ⟨A', h', he⟩ => ?_
    by_cases hk : rate b ≤ len b - (c + rate b)
    · right
      refine ⟨?_, len b - (c + rate b), ?_, c + rate b, A', h', rfl, ?_⟩
      · simpa only [hk, decide_true] using he
      · have := (Sha3.Vector.Resident.rate_bounds hp).1
        omega
      · omega
    · left
      exact ⟨by simpa only [hk, decide_false] using he, c + rate b, A', h'⟩
  · exact ⟨0, A₀, h₀, by omega, by simpa only [Nat.zero_add] using hp.enough⟩

end VG.Proof.Sha3.AArch64.Scalar.Resident

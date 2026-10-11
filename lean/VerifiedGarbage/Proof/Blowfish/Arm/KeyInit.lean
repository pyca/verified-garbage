import VerifiedGarbage.Proof.Blowfish.Arm.Ecb
import VerifiedGarbage.Proof.Blowfish.KeyTable

/-!
# Blowfish on ARMv7: the initial schedule

`initSchedule_run`: the 1042 words of the initial schedule's image, from
immediates, into the schedule at `r2`.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

theorem initWord32_byte (i : Nat) {b : Nat} (hb : b < 4) :
    (initWord32 i).extractLsb' (8 * b) 8 = initByte (4 * i + b) := by
  have h := initWord_byte (i / 2) (b := 4 * (i % 2) + b) (by omega)
  rw [show 8 * (i / 2) + (4 * (i % 2) + b) = 4 * i + b by omega] at h
  rw [← h, initWord32]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    show 8 * b + j < 32 by omega]
  congr 1; omega

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- One word of the initial schedule. -/
theorem initStore_run (u : State) {i : Nat} (hi : i < 1042) {K : BitVec 32} (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (h11 : u.gpr .r11 = K + BitVec.ofNat 32 0) (h12 : u.gpr .r12 = K + BitVec.ofNat 32 4096)
    (hw : InRegions u.wr (State.addr K + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (initStore i)) u fun t =>
      t.mem = u.mem.writeW (State.addr K + BitVec.ofNat 64 (4 * i)) (initWord32 i) := by
  have e := movw_movt (initWord32 i)
  by_cases h : i < 1024
  · have ea : State.addr (K + BitVec.ofNat 32 0 + BitVec.ofNat 32 (4 * i)) =
        State.addr K + BitVec.ofNat 64 (4 * i) := by rw [ofs_add, Nat.zero_add]; exact addr_add (by omega)
    have ho : 4 * i < 4096 := by omega
    simp only [initStore, h, ite_true]
    brun [h11, ea, hw, ho, e]
  · have ea : State.addr (K + BitVec.ofNat 32 4096 + BitVec.ofNat 32 (4 * (i - 1024))) =
        State.addr K + BitVec.ofNat 64 (4 * i) := by
      rw [ofs_add, show 4096 + 4 * (i - 1024) = 4 * i by omega, addr_add (by omega)]
    have ho : 4 * (i - 1024) < 4096 := by omega
    simp only [initStore, h, ite_false]
    brun [h12, ea, hw, ho, e]

/-- After the first `n` words, from `u₀`. -/
structure InitInv (u₀ : State) (K : BitVec 32) (n : Nat) (t : State) : Prop where
  bytes : ∀ o < 4 * n, t.mem (State.addr K + BitVec.ofNat 64 o) = initByte o
  frame : Frame [⟨State.addr K, 4168⟩] u₀.mem t.mem
  keep : Keep [.r9] u₀ t

theorem initSchedule_steps (u₀ : State) {K : BitVec 32} (fit : K.toNat + 4168 ≤ 2 ^ 32)
    (h11 : u₀.gpr .r11 = K + BitVec.ofNat 32 0) (h12 : u₀.gpr .r12 = K + BitVec.ofNat 32 4096)
    (hw : InRegions u₀.wr (State.addr K) 4168) :
    ∀ n ≤ 1042, WP isa (.block ((List.range n).flatMap initStore)) u₀ (InitInv u₀ K n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun o ho => absurd ho (by omega), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t I => ?_
    have hwt : InRegions t.wr (State.addr K + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [I.keep.2.2.1]; exact inRegions_off hw (by omega)
    refine WP.mono (WP.keep [.r9] (initStore_run t (by omega) fit (by rw [I.keep.gpr (by decide), h11])
      (by rw [I.keep.gpr (by decide), h12]) hwt) (by unfold initStore; split <;> simp [writesOnly, dstOf]))
      fun t' ⟨tm, tk⟩ => ⟨fun o ho => ?_, ?_, (I.keep.trans tk).mono (by decide)⟩
    · rw [tm]
      by_cases hl : o < 4 * n
      · rw [writeW32_other _ (Offset.disjoint _ (by omega) (by omega) (by omega)), I.bytes o hl]
      · rw [show o = 4 * n + (o - 4 * n) by omega, ← Offset.add_add, st_byte _ _ _ (by omega),
          initWord32_byte _ (by omega)]
    · rw [tm]
      exact I.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Blowfish.Arm

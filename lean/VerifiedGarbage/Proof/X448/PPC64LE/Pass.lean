module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Impl.X448.PPC64LE
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X448 on PPC64LE: carrying sums into limbs

`pass rb o src` stores at `rb + o` the 14 limbs of `Σ c_k 2^(32k) + cin`, from
the sums `c_k` that `src k` leaves in `r7` and the carry `cin` in `r8`
(`pass_ok`), with X25519's invariant (`PassInv`) and step (`carryStep_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r5, .r7, .r8]) (hrb0 : rb ≠ .r0) (ho : o + 56 ≤ 4096)
    (hw : ∀ k < 14, InRegions s0.wr (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h8 : (s0.gpr .r8).toNat = cin)
    (hc : ∀ k < 14, c k + 2 ^ 32 ≤ 2 ^ 64) (hcin : cin < 2 ^ 32)
    (hsrc : ∀ k < 14, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r7).toNat = c k ∧ Rest [.r5, .r7] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (PassInv rb o s0 c cin 14) := by
  have hr := not_mem3 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h8]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h7, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1]), h.rest.gpr _ hrb]
  have h81 : s1.gpr .r8 = s.gpr .r8 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := s0.gpr rb + BitVec.ofNat 64 (o + 4 * k))
    ⟨hr.2.1, hrb0⟩ (by omega_using [ho, hk]) (by rw [hrb1])
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [h7, h81, h.r8]; exact hsum)) fun s2 ⟨e8, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h7, h81, h.r8] at e8 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e8]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [ho, hk]))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_using [])
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega_using [ho, hk, hj]) (by omega_using [ho, hk])]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X448.PPC64LE

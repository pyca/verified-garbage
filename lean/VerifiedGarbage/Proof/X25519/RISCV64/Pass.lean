module

public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on RISCV64: carrying sums into limbs

`pass rb o src` stores at `rb + o` the limbs of `Σ c_k 2^(32k) + cin`, from
the sums `c_k` that `src k` leaves in `a4` and the carry `cin` in `a5`
(`pass_ok`), for any `src` that computes them from the memory as it was, but
for the limbs already stored (`PassInv.frame`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64

theorem not_mem3 {r : Reg} (h : r ∉ [Reg.a2, .a4, .a5]) : r ≠ .a2 ∧ r ≠ .a4 ∧ r ≠ .a5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

theorem carryStep_ok {rb : Reg} {off : Nat} {s : State} {a : Addr}
    (hrb : rb ≠ .a4) (ho : off < 2048)
    (ha : s.gpr rb + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0) (hw : InRegions s.wr a 4)
    (hs : (s.gpr .a4).toNat + (s.gpr .a5).toNat < 2 ^ 64) :
    WP isa (.block (carryStep rb off)) s fun s' =>
      (s'.gpr .a5).toNat = ((s.gpr .a4).toNat + (s.gpr .a5).toNat) / 2 ^ 32 ∧
      (∃ v : BitVec 32, v.toNat = ((s.gpr .a4).toNat + (s.gpr .a5).toNat) % 2 ^ 32 ∧
        s'.mem = s.mem.writeW a v) ∧
      Rest [.a4, .a5] s s' := by
  unfold carryStep
  refine wp_add fun s1 u1 => ?_
  refine wp_sw (a := a) ho (by rw [u1.other _ hrb]; exact ha) hal
    (by rw [u1.wr]; exact hw) fun s2 u2 => ?_
  refine wp_srl (by decide) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .a4).toNat = (s.gpr .a4).toNat + (s.gpr .a5).toNat := by
    rw [u1.gpr]; exact toNat_add_lt hs
  refine ⟨?_, ⟨(s1.gpr .a4).setWidth 32, ?_, ?_⟩, ?_⟩
  · rw [u3.gpr, u2.gpr, toNat_shr, e1]
  · rw [toNat_lo32, e1]
  · rw [u3.mem, u2.mem, u1.mem]
  · refine ⟨fun r hr => ?_, by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr],
      by rw [u3.sp, u2.sp, u1.sp]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2, u2.gpr, u1.other _ hr.1]

/-- After `k` limbs of `pass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure PassInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.a2, .a4, .a5] s0 s
  a5 : (s.gpr .a5).toNat = chain c cin k
  frame : Frame [⟨s0.gpr rb + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (s0.gpr rb) (o + 4 * j) = out c cin j

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.a2, .a4, .a5]) (ho : o + 32 ≤ 2048)
    (hw : ∀ k < 8, InRegions s0.wr (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)) 4)
    (hal : ∀ k < 8, (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)).toNat % 4 = 0)
    (h8 : (s0.gpr .a5).toNat = cin)
    (hc : ∀ k < 8, c k + 2 ^ 32 ≤ 2 ^ 64) (hcin : cin < 2 ^ 32)
    (hsrc : ∀ k < 8, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .a4).toNat = c k ∧ Rest [.a2, .a4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (PassInv rb o s0 c cin 8) := by
  have hr := not_mem3 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) 8 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h8]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h7, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1]), h.rest.gpr _ hrb]
  have h81 : s1.gpr .a5 = s.gpr .a5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := s0.gpr rb + BitVec.ofNat 64 (o + 4 * k))
    hr.2.1 (by omega_using [ho, hk]) (by rw [hrb1]) (hal k hk)
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [h7, h81, h.a5]; exact hsum)) fun s2 ⟨e8, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h7, h81, h.a5] at e8 hv
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

end VG.Proof.X25519.RISCV64

module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWNorm
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFirst
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWStep
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFin
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

-- separate module: the square root's run composed, apart from `SizedW`'s so a change to either rebuilds only it

/-! # The integer square root of Appendix C.2 on i686, by words

`RecoverDetRt.sqrt`: the radicand normalized (`normX`, `Rd/SqrtWNorm.lean`), its first digit by
bit pairs (`firstX`, `Rd/SqrtWFirst.lean`), a digit per word (`stepX`, `Rd/SqrtWStep.lean`,
`W' - 1` times, `sCt` counting them) and the root shifted back, with whether the radicand is a
square (`finishX`, `Rd/SqrtWFin.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa.X86.WordRt (wq MLen)

/-- The square root of the wide `[wR]` modulo `2^(64 W')` (`W' = wq a` for `a = n_len ≤ 1024`, the
argument `nl`): the root in `aY`, and whether `X` is a square in `sOk5`. -/
theorem sqrt_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {X a : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] V sqSlotsW u) (z : A aZero = 0) (hX : AW wR = X)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 1 ≤ a)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w) (ha1 : a ≤ 1024) :
    WP isa sqrt u fun v => ∃ A' AW',
      KS g s0 A' [aY, aD, aZero] AW' [] (upd V sOk5 (if isqrt (X % 2 ^ (64 * VG.Proof.Rsa.X86.WordRt.wq a)) *
          isqrt (X % 2 ^ (64 * VG.Proof.Rsa.X86.WordRt.wq a)) = X % 2 ^ (64 * VG.Proof.Rsa.X86.WordRt.wq a)
          then 1 else 0))
        (sOk5 :: sqSlotsW) v ∧
      A' aY = isqrt (X % 2 ^ (64 * VG.Proof.Rsa.X86.WordRt.wq a)) ∧ A' aD = A aD ∧ A' aZero = 0 := by
  have hw1 : 1 ≤ wq a := by simp only [wq]; omega
  unfold sqrt
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (normX_ok h hX ha ha1 ha0 haw)
    fun u1 ⟨AW1, V1, h1, e1, ez, eX1, lt1, ge1, hK, hzb, hzb'⟩ => ?_)
  refine WP.seq (WP.mono (firstX_ok h1 rfl ha ha1 ha0 haw lt1 ge1) fun u2 ⟨AW2, V2, s₀, r₀, h2, e2, hR2⟩ => ?_)
  -- `sCt := W' - 1`.
  refine WP.seq (WP.mono (Q := fun (u4 : State) => u4.zf = some (decide (wq a - 1 = 0)) ∧
    SqI g s0 A V1 a (AW1 wR) (wq a - 1) u4) ?_ fun u4 ⟨zf4, I4⟩ => ?_)
  · refine VG.Proof.Rsa.X86.WordRt.width4_ok (h2.mlen ha ha1) fun u3 K3 m3 e3 => ?_
    have h3 := h2.of_rest K3 (by decide) m3
    refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u4 U4 => ?_
    refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun u5 U5 z5 => ?_
    have h5 := (h3.of_rest U4.keeps (by decide) U4.mem).of_rest U5.keeps (by decide) U5.mem
    have v5 : (u5.gpr .eax).toNat = wq a - 1 := by
      rw [U5.gpr, U4.gpr, e3, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat, Nat.reducePow]
      have := ha1; simp only [wq] at hw1 ⊢; omega
    refine WP.mono (h5.storeSlot (d := sCt) (by decide) .eax) fun u6 ⟨h6, zf6, _⟩ => ?_
    refine ⟨?_, AW2, upd V2 sCt (wq a - 1), s₀, r₀, ?_, ?_, ?_, ?_⟩
    · rw [zf6, z5, ← U5.gpr]; congr 1
      by_cases e : wq a - 1 = 0
      · simp only [e, decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [v5, e]; rfl
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro c; have := congrArg BitVec.toNat c; rw [v5] at this; exact e this
    · rw [v5] at h6; exact h6
    · intro d hd
      have : d ≠ sCt := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [upd_ne _ _ this, e2 d hd]
    · rw [upd_self]
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hR2
      have n1 : VG.Impl.Rsa.X86.WordModRt.oD ≠ sCt := by decide
      have n2 : VG.Impl.Rsa.X86.WordModRt.oV ≠ sCt := by decide
      exact ⟨a1, a2, a3, a4, by rw [upd_ne _ _ n1]; exact a5, by rw [upd_ne _ _ n1]; exact a6, a7,
        by rw [upd_ne _ _ n2, upd_ne _ _ n1]; exact a8⟩
  -- The digits.
  refine WP.seq (WP.mono (Q := SqI g s0 A V1 a (AW1 wR) 0) (WP.ite (decide (wq a - 1 = 0)) (by simp only [eval]; exact zf4)
    (fun e => WP.block_nil (by have := of_decide_eq_true e; rw [this] at I4; exact I4)) (fun e => ?_))
    fun u5 I5 => ?_)
  · have e' := of_decide_eq_false e
    refine WP.loop (fun n v => 1 ≤ n ∧ n < wq a ∧ SqI g s0 A V1 a (AW1 wR) n v) ?_ (wq a - 1) u4
      ⟨by omega, by omega, I4⟩
    rintro n v ⟨hn1, hn, I⟩
    refine WP.mono (stepX_ok I ha ha1 haw hn1 hn) fun v' ⟨zf, I'⟩ => ?_
    by_cases e : n - 1 = 0
    · refine .inl ⟨by simp only [eval, zf, e, decide_true, Option.map_some, Bool.not_true], ?_⟩
      rw [e] at I'; exact I'
    · exact .inr ⟨by simp only [eval, zf, e, decide_false, Option.map_some, Bool.not_false], n - 1, by omega,
        by omega, by omega, I'⟩
  refine WP.mono (finishX_ok I5 z ha ha1 ha0 haw ez eX1 hK hzb hzb') fun v ⟨A', AW', hv, ey, ed, ez'⟩ => ?_
  refine ⟨A', AW', hv.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj) (fun d hd => ⟨hd, ?_⟩), ey, ed, ez'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · simp only [upd_self]
  all_goals
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    exact e1 _ (by decide)

end VG.Proof.Rsa.X86.Recover

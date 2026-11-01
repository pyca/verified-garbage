module

import VerifiedGarbage.Proof.X448.RISCV64.Invert
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# Ed448 on RISCV64: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `(p - 3) / 4` from 445 down to 0
(`rootQ_ok`), as X448's inversion computes `z^(p-2)`
(`Proof/X448/RISCV64/Invert.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (R Z2 one)
open VG.Spec.X448 (P Fe)

/-! ## The bits of `(p - 3) / 4` -/

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

def rbitsB : Nat → Bool
  | 0 => true
  | t + 1 => (RE >>> t % 2 == if t = 222 then 0 else 1) && rbitsB t

theorem rbitsB_ok : rbitsB 446 = true := by decide +kernel

/-- Every bit of `RE = 2⁴⁴⁶ - 2²²² - 1` below 446 but bit 222 is 1. -/
theorem rbits : ∀ t < 446, RE >>> t % 2 = if t = 222 then 0 else 1 := by
  have : ∀ n, rbitsB n = true → ∀ t < n, RE >>> t % 2 = if t = 222 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega_using [ht]
    | succ n ih =>
      intro h t ht
      simp only [rbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 446 rbitsB_ok

theorem r446 : RE >>> 446 = 0 := by decide +kernel

section
variable {b : Addr}

/-- `z^(((p - 3) / 4) >> n)` in `R`, for `z` at `Z2`. -/
def rootV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X448.pw (v Z2) (RE >>> n))

/-- The loop invariant of `root` from `sI`, before the step for the bit `n - 1`. -/
structure RootInv (b : Addr) (sI : State) (a : BitVec 64) (qs : List Nat) (v : Nat → Fe) (n : Nat)
    (s : State) : Prop where
  cur : R64.Cur b sI a (BitVec.ofNat 64 n) qs (rootV v n) s

theorem rootStep_ok {sI : State} {a : BitVec 64} {qs : List Nat} (hq : R64.Sep8 R qs = true) (hR : R ∈ qs)
    (hZ : Z2 ∈ qs) {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 446)
    {s : State} (h : RootInv b sI a qs v n s) :
    WP isa rootStep s fun s' => RootInv b sI a qs v (n - 1) s' ∧ (s'.gpr .t1 != 0) = decide (n - 1 ≠ 0) := by
  obtain ⟨hcur⟩ := h
  have hb := rbits (n - 1) (by omega_using [hn'])
  have he := shr_step RE (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold rootStep
  refine WP.seq (wp_subi (by decide) fun s1 u1 => WP.block_nil ?_)
  have h1 : R64.Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide),
      hcur.stp.trans (R64.Stp.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hcur.t2], ?_, by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr, hcur.t1, ofNat_sub_one hn (by omega_using [hn'])]
  refine WP.seq (WP.mono (R64.opMul (o := R) (x := R) (y := R) hq (by decide) hR hR h1)
    fun s2 h2 => ?_)
  have hsq : ∀ q ∈ qs, upd (rootV v n) R (rootV v n R * rootV v n R) q =
      upd v R (VG.Proof.X448.pw (v Z2) (2 * (RE >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X448.pw_mul]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := qs) (fun q hq' => List.mem_cons_of_mem _ hq') hsq
  refine WP.seq (WP.mono (R64.cmp_ok (d := 222) (by omega_using [hn']) (by decide) h2') fun s3 ⟨h3, hz3⟩ => ?_)
  refine WP.mono (Q := R64.Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v (n - 1))) ?_ fun s4 h4 =>
    ⟨⟨h4⟩, by rw [h4.t1, ofNat_ne_zero (by omega_using [hn'])]⟩
  refine WP.ite _ hz3 (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
  · have h4 : n - 1 = 222 := by simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, he, hb, iteT h4, Nat.add_zero]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 222 := by simpa using hf
    refine WP.mono (R64.opMul (o := R) (x := R) (y := Z2) hq (by decide) hR hZ h3)
      fun s5 h5 => h5.congr (fun q hq' => List.mem_cons_of_mem _ hq') fun q _ => ?_
    by_cases hq : q = R
    · subst hq
      rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), rootV, upd_self, he, hb,
        iteF h4, ← VG.Proof.X448.pw_mul, VG.Proof.X448.pw_one]
    · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]

theorem rootQ_ok {qs : List Nat} (hq : R64.Sep8 R qs = true) (hR' : R ∈ qs) (hZ : Z2 ∈ qs)
    {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa root s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (RE))) := by
  have hR : R = 840 := rfl
  unfold root
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.a1, .a2] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine sw0_ok hc2 (d := R) (by decide) (by omega_arith) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 13) (by decide) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.a1, .a2, .t1] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 14, limb s5.mem b R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, toNat_lo32, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf5 : Frame [⟨b + BitVec.ofNat 64 R, 56⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) ((s2.gpr .a1).setWidth 32)
      (Offset.contains b (d := R) (n := 32 / 8) (e := R) (k := 56) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : R64.Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩⟩
  have hS5 : SlotsOk s5.mem b qs (rootV v 446) := by
    have hA := ACC_eq
    intro q hq'
    by_cases hqR : q = R
    · subst hqR
      rw [FS, V, val32_congr hlimb, rootV, upd_self, r446, pw_zero, val32_single _ (by decide)]
      rfl
    · obtain ⟨h1, h3⟩ := sep1_get (R64.sep8_sep1 hq) hq'
      have e := limb_frame (o := q) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (by omega_using [hqR, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, rootV, upd_of_ne _ _ hqR]; exact hS q hq' hqR
  have h446 : RootInv b s5 a qs v 446 s5 :=
    ⟨⟨hc5, R64.Stp.refl _ _, by rw [hr5.gpr _ (by decide), h0], u5.gpr, hS5⟩⟩
  refine WP.mono (Q := RootInv b s5 a qs v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 446 ∧ RootInv b s5 a qs v m s') ?_ 446 s5 ⟨by decide, Nat.le_refl _, h446⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [rootV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (rootStep_ok hq hR' hZ h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩


end

end VG.Proof.Ed448.RISCV64

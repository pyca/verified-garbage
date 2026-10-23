module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Ladder
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on PPC64LE: the inversion

`invert` computes `z^(p-2)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `p - 2` from 254 down to 0 (`invert_ok`):
after the bits down to `n`, `R` holds `z^((p - 2) >> n)`.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)

/-! ## The bits of `p - 2` -/

def pbitsB : Nat → Bool
  | 0 => true
  | t + 1 => ((P - 2) >>> t % 2 == if t = 4 ∨ t = 2 then 0 else 1) && pbitsB t

theorem pbitsB_ok : pbitsB 255 = true := by decide +kernel

/-- Every bit of `p - 2 = 2²⁵⁵ - 21` but bits 4 and 2 (and those from 255 up) is 1. -/
theorem pbits : ∀ t < 255, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
  have : ∀ n, pbitsB n = true → ∀ t < n, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega_using [ht]
    | succ n ih =>
      intro h t ht
      simp only [pbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 255 pbitsB_ok

theorem p255 : (P - 2) >>> 255 = 0 := by decide +kernel

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem shr_step (x t : Nat) : x >>> t = 2 * (x >>> (t + 1)) + x >>> t % 2 := by
  rw [Nat.shiftRight_succ]; omega_using []

section
variable {b : Addr}

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X25519.pw (v Z2) ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : Addr) (sI : State) (a : BitVec 64) (v : Nat → Fe) (n : Nat) (s : State) :
    Prop where
  cur : Cur b sI a (BitVec.ofNat 64 n) IQ (invV v n) s

theorem sub_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 x) (BitVec.ofNat 64 y), h']; simp
    have := congrArg BitVec.toNat e
    rwa [toNat_imm hx, toNat_imm hy] at this

theorem Cur.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r0, h.r12, (h.slots.mono hq).congr hv⟩

/-- `subi r5, r12, d`, and the branch on `r5 = 0`. -/
theorem cmp_ok {s0 s : State} {a : BitVec 64} {qs : List Nat} {v : Nat → Fe} {m d : Nat}
    (hm : m < 255) (hd : d < 255) (h : Cur b s0 a (BitVec.ofNat 64 m) qs v s) :
    WP isa (.block [.subi .r5 .r12 d]) s fun s' => Cur b s0 a (BitVec.ofNat 64 m) qs v s' ∧
      isa.eval (.zero .d .r5) s' = some (decide (m = d)) := by
  refine wp_subi (by decide) (by omega_using [hd]) fun s1 u1 => WP.block_nil ⟨h.next (u1.rest (by decide))
    (by rw [u1.mem]; exact Frame.refl _ _) (by rw [u1.mem]; exact h.slots), ?_⟩
  rw [eval_zero, u1.gpr, h.r12, sub_beq (by omega_using [hm]) (by omega_using [hd])]

theorem invStep_ok {sI : State} {a : BitVec 64} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI a v n s) :
    WP isa invStep s fun s' => InvInv b sI a v (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  obtain ⟨hcur⟩ := h
  have hb := pbits (n - 1) (by omega_using [hn'])
  have he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have h1 : Cur b sI a (BitVec.ofNat 64 (n - 1)) IQ (invV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hcur.r0], ?_, by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_using [hn'])]
  refine WP.seq (WP.mono (opMul (o := R) (x := R) (y := R) (by decide) (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  -- After the square.
  have hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := IQ) (by decide) hsq
  refine WP.seq (WP.mono (cmp_ok (d := 4) (by omega_using [hn']) (by decide) h2') fun s3 ⟨h3, hz3⟩ => ?_)
  refine WP.seq (WP.mono (Q := Cur b sI a (BitVec.ofNat 64 (n - 1)) IQ (invV v (n - 1))) ?_ fun s4 h4 =>
    WP.block_nil ⟨⟨h4⟩, by rw [h4.r12, ofNat_ne_zero (by omega_using [hn'])]⟩)
  refine WP.ite _ hz3 (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
  · have h4 : n - 1 = 4 := by simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 4 := by simpa using hf
    refine WP.seq (WP.mono (cmp_ok (d := 2) (by omega_using [hn']) (by decide) h3) fun s4 ⟨h4', hz4⟩ => ?_)
    refine WP.ite _ hz4 (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
    · have h2 : n - 1 = 2 := by simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h2 : n - 1 ≠ 2 := by simpa using hf
      refine WP.mono (opMul (o := R) (x := R) (y := Z2) (by decide) (by decide) (by decide) (by decide) h4')
        fun s5 h5 => h5.congr (by decide) fun q _ => ?_
      by_cases hq : q = R
      · subst hq
        rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
          iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega), ← VG.Proof.X25519.pw_mul,
          VG.Proof.X25519.pw_one]
      · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]

theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .r0 = a) :
    WP isa Impl.X25519.PPC64LE.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 480 := rfl
  unfold Impl.X25519.PPC64LE.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r4, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine sw0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 7) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r4, .r5, .r12] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 8, limb s5.mem b R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, toNat_lo32, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf5 : Frame [⟨b + BitVec.ofNat 64 R, 32⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) ((s2.gpr .r4).setWidth 32)
      (Offset.contains b (d := R) (n := 32 / 8) (e := R) (k := 32) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩⟩
  have hS5 : SlotsOk s5.mem b IQ (invV v 255) := by
    have hZ2 : Z2 = 64 := rfl
    have hX2 : X2 = 32 := rfl
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e := limb_frame (o := Z2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hZ2, hR, hk])) (by omega_using [hZ2, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, invV, upd_of_ne _ _ (by decide)]; exact hS Z2 (by decide)
    · rw [FS, V, val32_congr hlimb, invV, upd_self, p255, VG.Proof.X25519.pw_zero]
      rfl
    · have e := limb_frame (o := X2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX2, hR, hk])) (by omega_using [hX2, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, invV, upd_of_ne _ _ (by decide)]; exact hS X2 (by decide)
  have h255 : InvInv b s5 a v 255 s5 :=
    ⟨⟨hc5, Stp.refl _ _, by rw [hr5.gpr _ (by decide), h0], u5.gpr, hS5⟩⟩
  refine WP.mono (Q := InvInv b s5 a v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s5 a v m s') ?_ 255 s5 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩

end

end VG.Proof.X25519.PPC64LE

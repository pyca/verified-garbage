module

public import VerifiedGarbage.Proof.X25519.X86.Step
import VerifiedGarbage.Proof.X25519.X86.Field32.Call
public import VerifiedGarbage.Impl.X25519.X86.Fn
public import VerifiedGarbage.Proof.X25519.X86.Field32.Chain
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit

/-!
# X25519 on x86 (32-bit): the inversion

`z2` copied to byte 128, a call of `vg_gf25519_r32_pow250`
(`pow250Call_ok'`), then five squarings and a product (`Field32`'s `sqnC` and
`mulC`) leave `invert z2` in `E1` (`invert_ok`). The copy overwrites the
scalar's bits and the call the 8 bytes of stack below `esp`: from then on,
what holds is `After`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw pw_mul sqn_pw pow_pw)
open VG.Proof.X25519.X86.Field32 (Cs CSpec cenv opMul opSqn sqnC mulC pow250Call_ok')

/-- What holds after the inversion: `Base` without the scalar's bits, with
the 8 bytes of stack below `esp` on entry (`callStk s₀`) changed too. -/
structure After (x : BitVec 32) (s₀ s : State) : Prop where
  ctx : Ctx 4096 x s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 x, callStk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr savedSlots

theorem Base.after {x : BitVec 32} {k : Nat} {s₀ s : State} (h : Base x k s₀ s) : After x s₀ s :=
  ⟨h.ctx, h.esp, h.rd, h.wr, h.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., h.saved⟩

/-- A change of the working space past the saved registers keeps `After`. -/
theorem After.of_frame {x : BitVec 32} {s₀ s s' : State} (h : After x s₀ s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {o n : Nat} (hf : Frame [sub x o n] s.mem s'.mem) (ho : o + n ≤ 4096)
    (hlo : 16 ≤ o) (hon : o < 4096) : After x s₀ s' := by
  have hfit := h.ctx.fit
  refine ⟨h.ctx.keep hedi hwr hesp, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr, scR_eq]
      exact sub_sub hfit (Nat.zero_le _) (by omega_using [ho]) hon⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit ho (by omega_using [this]) (.inl (by omega_using [this, hlo]))

/-- The operations keep `After`. -/
theorem After.ops {x : BitVec 32} {s₀ s s' : State} (h : After x s₀ s) (hk : Keep s s')
    (hf : Frame [sub x 288 640] s.mem s'.mem) : After x s₀ s' :=
  h.of_frame hk.edi hk.esp hk.rd hk.wr hf (by decide) (by decide) (by decide)

/-- The chain's tail for the inversion: five squarings, and `z^11`. -/
theorem invert_tail (z : Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 5 * pw z 11 = VG.Proof.X25519.invert z := by
  rw [VG.Proof.X25519.invert_eq, pow_pw, sqn_pw, pw_mul]
  exact congrArg (pw z) (by decide)

theorem tail_spec (x : BitVec 32) :
    CSpec x (.seq (Field32.sqn Field32.E1 Field32.E1 5) (.block (mul Field32.E1 Field32.E1 Field32.E0)))
      (fun e => opMul 1 1 0 (opSqn 1 1 5 e)) :=
  (sqnC x 1 1 5 (by decide) (by decide)).seq (mulC x 1 1 0)

/-- The inversion, from `Base` with the stack below `esp` apart from the working space. -/
theorem invert_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (h : Base x k s₀ s)
    (hE : 8 ≤ (s₀.gpr .esp).toNat) (hd : (scR 4096 x).Disjoint (callStk s₀)) :
    WP isa Impl.X25519.X86.invert s fun s' => After x s₀ s' ∧
      F s'.mem x Field32.E1 = VG.Proof.X25519.invert (F s.mem x Z2) ∧ F s'.mem x X2 = F s.mem x X2 := by
  have hfit := h.ctx.fit
  -- `z2` to byte 128.
  refine WP.seq (WP.mono (copy_ok h.ctx (o := Impl.X25519.X86.Field32.aAt) (a := Z2) (by decide) (by decide)
    (by decide)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
  have a₁ := h.after.of_frame k₁.edi k₁.esp k₁.rd k₁.wr f₁ (by decide) (by decide) (by decide)
  have z₁ : F s₁.mem x Impl.X25519.X86.Field32.aAt = F s.mem x Z2 := congrArg toFe e₁
  have x₁ : F s₁.mem x X2 = F s.mem x X2 := congrArg toFe (fe_frame1 f₁ hfit (by decide) (by decide) (by decide))
  -- The call.
  have cs₁ : callStk s₁ = callStk s₀ := by rw [callStk, callStk, a₁.esp]
  refine WP.seq (WP.mono (pow250Call_ok' a₁.ctx (by rw [a₁.esp]; exact hE) (cs₁ ▸ hd))
    fun s₂ ⟨k₂, f₂, p₁, p₀⟩ => ?_)
  rw [cs₁] at f₂
  have w₂ : ∀ d, d + 4 ≤ 512 → wd s₂.mem x d = wd s₁.mem x d := fun d hd' =>
    wd_frame f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega_using [hfit, hd']) (by omega_using [hfit]) (.inl hd')
      · exact hd.sub_left (by
          rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hd']) (by omega_using [hd']))
  have a₂ : After x s₀ s₂ := by
    refine ⟨k₂.ctx a₁.ctx, k₂.esp.trans a₁.esp, k₂.rd.trans a₁.rd, k₂.wr.trans a₁.wr,
      a₁.frame.trans (f₂.sub fun r hr => ?_), a₁.saved.of_readW fun p hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by
          rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · have := savedSlots_bound p hp
      exact w₂ _ (by omega_using [this])
  have x₂ : F s₂.mem x X2 = F s₁.mem x X2 :=
    congrArg toFe (fe_frame fun j hj => w₂ _ (by simp only [X2]; omega_using [hj]))
  -- Five squarings and `z^11`.
  refine WP.mono (tail_spec x s₂ a₂.ctx) fun s₃ ⟨k₃, e₃⟩ => ?_
  refine ⟨a₂.of_frame k₃.edi k₃.esp k₃.rd k₃.wr k₃.frame (by decide) (by decide) (by decide), ?_, ?_⟩
  · change cenv s₃.mem x 1 = _
    rw [e₃]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (0 : Cs) ≠ 1 by decide)]
    change VG.Proof.X25519.sqn (F s₂.mem x Field32.E1) 5 * F s₂.mem x Field32.E0 = _
    rw [p₁, p₀, z₁, invert_tail]
  · rw [← x₁, ← x₂]
    exact congrArg toFe (fe_frame1 k₃.frame hfit (by decide) (by decide) (by decide))

end VG.Proof.X25519.X86

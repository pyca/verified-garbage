import VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder
import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. `z` (slot 2) copied to slot 12,
a call of `vg_gf448_r56_pow_p34` (`powCall_ok`) with the return address kept in a
lane of `v8` (`call_spec`), and the power squared twice and multiplied by `z`:
slot 21 ends as `z^(p-2)` (`invEnv_eval`), since `z^(p-2) = (z^((p-3)/4))^4 z`
(`invert_rootPow`). It keeps what the inlined chain did (`IKeep`).
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Keeps Scr)
open VG.Proof.X448.AArch64.Weak (Index Env FieldOp applyOps opMul opCopy opSqn)
open VG.Proof.Ed448.AArch64 (rootEnv rootEnv_eval rootEnv_keep)
open VG.Proof.Ed448.AArch64.Point56 (CKeep powCall_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `z^(p-2)` is `(z^((p-3)/4))^4 z`. -/
theorem invert_rootPow (z : Spec.X448.Fe) :
    Proof.X448.sqn (Proof.Ed448.rootPow z) 2 * z = Proof.X448.invert z := by
  have e : (Spec.X448.P - 3) / 4 * 2 ^ 2 + 1 = Spec.X448.P - 2 := by decide +kernel
  calc Proof.X448.sqn (Proof.Ed448.rootPow z) 2 * z
      = Proof.X448.sqn (Proof.X448.pw z ((Spec.X448.P - 3) / 4)) 2 * Proof.X448.pw z 1 := by
        rw [Proof.Ed448.rootPow_eq, Proof.X448.pow_pw, Proof.X448.pw_one]
    _ = Proof.X448.pw z ((Spec.X448.P - 3) / 4 * 2 ^ 2 + 1) := by
        rw [Proof.X448.sqn_pw, Proof.X448.pw_mul]
    _ = Proof.X448.pw z (Spec.X448.P - 2) := congrArg (Proof.X448.pw z) e
    _ = Proof.X448.invert z := by rw [Proof.X448.invert_eq, Proof.X448.pow_pw]

/-- The call, with the return address kept in `v8`: the slots as after `root 12`. -/
theorem call_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.powCallKeep rootEnv := by
  intro s hs hb
  rw [Impl.X448.AArch64.Fast.powCallKeep, WP.seq_iff]
  refine WP.mono (insOf_ok [(.x30, .v8, 0)] s (by decide) (by decide))
    fun t₁ ⟨g₁, m₁, r₁, w₁, _, l₁, _⟩ => ?_
  have hs₁ : Scr t₁ base := hs.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide)
  rw [WP.seq_iff]
  refine WP.mono (powCall_ok hs₁ (m₁ ▸ hb)) fun t ⟨ck, pb, pe, _⟩ => ?_
  refine WP.mono (umovOf_ok [(.x30, .v8, 0)] t (by decide) (by decide))
    fun u ⟨um, ur, uw, _, ul, uo⟩ => ?_
  have l30 : u.gpr .x30 = s.gpr .x30 := by
    rw [ul _ List.mem_cons_self, ← l₁ _ List.mem_cons_self]
    exact ck.v .v8 (by decide)
  refine ⟨⟨⟨fun r hr => ?_, by rw [ur, ck.regs.2.1, r₁], by rw [uw, ck.regs.2.2, w₁]⟩,
    by rw [um, ← m₁]; exact ck.mem⟩, by rw [um]; exact pb, by rw [um, pe, m₁]⟩
  by_cases h30 : r = .x30
  · rw [h30]; exact l30
  · rw [uo r (by simpa using h30), ck.regs.1 r fun h => hr ((List.mem_cons.mp h).resolve_left h30 |> List.mem_cons_of_mem _), g₁]

/-- The slots after the inversion. -/
def invEnv (e : Env) : Env :=
  applyOps [.mul 21 21 2] (opSqn 21 2 (rootEnv (applyOps [.copy 12 2] e)))

theorem invert_spec (base : Addr) : ISpec base Impl.X448.AArch64.Fast.invert invEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 12 2] (by simp [MulCopy])).seq <| (call_spec base).seq <|
      (sqnI base 21 (n := 2) (by decide) (by decide)).seq (opsI base [.mul 21 21 2] (by simp [MulCopy]))
  exact h

theorem invEnv_eq (e : Env) :
    invEnv e = opMul 21 21 2 (opSqn 21 2 (rootEnv (opCopy 12 2 e))) := rfl

theorem invEnv_eval (e : Env) : invEnv e 21 = Proof.X448.invert (e 2) := by
  have h2 : rootEnv (opCopy 12 2 e) 2 = e 2 := by
    rw [rootEnv_keep _ 2 (by decide)]; rfl
  have h21 : rootEnv (opCopy 12 2 e) 21 = Proof.Ed448.rootPow (e 2) := by
    rw [rootEnv_eval]; rfl
  rw [invEnv_eq]
  simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (2 : Index) ≠ 21 by decide),
    h2, h21]
  exact invert_rootPow (e 2)

theorem invEnv_keep (e : Env) (i : Index) (hi : i.val < 12) : invEnv e i = e i := by
  have h12 : i ≠ 12 := fun h => absurd hi (by rw [h]; decide)
  have h21 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  rw [invEnv_eq]
  simp only [opMul, opSqn, opCopy, Function.update_of_ne h21, rootEnv_keep _ i (by omega),
    Function.update_of_ne h12]

theorem invEnv_x2 (e : Env) : invEnv e 1 = e 1 := invEnv_keep e 1 (by decide)

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa Impl.X448.AArch64.Fast.invert s fun t =>
      IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = invEnv (EV s.mem base) :=
  invert_spec base s hs hb

end VG.Proof.X448.AArch64.Fast

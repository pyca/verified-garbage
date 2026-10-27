module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Ed25519.RISCV64.Encode
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.Ed25519.RISCV64.Power
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on RISC-V: the candidate `x` of a decoding

`rootPower_ok`: slot 15 is `z^((p - 5) / 8)` for `z` in slot 2, by a call of
`vg_gf25519_r32_pow250`, two squarings and a product. `recoverCandidate_ok`:
from `y` in slot 1, `u = y² - 1` in slot 6, `v = d y² + 1` in slot 7, the
candidate `x = u v³ (u v⁷)^((p - 5) / 8)` (`rootX`) in slot 0, `v x²` in slot
11 and `-u` in slot 12, as `recoverX` computes them.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX)

theorem root_exp : (2 ^ 250 - 1) * 2 ^ 2 + 1 = (P - 5) / 8 := by decide

section
variable {b : Addr}

/-- **`z^((p - 5) / 8)`** of slot 2, into slot 15; slots 0–13 kept. -/
theorem rootPower_ok {s : State} (hc : Ctx8 b s) :
    WP isa rootPower s fun t => Keep b s t ∧
      env t.mem b 15 = Spec.X25519.pow (env s.mem b 2) ((P - 5) / 8) ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold Impl.Ed25519.RISCV64.rootPower
  refine WP.seq (WP.mono (power250_ok hc) fun t1 ⟨k1, e15, _, ek⟩ => ?_)
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (WP.mono (sqnLoop_ok hc1.ctx 15 (by decide) (n := 2) (by decide) (by decide))
    fun t2 ⟨r2, f2, e2⟩ => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (mulCall_ok hc2.ctx hc2.ws 15 15 2) fun t3 ⟨k3, e3⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine k1.trans (Keep.trans ⟨r2.mono (by decide), f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩⟩ k3)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
  · have hz : env t1.mem b 2 = env s.mem b 2 := ek 2 (by decide)
    rw [e3, Function.update_self, e2, Function.update_self, Function.update_of_ne (by decide), e15, hz,
      Proof.X25519.sqn_pw]
    conv => lhs; arg 2; rw [← Proof.X25519.pw_one (env s.mem b 2)]
    rw [Proof.X25519.pw_mul, root_exp, Proof.X25519.pow_pw]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [e3, Function.update_of_ne h15, e2, Function.update_of_ne h15, ek i hi]

/-- The slots `recoverInitOps` computes from `y` in slot 1. -/
theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧ evalOps recoverInitOps e 6 = rootU (e 1) ∧
      evalOps recoverInitOps e 7 = rootV (e 1) ∧
      evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
      evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, (Proof.Ed25519.pow_three _ : _ = _), ?_⟩
  rw [← Proof.Ed25519.pow_seven]
  rfl

theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧ evalOps recoverFinishOps e 6 = e 6 ∧
      evalOps recoverFinishOps e 7 = e 7 ∧ evalOps recoverFinishOps e 1 = e 1 ∧
      evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
      evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The candidate**, for `y` in slot 1. -/
theorem recoverCandidate_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverCandidate s fun t => Keep b s t ∧
      env t.mem b 0 = rootX (env s.mem b 1) ∧ env t.mem b 1 = env s.mem b 1 ∧
      env t.mem b 6 = rootU (env s.mem b 1) ∧ env t.mem b 7 = rootV (env s.mem b 1) ∧
      env t.mem b 11 = rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) ∧
      env t.mem b 12 = 0 - rootU (env s.mem b 1) := by
  unfold recoverCandidate
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  obtain ⟨a1, au, av, av3, a2⟩ := recoverInit_eval (env s.mem b)
  rw [← e1] at a1 au av av3 a2
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (rootPower_ok hc1) fun s2 ⟨k2, e15, ek⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  refine WP.mono (fieldCode_ok _ hc2.ctx hc2.ws) fun t ⟨k3, e3⟩ => ?_
  obtain ⟨f0, f6, f7, f1, f11, f12⟩ := recoverFinish_eval (env s2.mem b)
  rw [← e3] at f0 f6 f7 f1 f11 f12
  have bx : env s2.mem b 6 * env s2.mem b 9 * env s2.mem b 15 = rootX (env s.mem b 1) := by
    rw [ek 6 (by decide), ek 9 (by decide), e15, a2, au, av3]
    rfl
  refine ⟨k1.trans (k2.trans k3), by rw [f0, bx], by rw [f1, ek 1 (by decide), a1], ?_, ?_, ?_, ?_⟩
  · rw [f6, ek 6 (by decide), au]
  · rw [f7, ek 7 (by decide), av]
  · rw [f11, bx, ek 7 (by decide), av]
  · rw [f12, ek 6 (by decide), au]

end

end VG.Proof.Ed25519.RISCV64

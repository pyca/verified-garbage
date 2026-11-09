module

import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.X25519.RISCV64.Cswap
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.RISCV64.PointMul
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field

/-!
# Ed25519 on RISCV64: selecting a point back by a mask

The accumulator saved in slots 17–20 restored (`env_restorePoint`), and a
slot replaced by another's value under a mask (`cswapSlot_ok`, `sel_V`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519
open VG.Impl.X25519.RISCV64 (cswap)

section
variable {b : Addr}

theorem env_restorePoint (e : Env) : point (evalOps restorePointOps e) 0 1 2 3 = point e 17 18 19 20 ∧
    point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 ∧ evalOps restorePointOps e 16 = e 16 ∧
    point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem sel_V {m m' : Mem} {a c : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 8, limb m' b a j = sel sw (limb m b a j) (limb m b c j)) :
    V m' b a = sel sw (V m b a) (V m b c) := by
  unfold V
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · exact val32_congr fun j hj => by rw [h j hj]; rfl
  · exact val32_congr fun j hj => by rw [h j hj]; rfl

theorem sel_toFe {sw : Nat} {x y : Nat} : Proof.X25519.toFe (sel sw x y) = sel sw (Proof.X25519.toFe x) (Proof.X25519.toFe y) := by
  unfold sel; split <;> rfl

/-- A conditional swap of two slots, by the mask `0 - sw` in `t0`. -/
theorem cswapSlot_ok {s : State} (hc : Ctx8 b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw)
    (a c : Slot) (hac : a ≠ c) :
    WP isa (.block (cswap (offset a) (offset c))) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ Frame [FA b] s.mem t.mem ∧
      env t.mem b a = sel sw (env s.mem b a) (env s.mem b c) ∧ env t.mem b c = sel sw (env s.mem b c) (env s.mem b a) ∧
      ∀ i : Slot, i ≠ a → i ≠ c → env t.mem b i = env s.mem b i := by
  have ha := slot_range a
  have hc' := slot_range c
  have hsep : offset a + 32 ≤ offset c ∨ offset c + 32 ≤ offset a := by
    have : a.val ≠ c.val := fun e => hac (Fin.ext e)
    simp only [offset]; omega_arith
  refine WP.mono (cswap_ok (by omega_arith) (by omega_arith) hsep (by simp only [offset]; omega)
    (by simp only [offset]; omega) hc.ctx hsw h11) fun t ht => ⟨ht.rest, ?_, ?_, ?_, fun i hia hic => ?_⟩
  · refine ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by omega_arith) (by omega_arith)
    · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · unfold env FS; rw [sel_V hsw ht.lx, sel_toFe]
  · unfold env FS; rw [sel_V hsw ht.ly, sel_toFe]
  · have hi := slot_range i
    have h1 : i.val ≠ a.val := fun e => hia (Fin.ext e)
    have h2 : i.val ≠ c.val := fun e => hic (Fin.ext e)
    refine env_keep ht.frame i fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by simp only [offset] at *; omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by simp only [offset] at *; omega_arith) (by omega_arith) (by omega_arith)

end

end VG.Proof.Ed25519.RISCV64

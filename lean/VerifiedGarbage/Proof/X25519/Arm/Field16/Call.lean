import VerifiedGarbage.Proof.X25519.Arm.Field16.Fn
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Covers

/-!
# Calls of `vg_gf25519_r16_mul` on ARMv7

`mulCall_ok`: a call of the product (`mulCall`), from code whose working space
at `r0` has at least the function's 4096 bytes (`CtxN e`), as the inlined
product (`Proof/X25519/Arm/Mul.lean`, `mul_ok`) did: the offsets are moved
into `r1`–`r3` and the function runs on the first 4096 bytes (`WP.call`,
from `mulFn_ok`). It changes `r1`–`r3`, `r12` and `lr` (the call's), and
memory only at `o` and in the function's own working space.
-/

namespace VG.Proof.X25519.Arm.Field16

open VG VG.Arm VG.Impl.X25519.Arm.Field16 VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)

/-- The registers a call of the product changes. -/
abbrev callClob : List Reg := [.r1, .r2, .r3, .r12, .lr]

/-- The facts `mulFn_ok` proves, as a contract on the function's 4096 bytes. -/
def mulK (b : BitVec 32) (o x y : Nat) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨State.addr b, 4096⟩] ∧ Pre b o x y t
  post t t' := Rest [.r1, .r2, .r3, .r12] t t' ∧
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] t.mem t'.mem ∧
    Lim t'.mem (State.addr b) o ∧
    V t'.mem (State.addr b) o % P = V t.mem (State.addr b) x * V t.mem (State.addr b) y % P
  pub _ _ := True

theorem mulK_ok {b : BitVec 32} {o x y : Nat} (t : State) (h : (mulK b o x y).pre t) :
    ∃ tr t', Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧ (mulK b o x y).post t t' := by
  obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := mulFn_ok h.2.2
  exact ⟨tr, t', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hR, hF, hL, hV⟩

theorem movw_ofNat {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `[o] = [a] · [b]`, by a call of `vg_gf25519_r16_mul`. -/
theorem mulCall_ok {e : Nat} {b : BitVec 32} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC)
    (hy : y + 64 ≤ ACC) {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa (mulCall o x y) s fun t =>
      Rest callClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = V s.mem (State.addr b) x * V s.mem (State.addr b) y % P := by
  have hA : ACC = 1472 := rfl
  rw [mulCall, WP.seq_iff]
  refine wp_movw fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ => WP.block_nil ?_
  have k₃ : Rest [.r1, .r2, .r3] s s₃ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hc₃ : CtxN e b s₃ := hc.of_rest k₃ (by decide)
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s₃.callEntry.withRegions [] [⟨State.addr b, 4096⟩]).gpr q = s₃.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hcov : Covers [⟨State.addr b, 4096⟩] s₃.wr :=
    Covers.of_sub fun r hr => ⟨_, hc₃.wr, 0, by rw [List.mem_singleton.mp hr]; simp, by
      rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ 4096 + e; omega⟩
  refine WP.call (k := mulK b o x y) mulK_ok (rd := []) (wr := [⟨State.addr b, 4096⟩])
    ⟨rfl, rfl, ⟨⟨by rw [g _ (by decide)]; exact hc₃.r0, by have := hc.fit; omega,
        List.mem_singleton_self _⟩,
      by rw [g _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movw_ofNat (by omega)],
      by rw [g _ (by decide), u₃.other _ (by decide), u₂.gpr, movw_ofNat (by omega)],
      by rw [g _ (by decide), u₃.gpr, movw_ofNat (by omega)],
      ho, hx, hy, by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hlx,
      by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact hly⟩⟩
    (Covers.right hcov) hcov ?_ (by decide +kernel)
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hL, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₃] at hF hL hV
  refine ⟨⟨fun q hq => ?_, by rw [hrd, k₃.rd], by rw [hwr, k₃.wr], by rw [hsp, k₃.sp]⟩, hF, hL, hV⟩
  have hR' := hR.gpr q (by revert hq; cases q <;> decide)
  simp only [State.withRegions_gpr] at hR'
  rw [hR', State.callEntry_gpr _ (by revert hq; cases q <;> decide), k₃.gpr _ (by revert hq; cases q <;> decide)]

end VG.Proof.X25519.Arm.Field16

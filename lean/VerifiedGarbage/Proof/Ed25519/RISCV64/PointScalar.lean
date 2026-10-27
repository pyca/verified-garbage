module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointMul
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on RISC-V: the field area cleared, and `[S] P` from a scalar's pointer

`initFields_ok`: the slots cleared. `pointFromScalar_ok`: `d` into slot 16
and the product of the point of slots 0–3 by the `2 count` bytes at `s0`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

theorem initFields_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initFields) s fun t => Rest [.a4] s t ∧ Frame [FA b] s.mem t.mem := by
  unfold initFields
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (stores_ok (r := .a4) (o := 64) (n := 176) (by omega) (by omega)
    (hc.of_rest (u1.rest (ws := [.a4]) (by decide)) (by decide))) fun t ⟨_, h2, _, h4⟩ =>
      ⟨(u1.rest (by decide)).trans (h4.mono (by decide)), ?_⟩
  rw [← u1.mem]
  exact h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩

theorem env_const16 (e : Env) : point (evalOps [.const 16 Spec.Ed25519.d] e) 0 1 2 3 = point e 0 1 2 3 ∧
    evalOps [.const 16 Spec.Ed25519.d] e 16 = Spec.Ed25519.d := ⟨rfl, rfl⟩

/-- **`[S] P`** for the `2 count` bytes at `s0`. -/
theorem pointFromScalar_ok {s : State} (hc : Ctx8 b s) {count : Nat} (hc1 : 1 ≤ count) (hc32 : count ≤ 32)
    {p : Addr} (h14 : s.gpr .s0 = p) (hin : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * count⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa (pointFromScalar count) s fun t =>
      Rest (.s5 :: .a4 :: batchR) s t ∧ Frame (pmulW b) s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem p (2 * count))) (point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  unfold pointFromScalar
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have hc1' : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.s5]) (by decide)) (by decide)
  refine WP.seq (WP.mono (fieldCode_ok _ hc1'.ctx hc1'.ws) fun s2 ⟨k2, e2⟩ => ?_)
  obtain ⟨p2, d2⟩ := env_const16 (env s1.mem b)
  rw [← e2] at p2 d2
  have hc2 : Ctx8 b s2 := hc1'.of_keep k2
  have hb2 : bytesAt s2.mem p (2 * count) = bytesAt s.mem p (2 * count) := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    rw [← u1.mem]
    exact bytes_ws k2.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)) hpd
      (by omega) (List.mem_range.mp hi)
  refine WP.mono (pointMultiply_ok hc2 d2 (p := p) hc1 hc32
    (by rw [k2.rest.gpr _ (by decide), u1.gpr, h14])
    (fun i hi => by rw [k2.rest.rd, k2.rest.wr, u1.rd, u1.wr]; exact hin i hi) hpd) fun t ⟨rt, ft, pt, dt⟩ =>
      ⟨?_, ?_, ?_, dt⟩
  · exact (u1.rest (by decide)).trans ((k2.rest.mono (by decide)).trans (rt.mono (by decide)))
  · rw [← u1.mem]
    exact (k2.frame.mono (by simp)).trans ft
  · rw [pt, hb2, p2, u1.mem]

end

end VG.Proof.Ed25519.RISCV64

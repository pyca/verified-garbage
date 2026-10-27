module

import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.RISCV64.Pack
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarBit
import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Ed448 on RISCV64: `vg_ed448_scalar_reduce`

The function rounds `scratch` up to a multiple of 8 (Ed25519's `align_ok`,
the same two instructions), reduces the 114 bytes of `wide` into `SR`
(`engine_ok`), and writes `SR` to `out` as 57 bytes (`finish_ok`). It uses
only caller-saved registers.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)
open VG.Proof.Ed25519.RISCV64 (base base_sub)

theorem align_eq : Impl.X448.RISCV64.align = Impl.X25519.RISCV64.align := rfl

theorem SR_eq : SR = 0 := rfl

theorem rem_SR : Rem SR := ⟨by decide, by decide, by decide⟩

/-- A byte apart from `scratch` is in none of the rounded working space's parts. -/
theorem not_in_base {x q : Addr} {d n : Nat} (hd : d + n ≤ 2048)
    (h : ¬ (⟨q, 8192⟩ : Region).Contains x 1) : ¬ (⟨base q + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 :=
  fun hc => h (base_sub q hd x hc)

/-- The precondition, by register: `out` in `a0`, `wide` in `a1`, `scratch` in `a2`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 114⟩]
  wr : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩]
  out_wide : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a1, 114⟩
  out_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  wide_ws : (⟨s.gpr .a1, 114⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      bytesAt t.mem (s.gpr .a0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .a1) 114) := by
  have hS := SR_eq
  have hD := SD_eq
  have hws : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .a0, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .a1, 114⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  unfold scalarReduce scalarReduceSetup
  rw [align_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => WP.append
    (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a2) u1.gpr (by rw [u1.wr]; exact hws))
    fun s2 ⟨hc2, hr2, hm2⟩ => wp_mv fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a3, .t3] s s3 := (u1.rest (by decide)).trans ((hr2.mono (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, hm2, u1.mem]
  have hc3 : Ctx (base (s.gpr .a2)) s3 := hc2.of_rest (u3.rest (ws := [.t3]) (by decide)) (by decide)
  have e14 : s3.gpr .t3 = s.gpr .a1 := by
    rw [u3.gpr, hr2.gpr _ (by decide), u1.other _ (by decide)]
  have hwb : ∀ i < 114, ¬ (⟨s.gpr .a2, 8192⟩ : Region).Contains (s.gpr .a1 + BitVec.ofNat 64 i) 1 :=
    fun i hi => hp.wide_ws _ (Offset.contains_base _ (by omega) (by omega))
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 114) (by decide) (by decide) hc3 e14
    (fun i hi => by rw [hr3.rd, hr3.wr]; exact in_base (List.mem_append_left _ hwide) (by omega) (by omega))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact not_in_base (by omega) (hwb i hi))) fun s4 ⟨hr4, _, hv4⟩ => ?_)
  rw [hm3] at hv4
  refine WP.mono (finish_ok (hc3.of_rest hr4 (by decide)) (by rw [hr4.gpr _ (by decide), hr3.gpr _ (by decide)])
    (by rw [hr4.wr, hr3.wr]; exact hout) (hp.out_ws.sub_right (base_sub _ (by omega))))
    fun t ⟨_, _, hb⟩ => by rw [hb, hv4]; rfl

end VG.Proof.Ed448.RISCV64

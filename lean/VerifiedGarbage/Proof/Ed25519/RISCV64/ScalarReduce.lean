module

import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarCompare
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar

/-!
# `vg_ed25519_scalar_reduce` on RISC-V: correctness

The function rounds `scratch` up (`align_ok`), reduces the 64 bytes of `wide`
into `SR` (`engine_ok`), and copies `SR`'s words to `out` (`packField_ok`).
`SR`'s words are the scalar's 32 bytes, little-endian, so `out` holds
`scalarReduce wide` (`out_bytes`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (L decodeLE bytesAt)

/-- The precondition, by register: `out` in `a0`, `wide` in `a1`, `scratch` in `a2`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 64⟩]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a2, 8192⟩]
  out_wide : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a1, 64⟩
  out_ws : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  wide_ws : (⟨s.gpr .a1, 64⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩

/-- The copy of `SR` to `out` at `a0`, from the reduced remainder. -/
theorem finish_ok {B o : Addr} {s : State} (hc : Ctx B s) (h0 : s.gpr .a0 = o)
    (hout : (⟨o, 32⟩ : Region) ∈ s.wr) (hd : (⟨o, 32⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 SR, 32⟩)
    {x : Nat} (hv : V s.mem B SR = x) :
    WP isa (.block scalarFinish) s fun t => bytesAt t.mem o 32 = Spec.Ed25519.encodeLE 32 x := by
  have hS := SR_eq
  refine WP.mono (packField_ok hc (p := .a0) (by decide) h0 (a := SR) (dst := 0) (by omega) (by omega)
    (by decide) (fun k hk => in_base hout (by omega) (by omega)) (by rw [BitVec.add_zero]; exact hd))
    fun t ht => out_bytes (b := B) (a := SR) (fun j hj => by rw [← Nat.zero_add (4 * j)]; exact ht.outs j hj) hv

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .a1) 64) := by
  have hS := SR_eq
  have hws : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .a1, 64⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  unfold scalarReduce scalarReduceSetup
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => WP.append (align_ok (q := s.gpr .a2) u1.gpr (by rw [u1.wr]; exact hws))
    fun s2 ⟨hc2, hr2, hm2⟩ => wp_mv fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a3, .t3] s s3 := (u1.rest (by decide)).trans ((hr2.mono (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, hm2, u1.mem]
  have hc3 : Ctx (base (s.gpr .a2)) s3 := hc2.of_rest (u3.rest (ws := [.t3]) (by decide)) (by decide)
  have e14 : s3.gpr .t3 = s.gpr .a1 := by
    rw [u3.gpr, hr2.gpr _ (by decide), u1.other _ (by decide)]
  refine WP.seq (WP.mono (engine_ok hc3 e14
    (fun k hk => by rw [hr3.rd, hr3.wr]; exact in_base (List.mem_append_left _ hwide) (by omega) (by omega)))
    fun s4 ⟨hr4, _, hv4⟩ => ?_)
  rw [hm3] at hv4
  exact finish_ok (hc3.of_rest hr4 (by decide)) (by rw [hr4.gpr _ (by decide), hr3.gpr _ (by decide)])
    (by rw [hr4.wr, hr3.wr]; exact hout) (hp.out_ws.sub_right (base_sub _ (by omega))) hv4

end VG.Proof.Ed25519.RISCV64

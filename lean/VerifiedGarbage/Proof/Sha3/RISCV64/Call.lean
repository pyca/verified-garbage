module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Sha3.RISCV64.Permute
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-3 on RISC-V: calling the permutation

The streaming functions call `vg_keccak_f1600` (which allocates a frame of
its own, `WP.callAny`) on the state at `s2`, with the first 512 bytes of
their own frame, at the stack pointer, as its scratch space.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_sdepth : sdepth Impl.Sha3.RISCV64.permute = 608 := by decide +kernel

/-- Calling `vg_keccak_f1600` on the state at `a0`, with scratch space at
`a1`, the stack pointer: the callee-saved registers are kept, and memory
changes only in the state, the scratch space and the 608 bytes below. -/
theorem call_ok {s : State} {st : Addr} (h0 : s.gpr .a0 = st) (h1 : s.gpr .a1 = s.sp)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩, ⟨s.sp, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.sp := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callAny (k := Proof.Sha3.permuteRISCV64) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨s.sp, 512⟩]) ?_ ?_ hw ?_ (by rw [permute_sdepth]; decide)
  · simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1]
    exact ⟨trivial, trivial, d₁, hal, hsp, d₂,
      Offset.base_disjoint_below s.sp (n := 608) (k := 512) (by omega) |>.symm⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    rw [permute_sdepth] at hf
    exact hQ s' hrd hwr hsp' hcs (by simpa using hf) hpost

theorem preserved_a0_a1 : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 := by decide

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `s2`, with scratch
space at the stack pointer. -/
theorem permuteAt_ok {s : State} {st : Addr} (h1 : s.gpr .s2 = st)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩, ⟨s.sp, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAt s Q := by
  unfold permuteAt mov
  refine WP.seq (wp_mv fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have sp₂ : s₂.sp = s.sp := by rw [u₂.sp, u₁.sp]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine call_ok (st := st) (by rw [u₂.other _ (by decide), u₁.gpr, h1])
    (by rw [u₂.gpr, sp₂, u₁.sp]; exact BitVec.add_zero _) (by rw [sp₂]; exact hal)
    (by rw [sp₂]; exact hsp) (by rw [sp₂]; exact d₁) (by rw [sp₂]; exact d₂)
    (by rw [sp₂, u₂.wr, u₁.wr]; exact hw) fun s' rd' wr' sp' cs' f' e' => ?_
  refine hQ s' (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr]) (by rw [sp', sp₂])
    (fun r hr => ?_) (by rw [← hm, ← sp₂]; exact f') (by rw [e', hm])
  rw [cs' r hr, u₂.other _ (preserved_a0_a1 r hr).2, u₁.other _ (preserved_a0_a1 r hr).1]

end VG.Proof.Sha3.RISCV64

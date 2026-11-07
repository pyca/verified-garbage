module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Verified
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
meta import VerifiedGarbage.Impl.AesCtr.RISCV64
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Verified
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# `vg_aes_ctr32`'s work, in place, on RISC-V

As on PPC64LE (`Proof/AesCtr/PPC64LE/Call.lean`): `ctr_call`, counter mode
in place (`ctrCall`: `mv a6, a3`, then a call of `vg_aes_ctr32_to` with its
source the destination, so that one instance of the code serves every
caller) on `n` blocks at `D` from the counter block at `C`, with
working space `S`, from its contract (with `WP.call`): the blocks are then
counter mode's, the counter block is `n` further on, only `C`, `D` and `S`
change, and so do no callee-saved registers. `ctr_rel`: such calls, with
the same arguments in both runs, are constant time. A call (`jal`) stores
nothing in memory.
-/

@[expose] public section

namespace VG.Proof.AesCtr.RISCV64

open VG VG.RISCV64
open VG.Spec.Gcm (blocksAt blockAt ctr32 aesWith)
open VG.Spec.Aes (bytesAt)

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` with `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at
`S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = C
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 n
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem CtrCall.toNat_n {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    (BitVec.ofNat 64 n).toNat = n := by
  have := h.wrap
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The state after `mv a6, a3`, at the entry of `vg_aes_ctr32_to`, with its
source the destination: its precondition. -/
theorem CtrCall.pre {s s' : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n)
    (u : Steps.Upd s s' .a6 (s.gpr .a3)) :
    Proof.Aes.ctr32ToRISCV64.pre
      (s'.callEntry.withRegions [⟨K, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := h.toNat_n
  simp only [Proof.Aes.ctr32ToRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s' (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a5 ∉ linkRegs),
    State.callEntry_gpr s' (by decide : Reg.a6 ∉ linkRegs), u.gpr, u.other .a0 (by decide),
    u.other .a1 (by decide), u.other .a2 (by decide), u.other .a3 (by decide), u.other .a4 (by decide),
    u.other .a5 (by decide), h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.cd.symm, .inl trivial, h.ds, h.wrap, h.wrap,
    h.rounds⟩

/-- The regions `vg_aes_ctr32_to` is given are the caller's. -/
theorem CtrCall.reads' {s s' : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n)
    (u : Steps.Upd s s' .a6 (s.gpr .a3)) :
    Covers ([⟨K, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s'.rd ++ s'.wr) := by
  rw [u.rd, u.wr]
  refine (Covers.of_mem fun r hr => ?_).trans h.reads
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with (rfl | rfl) | rfl | rfl | rfl <;> simp

theorem ctr_call {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa Impl.AesCtr.RISCV64.ctrCall s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := h.toNat_n
  refine WP.seq (Steps.wp_mv fun s₁ u => WP.block_nil ?_)
  refine WP.call (k := Proof.Aes.ctr32ToRISCV64) Proof.Aes.RISCV64.ctr32To_correct
    (rd := [⟨K, 240⟩, ⟨D, 16 * n⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (h.pre u) (h.reads' u)
    (by rw [u.wr]; exact h.writes) ?_ Proof.Aes.RISCV64.ctr32To_noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s₁ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s₁ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s₁ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s₁ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s₁ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s₁ (by decide : Reg.a6 ∉ linkRegs),
    u.gpr, u.other .a0 (by decide), u.other .a1 (by decide), u.other .a2 (by decide), u.other .a3 (by decide),
    u.other .a4 (by decide), u.mem, h.a0, h.a1, h.a2, h.a3, h.a4, hR, hn] at hdata hctr
  refine ⟨by rw [hrd, u.rd], by rw [hwr, u.wr], by rw [hsp, u.sp], fun r hr => ?_, by rw [← u.mem]; exact hf,
    hdata, hctr⟩
  rw [hcs r hr, u.other r (by revert r; decide)]

/-- Calls of `vg_aes_ctr32`, with the same arguments in both runs, are
constant time. -/
theorem ctr_rel {P : State → State → Prop} {K C D S : Addr} {R n : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.AesCtr.RISCV64.ctrCall fun _ _ => True := by
  let F : State → State → Prop := fun σ s' => Steps.Upd σ s' .a6 (σ.gpr .a3)
  have hm : RelCT isa P (.block [.addi .a6 .a3 0]) fun s₁' s₂' => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁' ∧ F σ₂ s₂' :=
    RelCT.wpDep (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun s₁ s₂ hp => ⟨(h s₁ s₂ hp).2.2, fun r hr => by simp at hr⟩) (by taint_decide))
      fun s₁ s₂ _ => ⟨Steps.wp_mv fun _ u => WP.block_nil u, Steps.wp_mv fun _ u => WP.block_nil u⟩
  refine RelCT.seq hm (RelCT.call Proof.Aes.RISCV64.ctr32To_correct Proof.Aes.RISCV64.ctr32To_ct
    [⟨K, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] fun s₁ s₂ ⟨_, σ₁, σ₂, hp, u₁, u₂⟩ => ?_)
  obtain ⟨h₁, h₂, hsp⟩ := h σ₁ σ₂ hp
  refine ⟨h₁.pre u₁, h₂.pre u₂, ?_, h₁.reads' u₁, by rw [u₁.wr]; exact h₁.writes, h₂.reads' u₂,
    by rw [u₂.wr]; exact h₂.writes⟩
  simp only [Proof.Aes.ctr32ToRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a6 ∉ linkRegs), u₁.gpr, u₂.gpr, u₁.sp, u₂.sp,
    u₁.other .a0 (by decide), u₁.other .a1 (by decide), u₁.other .a2 (by decide), u₁.other .a3 (by decide),
    u₁.other .a4 (by decide), u₁.other .a5 (by decide), u₂.other .a0 (by decide), u₂.other .a1 (by decide),
    u₂.other .a2 (by decide), u₂.other .a3 (by decide), u₂.other .a4 (by decide), u₂.other .a5 (by decide),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCtr.RISCV64

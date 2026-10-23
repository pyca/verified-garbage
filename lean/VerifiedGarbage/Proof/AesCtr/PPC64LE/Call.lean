module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit

/-!
# A call of `vg_aes_ctr32` on PPC64LE

`ctr_call`: a call of `vg_aes_ctr32` on `n` blocks at `D` from the counter
block at `C`, with working space `S`, from its contract (with `WP.call`):
the blocks are then counter mode's, the counter block is `n` further on, only
`C`, `D` and `S` change, and so do no nonvolatile registers. `ctr_rel`: such
calls, with the same arguments in both runs, are constant time. A call
(`bl`) stores nothing in memory.
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Gcm (blocksAt blockAt ctr32 aesWith)
open VG.Spec.Aes (bytesAt)

theorem ctr32_noFrames : Impl.Aes.PPC64LE.ctr32.noFrames = true := by decide +kernel

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` with `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at
`S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
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

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem CtrCall.toNat_n {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    (BitVec.ofNat 64 n).toNat = n := by
  have := h.wrap
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32PPC64LE.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := h.toNat_n
  simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.wrap, h.rounds⟩

theorem ctr_call {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa Impl.AesCtr.PPC64LE.ctrCall s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := h.toNat_n
  refine WP.call (k := Proof.Aes.ctr32PPC64LE) Proof.Aes.PPC64LE.ctr32_correct
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_ ctr32_noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hn] at hdata hctr
  exact ⟨hrd, hwr, hsp, hcs, hf, hdata, hctr⟩

/-- Calls of `vg_aes_ctr32`, with the same arguments in both runs, are
constant time. -/
theorem ctr_rel {P : State → State → Prop} {K C D S : Addr} {R n : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.AesCtr.PPC64LE.ctrCall fun _ _ => True := by
  refine RelCT.call Proof.Aes.PPC64LE.ctr32_correct Proof.Aes.PPC64LE.ctr32_ct [⟨K, 240⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCtr.PPC64LE

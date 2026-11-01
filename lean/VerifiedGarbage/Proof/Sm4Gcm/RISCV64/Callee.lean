module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.Sm4.RISCV64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit

/-!
# SM4-GCM on RISC-V: the calls of SM4

Untrusted: everything here is checked by Lean. SM4-GCM calls
`vg_sm4_ctr32` and `vg_sm4_expand_key` by their contracts, as AES-GCM calls
AES's (`Proof/AesGcm/RISCV64/Callee.lean`): what the arguments in `a0`–`a3`
must be (`CtrCall`, `KeyCall`), and what the call leaves (`CtrPost`,
`KeyPost`): the callee's postcondition, memory changed only in the buffers
it writes and in its frame below the stack pointer (3232 and 3168 bytes),
and the callee-saved registers kept. `ctr_rel` and `key_rel`: such calls,
with the same public arguments in both runs, are constant time (and so
`CT.sctr`, `CT.skey`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64
open VG.Proof.AesGcm.RISCV64 (callEntry_gpr' toNat64)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 inc32)

/-! ## `vg_sm4_ctr32` -/

/-- `vg_sm4_ctr32`'s frame uses the 3232 bytes of stack its contract reserves. -/
theorem ctr32_sdepth : sdepth Impl.Sm4.RISCV64.ctr32 = 3232 := by lit_decide

/-- What a call of `vg_sm4_ctr32(schedule, counter, data, n)` needs. -/
structure CtrCall (s : State) (K C D : Addr) (n : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = C
  a2 : s.gpr .a2 = D
  a3 : s.gpr .a3 = BitVec.ofNat 64 n
  n_lt : n < 2 ^ 64
  kc : (⟨K, 128⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 128⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  fK : K.toNat + 128 ≤ 2 ^ 64
  fC : C.toNat + 16 ≤ 2 ^ 64
  fD : D.toNat + 16 * n ≤ 2 ^ 64
  spal : s.sp.toNat % 16 = 0
  spge : 3232 ≤ s.sp.toNat
  bk : (below s.sp 3232).Disjoint ⟨K, 128⟩
  bc : (below s.sp 3232).Disjoint ⟨C, 16⟩
  bd : (below s.sp 3232).Disjoint ⟨D, 16 * n⟩
  reads : Covers ([⟨K, 128⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩] s.wr

/-- What a call of `vg_sm4_ctr32` leaves. -/
structure CtrPost (s : State) (K C D : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, below s.sp 3232] s.mem s'.mem
  out : blocksAt s'.mem D n =
    ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem K)) (blockAt s.mem C) (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    (Proof.Sm4.RISCV64.Modes.modeContract Proof.Sm4.RISCV64.Modes.ctr32Post).pre
      (s.callEntry.withRegions [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  simp only [Proof.Sm4.RISCV64.Modes.modeContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, toNat64 h.n_lt]
  exact ⟨trivial, trivial, h.kc, h.kd, h.cd, h.fK, h.fC, h.fD, h.spal, h.spge, h.bk, h.bc, h.bd⟩

theorem ctr_call {name : String} {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    WP isa (.call name Impl.Sm4.RISCV64.ctr32) s (CtrPost s K C D n) := by
  refine WP.callAny (k := Proof.Sm4.RISCV64.Modes.modeContract Proof.Sm4.RISCV64.Modes.ctr32Post)
    Proof.Sm4.RISCV64.Modes.ctr32_correct (rd := [⟨K, 128⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.pre
    h.reads h.writes ?_ (by rw [ctr32_sdepth]; decide)
  intro s' hrd hwr hsp hf hcs hpost
  rw [ctr32_sdepth] at hf
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_, ?_⟩ <;>
  simp only [Proof.Sm4.RISCV64.Modes.modeContract, Proof.Sm4.RISCV64.Modes.ctr32Post,
    State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, toNat64 h.n_lt] at hpost
  exacts [hpost.1, hpost.2]

/-- Calls of `vg_sm4_ctr32` with the same arguments in both runs are constant time. -/
theorem ctr_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D n, CtrCall s₁ K C D n ∧ CtrCall s₂ K C D n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Sm4.RISCV64.ctr32) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Nat) (s₁ s₂ : State) =>
      CtrCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ CtrCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, D, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, C, D, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, D, n⟩ := x
  refine RelCT.call Proof.Sm4.RISCV64.Modes.ctr32_correct (Proof.Sm4.RISCV64.ctr32_constantTime _)
    [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Sm4.RISCV64.Modes.modeContract, Proof.Sm4.RISCV64.modePub, State.withRegions_gpr,
    State.withRegions_sp, State.callEntry_sp, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_sm4_expand_key` -/

/-- `vg_sm4_expand_key`, in its frame. -/
abbrev keyCode : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey

theorem key_sdepth : sdepth keyCode = 3168 := by lit_decide

/-- What a call of `vg_sm4_expand_key(key, schedule)` needs. -/
structure KeyCall (s : State) (K C : Addr) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = C
  kc : (⟨K, 16⟩ : Region).Disjoint ⟨C, 128⟩
  fK : K.toNat + 16 ≤ 2 ^ 64
  fC : C.toNat + 128 ≤ 2 ^ 64
  spal : s.sp.toNat % 16 = 0
  spge : 3168 ≤ s.sp.toNat
  bk : (below s.sp 3168).Disjoint ⟨K, 16⟩
  bc : (below s.sp 3168).Disjoint ⟨C, 128⟩
  reads : Covers ([⟨K, 16⟩] ++ [⟨C, 128⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 128⟩] s.wr

/-- What a call of `vg_sm4_expand_key` leaves. -/
structure KeyPost (s : State) (K C : Addr) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 128⟩, below s.sp 3168] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem C = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K)

theorem KeyCall.pre {s : State} {K C : Addr} (h : KeyCall s K C) :
    (Spec.Sm4.expandKeyContract RISCV64.abi 3168).pre (s.callEntry.withRegions [⟨K, 16⟩] [⟨C, 128⟩]) := by
  have g0 := callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs)
  have g1 := callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs)
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, RISCV64.abi, RISCV64.argRegs, List.getD,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    g0, g1, h.a0, h.a1]
  simp only [h.a0, h.a1]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | exact h.kc
    | exact h.fK
    | exact h.fC
    | exact h.spal
    | exact h.spge
    | exact h.bk
    | exact h.bc
    | exact h.kc.symm
    | exact h.bk.symm
    | exact h.bc.symm
    | omega

theorem key_call {name : String} {s : State} {K C : Addr} (h : KeyCall s K C) :
    WP isa (.call name keyCode) s (KeyPost s K C) := by
  refine WP.callAny (k := Spec.Sm4.expandKeyContract RISCV64.abi 3168) Proof.Sm4.RISCV64.expandKey_framed.1
    (rd := [⟨K, 16⟩]) (wr := [⟨C, 128⟩]) h.pre h.reads h.writes ?_ (by rw [key_sdepth]; decide)
  intro s' hrd hwr hsp hf hcs hpost
  rw [key_sdepth] at hf
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  sig_post [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, RISCV64.abi, RISCV64.argRegs] at hpost
  simp only [h.a0, h.a1] at hpost
  exact hpost

/-- Calls of `vg_sm4_expand_key` with the same arguments in both runs are
constant time. -/
theorem key_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C, KeyCall s₁ K C ∧ KeyCall s₂ K C ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name keyCode) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr) (s₁ s₂ : State) =>
      KeyCall s₁ x.1 x.2 ∧ KeyCall s₂ x.1 x.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, C), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C⟩ := x
  refine RelCT.call Proof.Sm4.RISCV64.expandKey_framed.1 Proof.Sm4.RISCV64.expandKey_framed.2.1
    [⟨K, 16⟩] [⟨C, 128⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  have e0 := callEntry_gpr' s₁ (by decide : Reg.a0 ∉ linkRegs)
  have e1 := callEntry_gpr' s₁ (by decide : Reg.a1 ∉ linkRegs)
  have f0 := callEntry_gpr' s₂ (by decide : Reg.a0 ∉ linkRegs)
  have f1 := callEntry_gpr' s₂ (by decide : Reg.a1 ∉ linkRegs)
  sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, RISCV64.abi, RISCV64.argRegs,
    State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, e0, e1, f0, f1, h₁.a0, h₁.a1, h₂.a0, h₂.a1,
    hsp]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial | exact h₁.a0.trans h₂.a0.symm |
    exact h₁.a1.trans h₂.a1.symm

/-- SM4's counter mode with the same arguments in both runs is constant time. -/
theorem CT.sctr {I : State → Prop} {name : String}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C D : Addr, ∃ n : Nat,
      CtrCall s₁ K C D n ∧ CtrCall s₂ K C D n ∧ s₁.sp = s₂.sp) :
    Proof.AesGcm.RISCV64.CT I (.call name Impl.Sm4.RISCV64.ctr32) :=
  ctr_rel fun _ _ hh => h _ _ hh.1 hh.2

/-- SM4's key expansion with the same arguments in both runs is constant time. -/
theorem CT.skey {I : State → Prop} {name : String}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C : Addr, KeyCall s₁ K C ∧ KeyCall s₂ K C ∧ s₁.sp = s₂.sp) :
    Proof.AesGcm.RISCV64.CT I (.call name keyCode) :=
  key_rel fun _ _ hh => h _ _ hh.1 hh.2

end VG.Proof.Sm4Gcm.RISCV64

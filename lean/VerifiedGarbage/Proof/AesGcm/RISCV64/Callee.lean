module

import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Verified
import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-!
# AES-GCM on RISC-V: the calls

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Callee.lean`): a call of `vg_ghash`, `vg_aes_ctr32`
or `vg_aes_expand_key_scratch` from its contract: what the arguments in
`a0`–`a5` must be (`GhCall`, `CtrCall`, `KeyCall`), and what the call leaves
(`GhPost`, `CtrPost`, `KeyPost`): the callee's postcondition, memory changed
only in the buffers it writes, and the callee-saved registers kept.
`vg_ghash` allocates a frame of 2048 bytes for its table (`WP.callAny`): its
call also needs those bytes below the stack pointer apart from its buffers,
and may change them. `gh_rel`, `ctr_rel` and `key_rel`: such calls, with the
same public arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 inc32 aesWith)

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-! ## `vg_ghash` -/

/-- `vg_ghash`'s frame uses the 2048 bytes of stack its contract reserves. -/
theorem ghash_sdepth : sdepth Impl.Gcm.RISCV64.ghash = 2048 := rfl

/-- What a call of `vg_ghash(h, y, data, n, scratch)` needs. -/
structure GhCall (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  a0 : s.gpr .a0 = H
  a1 : s.gpr .a1 = Y
  a2 : s.gpr .a2 = D
  a3 : s.gpr .a3 = BitVec.ofNat 64 n
  a4 : s.gpr .a4 = S
  n_lt : n < 2 ^ 64
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  kh : (below s.sp 2048).Disjoint ⟨H, 16⟩
  ky : (below s.sp 2048).Disjoint ⟨Y, 16⟩
  kd : (below s.sp 2048).Disjoint ⟨D, 16 * n⟩
  yfit : Y.toNat + 16 ≤ 2 ^ 64
  dfit : D.toNat + 16 * n ≤ 2 ^ 64
  spal : s.sp.toNat % 16 = 0
  spge : 2048 ≤ s.sp.toNat
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨S, 256⟩, below s.sp 2048] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n)

theorem GhCall.pre {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    Proof.Gcm.RISCV64.ghashX.pre
      (s.callEntry.withRegions [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  simp only [Proof.Gcm.RISCV64.ghashX, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a4 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, toNat64 h.n_lt]
  exact ⟨trivial, trivial, h.yd, h.kh, h.ky, h.kd, h.yfit, h.dfit, h.spal, h.spge⟩

theorem gh_call {name : String} {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa (.call name Impl.Gcm.RISCV64.ghash) s (GhPost s H Y D S n) := by
  refine WP.callAny (k := Proof.Gcm.RISCV64.ghashX) Proof.Gcm.RISCV64.ghash_correct
    (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) h.pre h.reads h.writes ?_
    (by rw [ghash_sdepth]; decide)
  intro s' hrd hwr hsp hf hcs hpost
  refine ⟨hrd, hwr, hsp, hcs, by rw [ghash_sdepth] at hf; exact hf, ?_⟩
  simp only [Proof.Gcm.RISCV64.ghashX, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, toNat64 h.n_lt] at hpost
  exact hpost

/-- Calls of `vg_ghash` with the same arguments in both runs are constant time. -/
theorem gh_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S n, GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Gcm.RISCV64.ghash) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat) (s₁ s₂ : State) =>
      GhCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧ GhCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧
        s₁.sp = s₂.sp) (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(H, Y, D, S, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨H, Y, D, S, n⟩ := x
  refine RelCT.call Proof.Gcm.RISCV64.ghash_correct Proof.Gcm.RISCV64.ghash_ct [⟨H, 16⟩, ⟨D, 16 * n⟩]
    [⟨Y, 16⟩, ⟨S, 256⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Gcm.RISCV64.ghashX, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a4 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32(schedule, rounds, counter, data, n, scratch)` needs. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = C
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 n
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n_lt : n < 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  fit : D.toNat + 16 * n ≤ 2 ^ 64
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : blocksAt s'.mem D n =
    ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C) (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32RISCV64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  simp only [Proof.Aes.ctr32RISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a5 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, toNat64 h.n_lt, toNat_rounds h.rounds]
  exact ⟨by trivial, by trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.fit, h.rounds⟩

theorem ctr_call {name : String} {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call name Impl.Aes.RISCV64.ctr32) s (CtrPost s K C D S R n) := by
  refine WP.call (k := Proof.Aes.ctr32RISCV64) Proof.Aes.RISCV64.ctr32_correct
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
    Proof.AesCtr.RISCV64.ctr32_noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_, ?_⟩ <;>
  simp only [Proof.Aes.ctr32RISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a4 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, toNat64 h.n_lt, toNat_rounds h.rounds] at hpost
  exacts [hpost.1, hpost.2]

/-- Calls of `vg_aes_ctr32` with the same arguments in both runs are constant time. -/
theorem ctr_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S R n, CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧
      s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Aes.RISCV64.ctr32) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat × Nat) (s₁ s₂ : State) =>
      CtrCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
        CtrCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, C, D, S, R, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, D, S, R, n⟩ := x
  refine RelCT.call Proof.Aes.RISCV64.ctr32_correct Proof.Aes.RISCV64.ctr32_ct [⟨K, 240⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32RISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a4 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a5 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

theorem expandKey_noFrames : Impl.Aes.RISCV64.expandKey.noFrames = true := by lit_decide

/-- What a call of `vg_aes_expand_key_scratch(key, key_len, schedule, scratch)` needs. -/
structure KeyCall (s : State) (K : Addr) (kl : Nat) (C S : Addr) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 kl
  a2 : s.gpr .a2 = C
  a3 : s.gpr .a3 = S
  kl_ok : kl = 16 ∨ kl = 24 ∨ kl = 32
  kc : (⟨K, kl⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨K, kl⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨K, kl⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure KeyPost (s : State) (K : Addr) (kl : Nat) (C S : Addr) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (kl / 4) + 1)) =
    Spec.Aes.expandKey (bytesAt s.mem K kl)

theorem toNat_kl {kl : Nat} (h : kl = 16 ∨ kl = 24 ∨ kl = 32) : (BitVec.ofNat 64 kl).toNat = kl := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem KeyCall.pre {s : State} {K : Addr} {kl : Nat} {C S : Addr} (h : KeyCall s K kl C S) :
    Proof.Aes.expandKeyRISCV64.pre (s.callEntry.withRegions [⟨K, kl⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, toNat_kl h.kl_ok]
  exact ⟨by trivial, by trivial, h.kc, h.ks, h.cs, h.kl_ok⟩

theorem key_call {name : String} {s : State} {K : Addr} {kl : Nat} {C S : Addr} (h : KeyCall s K kl C S) :
    WP isa (.call name Impl.Aes.RISCV64.expandKey) s (KeyPost s K kl C S) := by
  refine WP.call (k := Proof.Aes.expandKeyRISCV64) Proof.Aes.RISCV64.expandKey_correct
    (rd := [⟨K, kl⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩]) h.pre h.reads h.writes ?_ expandKey_noFrames
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, toNat_kl h.kl_ok] at hpost
  exact hpost

/-- Calls of `vg_aes_expand_key_scratch` with the same arguments in both runs
are constant time. -/
theorem key_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K kl C S, KeyCall s₁ K kl C S ∧ KeyCall s₂ K kl C S ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Aes.RISCV64.expandKey) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Nat × Addr × Addr) (s₁ s₂ : State) =>
      KeyCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ KeyCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, kl, C, S, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, kl, C, S), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, kl, C, S⟩ := x
  refine RelCT.call Proof.Aes.RISCV64.expandKey_correct Proof.Aes.RISCV64.expandKey_ct [⟨K, kl⟩]
    [⟨C, 240⟩, ⟨S, 512⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.a0 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a1 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.a2 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesGcm.RISCV64

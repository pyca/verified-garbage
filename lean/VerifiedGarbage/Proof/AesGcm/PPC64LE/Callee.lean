module

import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Gcm.PPC64LE
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-!
# AES-GCM on PPC64LE: the calls

Untrusted: everything here is checked by Lean. A call of `vg_ghash`,
`vg_aes_ctr32` or `vg_aes_expand_key_scratch` from its contract (with
`WP.call`): what the arguments in `r3`–`r8` must be (`GhCall`, `CtrCall`,
`KeyCall`), and what the call leaves (`GhPost`, `CtrPost`, `KeyPost`): the
callee's postcondition, memory changed only in the buffers it writes, and
the nonvolatile registers kept. `gh_rel`, `ctr_rel` and `key_rel`: such
calls, with the same public arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 inc32 aesWith)

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash(h, y, data, n, scratch)` needs. -/
structure GhCall (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = H
  r4 : s.gpr .r4 = Y
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 n
  r7 : s.gpr .r7 = S
  n_lt : n < 2 ^ 64
  hy : (⟨H, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  hs : (⟨H, 16⟩ : Region).Disjoint ⟨S, 256⟩
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ys : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 256⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 256⟩
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨S, 256⟩] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n)

theorem GhCall.pre {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    Proof.Gcm.ghashPPC64LE.pre (s.callEntry.withRegions [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  simp only [Proof.Gcm.ghashPPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, toNat64 h.n_lt]
  exact ⟨by trivial, by trivial, h.hy, h.hs, h.yd, h.ys, h.ds⟩

theorem gh_call [VG.Proof.Gcm.PPC64LE.GhashLaw] {name : String} {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa (.call name Impl.Gcm.PPC64LE.ghash) s (GhPost s H Y D S n) := by
  refine WP.call (k := Proof.Gcm.ghashPPC64LE) Proof.Gcm.PPC64LE.ghash_correct
    (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Gcm.ghashPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, toNat64 h.n_lt] at hpost
  exact hpost

/-- Calls of `vg_ghash` with the same arguments in both runs are constant time. -/
theorem gh_rel [VG.Proof.Gcm.PPC64LE.GhashLaw] {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S n, GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Gcm.PPC64LE.ghash) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat) (s₁ s₂ : State) =>
      GhCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧ GhCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ∧
        s₁.sp = s₂.sp) (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(H, Y, D, S, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨H, Y, D, S, n⟩ := x
  refine RelCT.call Proof.Gcm.PPC64LE.ghash_correct Proof.Gcm.PPC64LE.ghash_ct [⟨H, 16⟩, ⟨D, 16 * n⟩]
    [⟨Y, 16⟩, ⟨S, 256⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Gcm.ghashPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32(schedule, rounds, counter, data, n, scratch)` needs. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
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
    Proof.Aes.ctr32PPC64LE.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, toNat64 h.n_lt, toNat_rounds h.rounds]
  exact ⟨by trivial, by trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.fit, h.rounds⟩

theorem ctr_call {name : String} {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call name Impl.Aes.PPC64LE.ctr32) s (CtrPost s K C D S R n) := by
  refine WP.call (k := Proof.Aes.ctr32PPC64LE) Proof.Aes.PPC64LE.ctr32_correct
    (rd := [⟨K, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_, ?_⟩ <;>
  simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, toNat64 h.n_lt, toNat_rounds h.rounds] at hpost
  exacts [hpost.1, hpost.2]

/-- Calls of `vg_aes_ctr32` with the same arguments in both runs are constant time. -/
theorem ctr_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S R n, CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧
      s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Aes.PPC64LE.ctr32) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Addr × Addr × Addr × Nat × Nat) (s₁ s₂ : State) =>
      CtrCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧
        CtrCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, C, D, S, R, n), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, C, D, S, R, n⟩ := x
  refine RelCT.call Proof.Aes.PPC64LE.ctr32_correct Proof.Aes.PPC64LE.ctr32_ct [⟨K, 240⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch(key, key_len, schedule, scratch)` needs. -/
structure KeyCall (s : State) (K : Addr) (kl : Nat) (C S : Addr) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 kl
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = S
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
    Proof.Aes.expandKeyPPC64LE.pre (s.callEntry.withRegions [⟨K, kl⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, toNat_kl h.kl_ok]
  exact ⟨by trivial, by trivial, h.kc, h.ks, h.cs, h.kl_ok⟩

theorem key_call {name : String} {s : State} {K : Addr} {kl : Nat} {C S : Addr} (h : KeyCall s K kl C S) :
    WP isa (.call name Impl.Aes.PPC64LE.expandKey) s (KeyPost s K kl C S) := by
  refine WP.call (k := Proof.Aes.expandKeyPPC64LE) Proof.Aes.PPC64LE.expandKey_correct
    (rd := [⟨K, kl⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), h.r3, h.r4, h.r5, toNat_kl h.kl_ok] at hpost
  exact hpost

/-- Calls of `vg_aes_expand_key_scratch` with the same arguments in both runs
are constant time. -/
theorem key_rel {name : String} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K kl C S, KeyCall s₁ K kl C S ∧ KeyCall s₂ K kl C S ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name Impl.Aes.PPC64LE.expandKey) fun _ _ => True := by
  refine RelCT.exists_ (P := fun (x : Addr × Nat × Addr × Addr) (s₁ s₂ : State) =>
      KeyCall s₁ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ KeyCall s₂ x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ s₁.sp = s₂.sp)
      (fun x => ?_) |>.mono (fun s₁ s₂ hp => by
      obtain ⟨K, kl, C, S, h₁, h₂, hsp⟩ := h s₁ s₂ hp
      exact ⟨(K, kl, C, S), h₁, h₂, hsp⟩) fun _ _ h => h
  obtain ⟨K, kl, C, S⟩ := x
  refine RelCT.call Proof.Aes.PPC64LE.expandKey_correct Proof.Aes.PPC64LE.expandKey_ct [⟨K, kl⟩]
    [⟨C, 240⟩, ⟨S, 512⟩] fun s₁ s₂ ⟨h₁, h₂, hsp⟩ => ?_
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₂.r3, h₂.r4, h₂.r5, h₂.r6, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesGcm.PPC64LE

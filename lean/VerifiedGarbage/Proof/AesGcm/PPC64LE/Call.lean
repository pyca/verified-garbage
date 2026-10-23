module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Aes.PPC64LE.Ctr32
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM on PPC64LE: the calls

Untrusted: everything here is checked by Lean. A call of `vg_ghash`
(`gh_call`), `vg_aes_ctr32` (`ctr_call`) or `vg_aes_expand_key_scratch`
(`ek_call`), from its contract (`WP.call`): what it computes, that it
changes memory only in the buffers it writes, and that it keeps the
permissions, the stack pointer and the nonvolatile registers (`CallKeep`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-- What a call keeps, writing only within `wr`. -/
structure CallKeep (s s' : State) (ws : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame ws s.mem s'.mem
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  Nat.mod_eq_of_lt h

/-- What a call of `vg_ghash` needs. -/
structure GhPre (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = H
  r4 : s.gpr .r4 = Y
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 n
  r7 : s.gpr .r7 = S
  lt : 16 * n < 2 ^ 64
  hy : (⟨H, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  hs : (⟨H, 16⟩ : Region).Disjoint ⟨S, 256⟩
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ys : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 256⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 256⟩
  wrap : S.toNat + 256 ≤ 2 ^ 64
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

theorem gh_call {s : State} {H Y D S : Addr} {n : Nat} (h : GhPre s H Y D S n) :
    WP isa ghCall s fun s' => CallKeep s s' [⟨Y, 16⟩, ⟨S, 256⟩] ∧
      blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt (by have := h.lt; omega)
  refine WP.call (k := Proof.Gcm.ghashPPC64LE) Proof.Gcm.PPC64LE.ghash_correct
    (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩]) (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) ?_ h.reads h.writes ?_
  · simp only [Proof.Gcm.ghashPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
      h.r3, h.r4, h.r5, h.r6, h.r7, hn]
    exact ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, h.wrap⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine ⟨⟨hrd, hwr, hsp, hf, hcs⟩, ?_⟩
    simp only [Proof.Gcm.ghashPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, hn] at hpost
    exact hpost

/-- What a call of `vg_aes_ctr32` needs. -/
structure CtrPre (s : State) (C : Addr) (R : Nat) (Cb D S : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = C
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = Cb
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  lt : 16 * n < 2 ^ 64
  cc : (⟨C, 240⟩ : Region).Disjoint ⟨Cb, 16⟩
  cd : (⟨C, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  bd : (⟨Cb, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  bs : (⟨Cb, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  reads : Covers ([⟨C, 240⟩] ++ [⟨Cb, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Cb, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  toNat_ofNat_lt (by omega)

theorem ctr_call {s : State} {C : Addr} {R : Nat} {Cb D S : Addr} {n : Nat} (h : CtrPre s C R Cb D S n) :
    WP isa ctrCall s fun s' => CallKeep s s' [⟨Cb, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] ∧
      blocksAt s'.mem D n =
        ctr32 (aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))) (blockAt s.mem Cb) (blocksAt s.mem D n) ∧
      blockAt s'.mem Cb = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem Cb) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := toNat_ofNat_lt (by have := h.lt; omega)
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.ctr32PPC64LE) Proof.Aes.PPC64LE.ctr32_correct
    (rd := [⟨C, 240⟩]) (wr := [⟨Cb, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) ?_ h.reads h.writes ?_ (by lit_decide)
  · simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, hn, hR]
    exact ⟨trivial, trivial, h.cc, h.cd, h.cs, h.bd, h.bs, h.ds, h.wrap, h.rounds⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine ⟨⟨hrd, hwr, hsp, hf, hcs⟩, ?_⟩
    simp only [Proof.Aes.ctr32PPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
      h.r3, h.r4, h.r5, h.r6, h.r7, hn, hR] at hpost
    exact hpost

/-- What a call of `vg_aes_expand_key_scratch` needs. -/
structure EkPre (s : State) (K : Addr) (L : Nat) (C S : Addr) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 L
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  kc : (⟨K, L⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨K, L⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

theorem ek_call {s : State} {K : Addr} {L : Nat} {C S : Addr} (h : EkPre s K L C S) :
    WP isa ekCall s fun s' => CallKeep s s' [⟨C, 240⟩, ⟨S, 512⟩] ∧
      Spec.Aes.bytesAt s'.mem C (16 * (Spec.Aes.rounds (L / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem K L) := by
  have hL : (BitVec.ofNat 64 L).toNat = L := toNat_ofNat_lt (by rcases h.len with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyPPC64LE) Proof.Aes.PPC64LE.expandKey_correct
    (rd := [⟨K, L⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩]) ?_ h.reads h.writes ?_ (by lit_decide)
  · simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, hL]
    exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.len⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine ⟨⟨hrd, hwr, hsp, hf, hcs⟩, ?_⟩
    simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
      h.r3, h.r4, h.r5, hL] at hpost
    exact hpost

end VG.Proof.AesGcm.PPC64LE

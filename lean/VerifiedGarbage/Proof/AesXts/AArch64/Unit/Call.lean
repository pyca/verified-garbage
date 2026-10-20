module
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.Spec

import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.Framework.Contract

/-!
# XTS-AES of data units on AArch64: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false) for an implementation of the block functions, on `N` blocks
at `D`, from the tweak at `T`, with working space `S`, from its contract
(`WP.call`): the blocks are then XTS of them, the tweak the one after them,
and only the tweak, the blocks and `S` change. `xts_rel`: such calls, with
the same arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64
open VG.Proof.AesCbc.AArch64 (modeAArch64 toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = T
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = BitVec.ofNat 64 N
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 60
  wt : (⟨W, 240⟩ : Region).Disjoint ⟨T, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  td : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16 * N⟩
  ts : (⟨T, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ds : (⟨D, 16 * N⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapT : T.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * N ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : Addr) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modeAArch64 (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modeAArch64 (AesXts.xtsMode enc)) ok (rd := [⟨W, 240⟩])
    (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [modeAArch64, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4, hR, hN,
    Proof.AesXts.Unit.length_blocksAt] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost.1, hpost.2⟩

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre (modeAArch64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes⟩
  simp only [modeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    AesCbc.AArch64.callEntry_x0, AesCbc.AArch64.callEntry_x1, AesCbc.AArch64.callEntry_x2,
    AesCbc.AArch64.callEntry_x3, AesCbc.AArch64.callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.AArch64.Unit

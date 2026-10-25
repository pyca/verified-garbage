module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Contract

/-!
# XTS-AES of data units on RISC-V: a call of a whole-block function

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Call.lean`): `xts_call`, a call of
`vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc` true or false) on `N`
blocks at `D`, from the tweak at `T`, with working space `S`, from its
contract (`WP.call`): the blocks are then XTS of them, the tweak the one
after them, and only the tweak, the blocks and `S` change. `xts_rel`: such
calls, with the same arguments in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64
open VG.Proof.AesCbc.RISCV64 (modeRISCV64 toNat_rounds)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : Addr) (N R : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = T
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 N
  a5 : s.gpr .a5 = S
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
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem D N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem W (16 * (R + 1)))) (bytesAt s.mem T 16)
      (Spec.Cbc.blocksAt s.mem D N)
  tw : bytesAt s'.mem T 16 = Spec.Xts.next (bytesAt s.mem T 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 60) : (BitVec.ofNat 64 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ce0 (s : State) : s.callEntry.gpr .a0 = s.gpr .a0 := s.callEntry_gpr (by decide)
theorem ce1 (s : State) : s.callEntry.gpr .a1 = s.gpr .a1 := s.callEntry_gpr (by decide)
theorem ce2 (s : State) : s.callEntry.gpr .a2 = s.gpr .a2 := s.callEntry_gpr (by decide)
theorem ce3 (s : State) : s.callEntry.gpr .a3 = s.gpr .a3 := s.callEntry_gpr (by decide)
theorem ce4 (s : State) : s.callEntry.gpr .a4 = s.gpr .a4 := s.callEntry_gpr (by decide)
theorem ce5 (s : State) : s.callEntry.gpr .a5 = s.gpr .a5 := s.callEntry_gpr (by decide)

/-- The whole-block function's precondition, on entry to a call with the
regions it is given. -/
theorem XPre.mode_pre {enc : Bool} {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    (modeRISCV64 (AesXts.xtsMode enc)).pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce0, ce1, ce2, ce3, ce4, ce5, h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hN]
  exact ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, h.wrapT, h.wrapD, h.wrapS, h.rounds⟩

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s')
    (nf : c.noFrames = true)
    {s : State} {W T D S : Addr} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.call n c) s (XPost enc s W T D S N R) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_n h.n
  refine WP.call (k := modeRISCV64 (AesXts.xtsMode enc)) ok (rd := [⟨W, 240⟩])
    (wr := [⟨T, 16⟩, ⟨D, 16 * N⟩, ⟨S, 2176⟩]) h.mode_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [modeRISCV64, AesXts.xtsMode, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce0, ce1, ce2, ce3, ce4, h.a0, h.a1, h.a2, h.a3, h.a4, hR, hN,
    Proof.AesXts.Unit.length_blocksAt] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost.1, hpost.2⟩

/-- Calls of a whole-block function, with the same arguments in both runs,
are constant time. -/
theorem xts_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeRISCV64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeRISCV64 (AesXts.xtsMode enc)).pre (modeRISCV64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, T, D, S, N, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.mode_pre (enc := enc), h₂.mode_pre (enc := enc), ?_, h₁.reads, h₁.writes, h₂.reads,
    h₂.writes⟩
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    ce0, ce1, ce2, ce3, ce4, ce5, h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3,
    h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.RISCV64.Unit

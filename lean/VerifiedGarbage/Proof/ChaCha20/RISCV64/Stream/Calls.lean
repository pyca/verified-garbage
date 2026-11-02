module

import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Bytes
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Spec.ChaCha20

/-!
# Streaming ChaCha20 on RISC-V: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of `vg_chacha20_xor`, from their proofs of
correctness (with `WP.call`). A call stores nothing in memory, so the callee
changes memory only within the regions it may write.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64.Stream

open VG VG.RISCV64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

/-- `s'` differs from `s` only in memory within `rs`, and in registers that
are not callee-saved. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- An 8-byte aligned pointer plus a multiple of 4 is 4-byte aligned. -/
theorem al4_of_al8 {p : Addr} (h : p.toNat % 8 = 0) {d : Nat} (hd : d % 4 = 0) :
    (p + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

theorem block_call {s : State} {S B : Addr} (ha0 : s.gpr .a0 = S) (ha1 : s.gpr .a1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩) (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockRISCV64) Proof.ChaCha20.RISCV64.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ Proof.ChaCha20.RISCV64.Xor.block_noFrames
  · simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), ha0, ha1]
    exact ⟨trivial, trivial, hdj, hSa, hBa⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), ha0, ha1] using hpost

theorem xor_noFrames : Impl.ChaCha20.RISCV64.Xor.xor.noFrames = true := by decide +kernel

theorem xor_call {s : State} {S D B : Addr} {n : Nat}
    (ha0 : s.gpr .a0 = S) (ha1 : s.gpr .a1 = D)
    (ha2 : s.gpr .a2 = BitVec.ofNat 64 n) (ha3 : s.gpr .a3 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.call (k := Proof.ChaCha20.xorRISCV64) Proof.ChaCha20.RISCV64.Xor.xor_correct
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ xor_noFrames
  · simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.a3 ∉ linkRegs), ha0, ha1, ha2, ha3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hwrap, hSa, hBa⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.a0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.a1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.a2 ∉ linkRegs),
      ha0, ha1, ha2, hn'] using hpost

end VG.Proof.ChaCha20.RISCV64.Stream

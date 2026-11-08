module

public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Stream.Bytes
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Contract
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Xor

/-!
# Streaming ChaCha20 on PPC64LE: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of `vg_chacha20_xor`, from their proofs of
correctness (with `WP.call`). A call stores nothing in memory, so the callee
changes memory only within the regions it may write.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE.Stream

open VG VG.PPC64LE
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

/-- `s'` differs from `s` only in memory within `rs`, in registers that are
not callee-saved, and in the link register. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem block_call {s : State} {S B : Addr} (hr3 : s.gpr .r3 = S) (hr4 : s.gpr .r4 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockPPC64LE) Proof.ChaCha20.PPC64LE.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ Proof.ChaCha20.PPC64LE.Xor.block_noFrames
  · simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), hr3, hr4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), hr3, hr4] using hpost

/-- `vg_chacha20_xor` in place (`Vmx4.xor_call`). -/
theorem xor_call {s : State} {S D B : Addr} {n : Nat}
    (hr3 : s.gpr .r3 = S) (hr4 : s.gpr .r4 = D)
    (hr5 : s.gpr .r5 = BitVec.ofNat 64 n) (hr6 : s.gpr .r6 = B) (hr7 : s.gpr .r7 = D) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Vmx4.xor) s Q :=
  Vmx4.xor_call hr3 hr4 hr5 hr6 hr7 hn hSD hSB hDB hwrap hc hw
    fun s' hrd hwr hsp hf hcs _ hpost => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

end VG.Proof.ChaCha20.PPC64LE.Stream

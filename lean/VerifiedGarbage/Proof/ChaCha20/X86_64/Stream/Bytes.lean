module
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming ChaCha20 on x86-64: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `rdx`
bytes at `rsi` into those at `r14` (`XorBuf.xorBuf_ok`), and moves past them.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  r14 : s.gpr .r14 = D
  rsi : s.gpr .rsi = K
  rdx : s.gpr .rdx = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : InRegions s.wr D c
  rK : InRegions (s.rd ++ s.wr) K c
  sep : (⟨D, c⟩ : Region).Disjoint ⟨K, c⟩

/-- What `xorBytes` leaves: the bytes XORed, `r14` past them and `r15`
less their number; only `rax`, `r8`, `rcx`, `r14`, `r15` and the flags are
written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  r14 : s'.gpr .r14 = D + BitVec.ofNat 64 c
  r15 : s'.gpr .r15 = s.gpr .r15 - BitVec.ofNat 64 c
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) = s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

theorem xorBytes_eq : xorBytes =
    .seq (Impl.ChaCha20.X86_64.XorBuf.xorBuf .r14 .rsi)
      (.block [.alu .add .r14 (.reg .rdx), .alu .sub .r15 (.reg .rdx)]) :=
  rfl

set_option simprocs false in
theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.c_lt
  rw [xorBytes_eq]
  refine WP.seq (WP.mono (XorBuf.xorBuf_ok (by decide) (by decide) hp.r14 hp.rsi hp.rdx (by omega)
    hp.sep hp.wD hp.rK) fun s₂ h₂ => ?_)
  have hrdx : s₂.gpr .rdx = BitVec.ofNat 64 c := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.rdx]
  have hr14 : s₂.gpr .r14 = D := by rw [h₂.keep _ (by decide) (by decide) (by decide), hp.r14]
  have hr15 : s₂.gpr .r15 = s.gpr .r15 := h₂.keep _ (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_false, hrdx, hr14, hr15]
  refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    fun r e₁ e₂ e₃ e₄ e₅ => ?_, h₂.rd, h₂.wr, h₂.data, h₂.frame⟩
  simp only [e₄, e₅, ite_false]; exact h₂.keep r e₁ e₂ e₃

end VG.Proof.ChaCha20.X86_64.Stream

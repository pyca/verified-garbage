module

import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Step
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-! # A pair of verified native binary steps advances the fixed GCD schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Gcd64

def arrays : List Nat := [0, 1, 4, 5, aT1, aT2, aT3]
def slots : List Nat := [sOdd, sB, sC]

structure LoopState (s₀ : State) (base : Addr) (size count i : Nat) (s : State) : Prop where
  workspace : Ws s base size 2 count
  frame : Keep base 2 arrays slots s₀.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 (64 - i)
  value : (num s.mem base 2 0, num s.mem base 2 1) =
    VG.Proof.RsaKeyGen.gcdIter (2 * i) (num s₀.mem base 2 0) (num s₀.mem base 2 1)

theorem body_ok {s₀ s : State} {base : Addr} {size count i : Nat} (space : 15 ≤ count)
    (S : LoopState s₀ base size count i s) (index : i < 64) :
    WP isa body s fun t => LoopState s₀ base size count (i + 1) t ∧ t.zf = some (decide (i + 1 = 64)) := by
  unfold body
  refine WP.seq (WP.mono (bankStep_ok S.workspace space (Or.inl ⟨rfl, rfl⟩))
    fun a ⟨Wa, Fa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (bankStep_ok Wa space (Or.inr ⟨rfl, rfl⟩))
    fun b ⟨Wb, Fb, Vb, Kb⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok b) fun t ⟨counter, Z, M, K⟩ => ?_
  have beforeCount : b.gpr .esi = s.gpr .esi := (Kb.1 .esi (by decide)).trans (Ka.1 .esi (by decide))
  have A₀ := congrArg Prod.fst S.value
  have A₁ := congrArg Prod.snd S.value
  dsimp only [Prod.fst, Prod.snd] at A₀ A₁
  rw [A₀, A₁, ← VG.Proof.RsaKeyGen.gcdIter_succ'] at Va
  have V₀ := congrArg Prod.fst Va
  have V₁ := congrArg Prod.snd Va
  dsimp only [Prod.fst, Prod.snd] at V₀ V₁
  rw [V₀, V₁, ← VG.Proof.RsaKeyGen.gcdIter_succ'] at Vb
  refine ⟨⟨Wb.rest K (by decide) (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [M]
    exact (S.frame.trans (Fa.mono (by decide) (by decide))).trans (Fb.mono (by decide) (by decide))
  · exact S.rest.trans (((Ka.mono (by decide)).trans (Kb.mono (by decide))).widen K)
  · rw [counter, beforeCount, S.counter]
    change BitVec.ofNat 32 (64 - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [M, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    exact Vb
  · rw [Z, beforeCount, S.counter]
    change some (BitVec.ofNat 32 (64 - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 64 - i - 1 = 0 ↔ i + 1 = 64 by omega]

end VG.Proof.RsaKeyGen.X86.Gcd64

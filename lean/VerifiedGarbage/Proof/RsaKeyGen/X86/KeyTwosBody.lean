module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyHalveStep
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToDual

/-! # One public iteration of the native RSA LCM halving schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

structure HalveLoop (s₀ : State) (B : Addr) (Z n i : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  frame : Keep B n halveArrays [kFlag] s₀.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 (32 * n - i)
  value : triple s.mem B n = VG.Proof.RsaKeyGen.halveIter i (triple s₀.mem B n)

theorem twoStep_ok {s₀ s : State} {B : Addr} {Z n i : Nat}
    (H : HalveLoop s₀ B Z n i s) (index : i < 32 * n) :
    WP isa (twoStep n) s fun t => HalveLoop s₀ B Z n (i + 1) t ∧
      t.zf = some (decide (i + 1 = 32 * n)) := by
  have bound : 32 * n < 2 ^ 32 := by have := H.workspace.wle; omega
  unfold twoStep
  refine WP.seq (WP.mono (halveStep_ok H.workspace) fun u ⟨hu, Ou, value, Ku⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok u) fun t ⟨counter, Zf, memory, Kt⟩ => ?_
  have before : u.gpr .esi = s.gpr .esi := Ku.1 _ (by decide)
  rw [H.value, ← VG.Proof.RsaKeyGen.halveIter_succ'] at value
  refine ⟨⟨hu.rest Kt, ?_, H.rest.trans ((Ku.mono (by decide)).widen Kt), ?_, ?_⟩, ?_⟩
  · rw [memory]
    exact H.frame.trans Ou
  · rw [counter, before, H.counter]
    change BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [memory]
    exact value
  · rw [Zf, before, H.counter]
    change some (BitVec.ofNat 32 (32 * n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * n - i - 1 = 0 ↔ i + 1 = 32 * n by omega]

end VG.Proof.RsaKeyGen.X86.Key

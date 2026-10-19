module

public import VerifiedGarbage.Proof.Dsa.AArch64.MinusCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.Modulus
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Framework.Block

/-! # Constant-time construction of p-minus-one and q-minus-two -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReadyMinusPublic (side : ModulusSide) (amount d : Nat) where
  layout : ExecutionLayout
  enough : amount ≤ side.value layout
  outputStart : activeBytes ≤ d
  outputEnd : d + side.length layout ≤ usedBytes

def ReadyMinusPublic.call {side : ModulusSide} {amount d : Nat} (p : ReadyMinusPublic side amount d) : MinusPublic amount where
  x := ⟨p.layout.base, activeBytes, side.offset, outerWords, side.words p.layout⟩
  ptr := off p.layout.base d
  len := side.length p.layout
  minv := side.inverse p.layout
  modulus := side.value p.layout
  lower := (side.bounds p.layout).1
  upper := by
    change side.words p.layout < 2 ^ 31
    have h : side.words p.layout ≤ 48 := (side.bounds p.layout).2.1
    omega
  enough := p.enough

theorem minusCallHead_ok {side : ModulusSide} {amount d : Nat} {p : ReadyMinusPublic side amount d}
    {s : State} (hd31 : d < 2 ^ 16) (hr : Ready p.layout s) :
    WP isa (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) s
      (MinusPre p.call) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds p.layout
  have h256 : 256 ≤ slot outerWords 8 := by decide
  have hactive : activeBytes ≤ 2 ^ 64 := by decide
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hr.parent (by decide) ⟨.local d, side.lengthField⟩ hd31 (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun u ⟨hgu, hup, hul, _, hfu, hku⟩ => ?_
  have child := call_ready (hr.child side) hfu (by decide) (by decide) (by omega) (by omega)
  refine WP.mono (enter_ok hgu child.header hlo hhi ho) fun t ⟨hct, hm, hkt⟩ => ?_
  have hk : Keep coreRegs s t := (hku.trans hkt).mono (by decide)
  refine ⟨hct, ⟨hct.good, hm ▸ child.modulus, hm ▸ child.inverse⟩,
    ⟨⟨side.inverse p.layout, hct, ?_, ?_⟩, hk1, hk31, rfl, ?_, hr.local_out p.outputStart p.outputEnd⟩⟩
  · change word t.mem p.layout.base (8 * result) = off p.layout.base d
    rw [hm]
    exact hup
  · change word t.mem p.layout.base (8 * resultLen) = BitVec.ofNat 64 (side.length p.layout)
    rw [hm]
    exact hul.trans (hr.length side)
  · intro j hj
    rw [hk.wr]
    exact hr.local_write p.outputEnd j hj

theorem readyMinus_ct (side : ModulusSide) (amount d : Nat)
    (ha : amount < 2 ^ 16) (hd31 : d < 2 ^ 16)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) (minusRest amount) h₂).isSome = true) :
    RelCT isa (Two fun p : ReadyMinusPublic side amount d => Ready p.layout)
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  unfold Checks.modulusMinus
  refine RelCT.seq (two_piece (Ψ := fun p s => MinusPre p.call s) [.x0]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.parent.x0)) ht₁ (fun _ _ h => minusCallHead_ok hd31 h)) ?_
  exact (two_map ReadyMinusPublic.call (fun _ _ h => h) (minusFinish_ct amount ha ht₂))

end VG.Proof.Dsa.AArch64

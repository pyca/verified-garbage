module

public import VerifiedGarbage.Proof.Dsa.X86_64.MinusCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time construction of p-minus-one and q-minus-two -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    {s : State} (hd31 : d < 2 ^ 31) (hr : Ready p.layout s) :
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
    rw [hk.2.2]
    exact hr.local_write p.outputEnd j hj

theorem readyMinus_ct (side : ModulusSide) (amount d : Nat)
    (ha : amount < 2 ^ 31) (hd31 : d < 2 ^ 31)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++ Core.enter side.offset)) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.r12, .rsi, .rbx]) (.block
      [.mov .rax (.mem (at0 .rsi)), .alu .sub .rax (.imm (BitVec.ofNat 32 amount)),
        .store (at0 .rbx) .rax, cfToRbp]) h₂).isSome = true) :
    RelCT isa (Two fun p : ReadyMinusPublic side amount d => Ready p.layout)
      (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block ((Core.operand result resultLen ⟨.local d, side.lengthField⟩ ++
    Core.enter side.offset) ++ minusHead amount)) (.seq (wordLoop 1 minusTail) (seqs Core.finish))) _
  apply fuseBlocks_ct
  refine RelCT.seq (two_piece (Ψ := fun p s => MinusPre p.call s) [.rdi]
    (pins_of (fun p _ => p.layout.base) (by
      intro p s h r hr
      obtain rfl := List.mem_singleton.mp hr
      exact h.parent.rdi)) ht₁ (fun _ _ h => minusCallHead_ok hd31 h)) ?_
  exact RelCT.assoc (two_map ReadyMinusPublic.call (fun _ _ h => h) (minusFinish_ct amount ha ht₂))

end VG.Proof.Dsa.X86_64

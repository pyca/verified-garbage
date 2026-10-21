module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A pair of native carry chains shifts one candidate bit into a 64-bit remainder -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

def incoming (x : BitVec 32) : Bool := decide (2 ^ 32 ≤ x.toNat + x.toNat)
def pair (low high : BitVec 32) : Nat := low.toNat + 2 ^ 32 * high.toNat

theorem shift_ok (s : State) :
    WP isa (.block shift) s fun t =>
      t.gpr .esi = s.gpr .esi + s.gpr .esi ∧
      (∃ carry : Bool, t.gpr .ebp = (if carry then BitVec.allOnes 32 else 0) ∧
        pair (t.gpr .ecx) (t.gpr .ebx) + 2 ^ 64 * carry.toNat =
          2 * pair (s.gpr .ecx) (s.gpr .ebx) + (incoming (s.gpr .esi)).toNat) ∧
      t.mem = s.mem ∧ Keeps [.esi, .ecx, .ebx, .ebp] s t := by
  unfold shift
  refine wp_addS rfl fun a A cfA => wp_adcS rfl cfA fun b B cfB => wp_adcS rfl cfB fun c C cfC => ?_
  refine wp_sbb_self cfC fun t T => WP.block_nil ?_
  let input := incoming (s.gpr .esi)
  let lowCarry := decide (2 ^ 32 ≤ (a.gpr .ecx).toNat + (a.gpr .ecx).toNat + input.toNat)
  let highCarry := decide (2 ^ 32 ≤ (b.gpr .ebx).toNat + (b.gpr .ebx).toNat + lowCarry.toNat)
  have lo := adc_rel (a.gpr .ecx) (a.gpr .ecx) input
  have hi : (c.gpr .ebx).toNat + 2 ^ 32 * highCarry.toNat =
      (b.gpr .ebx).toNat + (b.gpr .ebx).toNat + lowCarry.toNat := by
    rw [C.gpr]
    exact adc_rel (b.gpr .ebx) (b.gpr .ebx) lowCarry
  dsimp only [input, incoming] at lo
  rw [← B.gpr] at lo
  change (b.gpr .ecx).toNat + 2 ^ 32 * lowCarry.toNat =
    (a.gpr .ecx).toNat + (a.gpr .ecx).toNat + input.toNat at lo
  rw [A.other .ecx (by decide)] at lo
  rw [B.other .ebx (by decide), A.other .ebx (by decide)] at hi
  refine ⟨?_, ⟨highCarry, T.gpr, ?_⟩, T.mem.trans (C.mem.trans (B.mem.trans A.mem)),
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen T.keeps⟩
  · rw [T.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.gpr]
  · rw [T.other .ecx (by decide), T.other .ebx (by decide), C.other .ecx (by decide)]
    change (b.gpr .ecx).toNat + 2 ^ 32 * (c.gpr .ebx).toNat + 2 ^ 64 * highCarry.toNat = _
    unfold pair
    dsimp only [input] at lo
    omega

end VG.Proof.RsaKeyGen.X86.Mod64

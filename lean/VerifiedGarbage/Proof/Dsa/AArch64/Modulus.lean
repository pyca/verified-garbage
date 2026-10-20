module

public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
import VerifiedGarbage.Proof.Dsa.Layout

/-! # Selecting one of the two reusable DSA arithmetic moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

inductive ModulusSide where | p | q

def ModulusSide.offset : ModulusSide → Nat | .p => pWorkspace | .q => qWorkspace
def ModulusSide.lengthField : ModulusSide → Field | .p => .pLen | .q => .qLen
def ModulusSide.length (side : ModulusSide) (L : ExecutionLayout) : Nat := match side with | .p => L.pLen | .q => L.qLen
def ModulusSide.words (side : ModulusSide) (L : ExecutionLayout) : Nat := (side.length L + 7) / 8
def ModulusSide.value (side : ModulusSide) (L : ExecutionLayout) : Nat := match side with | .p => L.modulus | .q => L.subgroup
def ModulusSide.inverse (side : ModulusSide) (L : ExecutionLayout) : BitVec 64 := match side with | .p => L.pInverse | .q => L.qInverse

theorem ModulusSide.bounds (side : ModulusSide) (L : ExecutionLayout) :
    2 ≤ side.words L ∧ side.words L ≤ outerWords ∧
    slot outerWords 8 ≤ side.offset ∧ side.offset < 2 ^ 16 ∧
    side.offset + slot (side.words L) 8 + tabBytes (side.words L) ≤ activeBytes ∧
    1 ≤ side.length L ∧ side.length L < 2 ^ 31 := by
  obtain ⟨hp2, hp48, hq2, hq48, hpLo, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hl : 1 ≤ L.pLen ∧ L.pLen < 2 ^ 31 ∧ 1 ≤ L.qLen ∧ L.qLen < 2 ^ 31 := by
    rcases L.lengths with ⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  cases side
  · exact ⟨hp2, hp48, hpLo, by decide, Nat.le_trans hpHi hqa, hl.1, hl.2.1⟩
  · exact ⟨hq2, hq48, by decide, by decide, hqHi, hl.2.2.1, hl.2.2.2⟩

theorem Ready.child {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide) :
    ChildReady s.mem L.base side.offset (side.words L) (side.value L) (side.inverse L) := by
  cases side
  · exact h.pChild
  · exact h.qChild

theorem Ready.length {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide) :
    word s.mem L.base side.lengthField.offset = BitVec.ofNat 64 (side.length L) := by
  cases side
  · exact (h.fields .pLen (by decide)).trans L.pLength
  · exact (h.fields .qLen (by decide)).trans L.qLength

theorem Ready.afterCall {L : ExecutionLayout} {s t : State} {d k : Nat} (side : ModulusSide)
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base side.offset (side.words L) (side.value L) (side.inverse L))
    (hf : CallFrame L.base side.offset (side.words L) (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  cases side
  · exact h.afterP hp hc hf hk hd hend
  · exact h.afterQ hp hc hf hk hd hend

end VG.Proof.Dsa.AArch64

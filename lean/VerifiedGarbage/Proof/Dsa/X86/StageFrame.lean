module
public import VerifiedGarbage.Proof.Dsa.X86.RunFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand

/-! # Uniform frames for calls in the DSA signing and verification schedules -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure StageFrame (base : Addr) (s t : State) (output len : Nat) : Prop where
  keeps : Keeps powerClob s t
  mem : StackOuts base (s.gpr .esp) [(0, contextBytes 48), (output, len)] s.mem t.mem

theorem StageFrame.of_frame {base : Addr} {s t : State} {output len n : Nat} {rs : List Reg}
    (K : Keeps rs s t) (hk : ∀ r ∈ rs, r ∈ powerClob)
    (O : Outs base [(0, contextBytes n), (output, len)] s.mem t.mem) (hn : n ≤ 48) :
    StageFrame base s t output len := by
  refine ⟨K.mono hk, StackOuts.of_outs ?_⟩
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  intro x hx
  apply O x
  intro pair hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · have H := hx (0, contextBytes 48) (by simp)
    change ofs base x < 0 ∨ 7048 ≤ ofs base x at H
    omega
  · exact hx _ (by simp)

theorem StageFrame.of_stackFrame {base : Addr} {s t : State} {output len n : Nat} {rs : List Reg}
    (K : Keeps rs s t) (hk : ∀ r ∈ rs, r ∈ powerClob)
    (O : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem) (hn : n ≤ 48) :
    StageFrame base s t output len := by
  refine ⟨K.mono hk, O.mono ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨(0, contextBytes 48), by simp, Nat.le_refl _, by
      have H := VG.Proof.Dsa.X86.Layout.context_bound hn
      simp only [contextBytes, slot, stride] at H ⊢
      omega⟩
  · exact ⟨(output, len), by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem StageFrame.scr {base : Addr} {s t : State} {output len size : Nat}
    (F : StageFrame base s t output len) (hs : Scr s base size) : Scr t base size :=
  hs.of_keeps F.keeps (by decide)

theorem StageFrame.run {base : Addr} {s t : State} {output len : Nat}
    (F : StageFrame base s t output len)
    (ho : (r ≤ output ∧ output + len ≤ usedBytes) ∨ (output = Layout.field .mask ∧ len = 4)) :
    StackOuts base (s.gpr .esp) runRanges s.mem t.mem := by
  intro x hx hs
  apply F.mem x ?_ hs
  intro pair hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact hx _ (by simp [runRanges])
  · rcases ho with ⟨lo, hi⟩ | ⟨rfl, rfl⟩
    · have H := hx (r, usedBytes - r) (by simp [runRanges])
      have E : r + (usedBytes - r) = usedBytes := by decide
      simp only [E] at H
      omega
    · exact hx _ (by simp [runRanges])

theorem StageFrame.local_bytes {base : Addr} {s t : State} {output len d count : Nat}
    (F : StageFrame base s t output len) (hd : contextBytes 48 ≤ d) (hb : d + count ≤ usedBytes)
    (ho : output + len ≤ 2 ^ 64) (hsep : d + count ≤ output ∨ output + len ≤ d) :
    Spec.Rsa.bytesAt t.mem (off base d) count = Spec.Rsa.bytesAt s.mem (off base d) count := by
  apply stackOuts_bytes F.mem (by change d + count ≤ 15712 at hb; omega)
  · intro x hx
    left
    have H := Offset.lt_iff x base (show d + count ≤ 2 ^ 64 by change d + count ≤ 15712 at hb; omega)
    change (x - off base d).toNat + 1 ≤ count at hx
    change (x - off base d).toNat < count ↔ d ≤ ofs base x ∧ ofs base x < d + count at H
    omega
  · intro pair hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · decide
    · exact ho
  · intro pair hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa only [off, BitVec.add_zero] using Offset.disjoint_base base hd (by change d + count ≤ 15712 at hb; omega)
    · exact Offset.disjoint base hsep (by change d + count ≤ 15712 at hb; omega) ho

structure StageResult (base : Addr) (s t : State) (output len value : Nat) : Prop extends StageFrame base s t output len where
  bytes : Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len value

theorem StageResult.value {base : Addr} {s t : State} {output len value : Nat}
    (R : StageResult base s t output len value) (hv : value < 256 ^ len) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off base output) len) = value := by
  rw [R.bytes, VG.Proof.Dsa.decodeBE_encodeBE hv]

end VG.Proof.Dsa.X86

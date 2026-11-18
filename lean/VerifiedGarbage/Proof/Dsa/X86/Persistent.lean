module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Layout
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame

/-! ### `Dsa.X86.StageValues`, which this module and modules that import it used -/

section

/-! # Reading stage outputs and retaining other persistent intermediates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem StageResult.local_value {base : Addr} {s t : State} {size output len value : Nat}
    (R : StageResult base s t output len value) (hs : Scr s base size)
    (hl : 0 < len) (hb : output + len ≤ size) (hv : value < 256 ^ len) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local output)).setWidth 64) len) = value := by
  rw [local_pointer (R.toStageFrame.scr hs) hl hb]
  exact R.value hv

theorem StageFrame.local_value_keep {base : Addr} {s t : State} {size output len d count : Nat}
    (F : StageFrame base s t output len) (hs : Scr s base size) (hc : 0 < count)
    (hd : contextBytes 48 ≤ d) (hb : d + count ≤ size) (ho : output + len ≤ size) (hused : d + count ≤ VG.Impl.Dsa.Layout.usedBytes)
    (hsep : d + count ≤ output ∨ output + len ≤ d) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem ((pointerValue base t (.local d)).setWidth 64) count) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.local d)).setWidth 64) count) := by
  rw [local_pointer (F.scr hs) hc hb, local_pointer hs hc hb,
    F.local_bytes hd hused (by have := hs.nowrap; omega_using [ho, this]) hsep]

/-- A value in the working space lies apart from the stack its calls use. -/
theorem localStack {s : State} {base : Addr} {size offset len : Nat}
    (hs : Scr s base size) (room : Pow.Room (s.gpr .esp) base size) (hlen : 0 < len) (hb : offset + len ≤ size) :
    Region.Disjoint ⟨(pointerValue base s (.local offset)).setWidth 64, len⟩ (callStack (s.gpr .esp)) := by
  rw [local_pointer hs hlen hb]
  have nw := hs.nowrap
  have R := room
  unfold Pow.Room at R
  have e₁ : (off base offset).toNat = base.toNat + offset := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hb, nw]
  have e₂ : (BitVec.setWidth 64 (s.gpr .esp - 108#32)).toNat = (s.gpr .esp).toNat - 108 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega_using [R]
  apply Region.disjoint_of_le
  · simp only [callStack, e₁, e₂]; omega_using [hb, R]
  · simp only [e₁]; omega_using [hb, nw]
  · simp only [callStack, e₂]; omega_using []

theorem localStream {s : State} {base : Addr} {size offset len n : Nat}
    (hs : Scr s base size) (hlen : 0 < len) (hb : offset + len ≤ size) (hfar : contextBytes n ≤ offset) :
    StreamInput s base (contextBytes n) (pointerValue base s (.local offset)) len := by
  have R := localReady hs hlen hb hfar
  have ptr := local_pointer hs hlen hb
  refine ⟨R.fits, ?_, ?_, ?_⟩
  · intro i hi
    rw [ptr]
    change InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact hs.read (by omega_using [hb, hi])
  · intro i hi
    rw [ptr, ofs_off base (by have := hs.nowrap; omega_using [hb, hi, this])]
    omega_using [hfar]
  · rw [ptr]
    exact hs.read hb

end VG.Proof.Dsa.X86

end

end

/-! # Persistent scalar and group-element buffers in the DSA schedule -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem Moduli.scalarFit {base : Addr} {size pLen qLen p q d : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.scalars) : d + qLen ≤ usedBytes := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have L := M.lengths
  have T : VG.Impl.Dsa.Layout.t ≤ usedBytes := by decide
  omega_using [H, L, T]

theorem Moduli.wideFit {base : Addr} {size pLen qLen p q d : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) : d + pLen ≤ usedBytes := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have L := M.lengths
  omega_using [H, L]

theorem Moduli.scalarReady {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.scalars) (hn : n ≤ 48) :
    OperandReady s base n (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localReady M.scr (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.scalarFit hd) M.extent) (by omega_using [H, C])

theorem Moduli.wideReady {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) (hn : n ≤ 48) :
    OperandReady s base n (.local d) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localReady M.scr (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.wideFit hd) M.extent) (by omega_using [H, C])

theorem Moduli.wideStream {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) (hn : n ≤ 48) :
    StreamInput s base (contextBytes n) (pointerValue base s (.local d)) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localStream M.scr (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.wideFit hd) M.extent) (by omega_using [H, C])

theorem Moduli.wideStack {base : Addr} {size pLen qLen p q d : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) :
    Region.Disjoint ⟨(pointerValue base s (.local d)).setWidth 64, pLen⟩ (callStack (s.gpr .esp)) :=
  localStack M.scr M.room (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.wideFit hd) M.extent)

theorem scalar_separate {a b len : Nat} (ha : a ∈ Layout.scalars) (hb : b ∈ Layout.scalars)
    (hab : a ≠ b) (hl : len ≤ 32) : a + len ≤ b ∨ b + len ≤ a := by
  simp only [Layout.scalars, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [r, s, VG.Impl.Dsa.Layout.inverse, u, v, z, qMinusTwo] at * <;> omega

theorem scalar_before_wide {a b len : Nat} (ha : a ∈ Layout.scalars) (hb : b ∈ Layout.wideValues)
    (hl : len ≤ 32) : a + len ≤ b := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds ha
  simp only [Layout.wideValues, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> simp only [VG.Impl.Dsa.Layout.t, t2] at * <;> omega_using [hl, H]

theorem StageFrame.scalar_keep {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output qLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) (ho : output ∈ Layout.scalars) (hne : d ≠ output) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega_using [H]
  exact F.local_value_keep M.scr (by have := M.lengths; omega_using [this]) low
    (Nat.le_trans (M.scalarFit hd) M.extent) (Nat.le_trans (M.scalarFit ho) M.extent) (M.scalarFit hd)
    (scalar_separate hd ho hne (by have := M.lengths; omega_using [this]))

theorem StageFrame.scalar_keep_wide {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output pLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) (ho : output ∈ Layout.wideValues) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega_using [H]
  exact F.local_value_keep M.scr (by have := M.lengths; omega_using [this]) low
    (Nat.le_trans (M.scalarFit hd) M.extent) (Nat.le_trans (M.wideFit ho) M.extent) (M.scalarFit hd)
    (.inl (scalar_before_wide hd ho (by have := M.lengths; omega_using [this])))

theorem StageResult.scalar_value {base : Addr} {size pLen qLen p q output value : Nat} {s t : State}
    (R : StageResult base s t output qLen value) (M : Moduli base size pLen qLen p q s)
    (ho : output ∈ Layout.scalars) (hv : value < 256 ^ qLen) :
    operandValue t base (.local output) qLen = value :=
  R.local_value M.scr (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.scalarFit ho) M.extent) hv

theorem StageResult.wide_value {base : Addr} {size pLen qLen p q output value : Nat} {s t : State}
    (R : StageResult base s t output pLen value) (M : Moduli base size pLen qLen p q s)
    (ho : output ∈ Layout.wideValues) (hv : value < 256 ^ pLen) :
    operandValue t base (.local output) pLen = value :=
  R.local_value M.scr (by have := M.lengths; omega_using [this]) (Nat.le_trans (M.wideFit ho) M.extent) hv

theorem StageFrame.wide_keep {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output pLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.wideValues) (ho : output ∈ Layout.wideValues) (hne : d ≠ output) :
    operandValue t base (.local d) pLen = operandValue s base (.local d) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega_using [H]
  apply F.local_value_keep M.scr (by have := M.lengths; omega_using [this]) low
    (Nat.le_trans (M.wideFit hd) M.extent) (Nat.le_trans (M.wideFit ho) M.extent) (M.wideFit hd)
  have L := M.lengths
  simp only [Layout.wideValues, List.mem_cons, List.not_mem_nil, or_false] at hd ho
  rcases hd with rfl | rfl <;> rcases ho with rfl | rfl <;>
    simp only [VG.Impl.Dsa.Layout.t, t2] at * <;> omega

end VG.Proof.Dsa.X86

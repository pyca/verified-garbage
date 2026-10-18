module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageValues

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
  omega

theorem Moduli.wideFit {base : Addr} {size pLen qLen p q d : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) : d + pLen ≤ usedBytes := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have L := M.lengths
  omega

theorem Moduli.scalarReady {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.scalars) (hn : n ≤ 48) :
    OperandReady s base n (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localReady M.scr (by have := M.lengths; omega) (Nat.le_trans (M.scalarFit hd) M.extent) (by omega)

theorem Moduli.wideReady {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) (hn : n ≤ 48) :
    OperandReady s base n (.local d) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localReady M.scr (by have := M.lengths; omega) (Nat.le_trans (M.wideFit hd) M.extent) (by omega)

theorem Moduli.wideStream {base : Addr} {size pLen qLen p q d n : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (hd : d ∈ Layout.wideValues) (hn : n ≤ 48) :
    StreamInput s base (contextBytes n) (pointerValue base s (.local d)) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have C := VG.Proof.Dsa.X86.Layout.context_bound hn
  exact localStream M.scr (by have := M.lengths; omega) (Nat.le_trans (M.wideFit hd) M.extent) (by omega)

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
  rcases hb with rfl | rfl <;> simp only [VG.Impl.Dsa.Layout.t, t2] at * <;> omega

theorem StageFrame.scalar_keep {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output qLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) (ho : output ∈ Layout.scalars) (hne : d ≠ output) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega
  exact F.local_value_keep M.scr (by have := M.lengths; omega) low
    (Nat.le_trans (M.scalarFit hd) M.extent) (Nat.le_trans (M.scalarFit ho) M.extent) (M.scalarFit hd)
    (scalar_separate hd ho hne (by have := M.lengths; omega))

theorem StageFrame.scalar_keep_wide {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output pLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) (ho : output ∈ Layout.wideValues) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega
  exact F.local_value_keep M.scr (by have := M.lengths; omega) low
    (Nat.le_trans (M.scalarFit hd) M.extent) (Nat.le_trans (M.wideFit ho) M.extent) (M.scalarFit hd)
    (.inl (scalar_before_wide hd ho (by have := M.lengths; omega)))

theorem StageResult.scalar_value {base : Addr} {size pLen qLen p q output value : Nat} {s t : State}
    (R : StageResult base s t output qLen value) (M : Moduli base size pLen qLen p q s)
    (ho : output ∈ Layout.scalars) (hv : value < 256 ^ qLen) :
    operandValue t base (.local output) qLen = value :=
  R.local_value M.scr (by have := M.lengths; omega) (Nat.le_trans (M.scalarFit ho) M.extent) hv

theorem StageResult.wide_value {base : Addr} {size pLen qLen p q output value : Nat} {s t : State}
    (R : StageResult base s t output pLen value) (M : Moduli base size pLen qLen p q s)
    (ho : output ∈ Layout.wideValues) (hv : value < 256 ^ pLen) :
    operandValue t base (.local output) pLen = value :=
  R.local_value M.scr (by have := M.lengths; omega) (Nat.le_trans (M.wideFit ho) M.extent) hv

theorem StageFrame.wide_keep {base : Addr} {size pLen qLen p q output d : Nat} {s t : State}
    (F : StageFrame base s t output pLen) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.wideValues) (ho : output ∈ Layout.wideValues) (hne : d ≠ output) :
    operandValue t base (.local d) pLen = operandValue s base (.local d) pLen := by
  have H := VG.Proof.Dsa.X86.Layout.wide_bounds hd
  have low : contextBytes 48 ≤ d := by change 7048 ≤ d; omega
  apply F.local_value_keep M.scr (by have := M.lengths; omega) low
    (Nat.le_trans (M.wideFit hd) M.extent) (Nat.le_trans (M.wideFit ho) M.extent) (M.wideFit hd)
  have L := M.lengths
  simp only [Layout.wideValues, List.mem_cons, List.not_mem_nil, or_false] at hd ho
  rcases hd with rfl | rfl <;> rcases ho with rfl | rfl <;>
    simp only [VG.Impl.Dsa.Layout.t, t2] at * <;> omega

end VG.Proof.Dsa.X86

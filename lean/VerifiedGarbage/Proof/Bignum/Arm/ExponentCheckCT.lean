module

import VerifiedGarbage.Proof.Bignum.Arm.ExponentScan
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentScan
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentByte
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Bignum.Arm.ExponentScanCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.ExponentState`, which only this module used -/

section

/-! ### `Bignum.Arm.ExponentByteCT`, which only this module used -/

section

/-! # The exponent scanner's saturation branch uses only the public prefix -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure ExponentByteInput (p : BitVec 32) (x : Nat) (s : State) : Prop where
  ptr : s.gpr .r1 = p
  low : s.gpr .r3 = BitVec.ofNat 32 (x % 2 ^ 32)
  high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh x)
  read : InRegions (s.rd ++ s.wr) (State.addr p) 1

theorem exponentByte_ct {p : BitVec 32} {x : Nat} :
    RelCT isa (fun s t => ExponentByteInput p x s ∧ ExponentByteInput p x t)
      exponentByte (fun _ _ => True) := by
  let P := ExponentByteInput p x
  let z := (((BitVec.ofNat 32 (exponentHigh x) <<< 8) +
    (BitVec.ofNat 32 (x % 2 ^ 32) >>> 24)) >>> 1) == 0
  have accum : RelCT isa (fun s t => P s ∧ P t) (.block exponentAccumulate) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block exponentAccumulate) s (fun t => t.z = z) := by
    refine WP.mono (exponentAccumulate_ok s (by rw [h.ptr]; simp) h.read) ?_
    rintro t ⟨_, _, zero, _, _⟩
    simpa only [h.low, h.high] using zero
  have branch : RelCT isa (fun s t => s.z = z ∧ t.z = z)
      (.ite .eq (.block []) (.block [.mov .r4 (.imm 2)])) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      change some s.z = some t.z
      rw [h.1, h.2]
    · exact RelCT.block_nil (fun _ _ _ => trivial)
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t _
      exact Taint.agree_ofRegs (by simp)
  have advance : RelCT isa (fun _ _ => True) (.block exponentAdvance) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact ((pair_posts accum wp).seq branch).seq advance

end VG.Proof.Bignum.Arm

end

end

/-! # The public buffer and prefix invariants of exponent validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

structure ExponentBuffer (ep : BitVec 32) (eb : List Byte) (s : State) : Prop where
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

structure ExponentState (ep : BitVec 32) (eb : List Byte) (j : Nat) (s : State) : Prop where
  buffer : ExponentBuffer ep eb s
  ptr : s.gpr .r1 = ep + BitVec.ofNat 32 j
  count : s.gpr .lr = BitVec.ofNat 32 (eb.length - j)
  low : s.gpr .r3 = BitVec.ofNat 32 (pre eb j % 2 ^ 32)
  high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh (pre eb j))

theorem ExponentState.input {s : State} {ep : BitVec 32} {eb : List Byte} {j : Nat}
    (h : ExponentState ep eb j s) (hj : j < eb.length) :
    ExponentByteInput (ep + BitVec.ofNat 32 j) (pre eb j) s := by
  refine ⟨h.ptr, h.low, h.high, ?_⟩
  rw [addr_add (by have := h.buffer.sourceFit; omega_using [hj, this])]
  exact CallLay.inRegions_sub h.buffer.read (by omega_using [hj]) (by have := h.buffer.countFit; omega_using [this])

theorem exponentState_step (s : State) {ep : BitVec 32} {eb : List Byte} {j : Nat}
    (h : ExponentState ep eb j s) (hj : j < eb.length) :
    WP isa exponentByte s fun t => ExponentState ep eb (j + 1) t ∧ t.z = decide (j + 1 = eb.length) := by
  have input := h.input hj
  have byte : s.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
    rw [addr_add (by have := h.buffer.sourceFit; omega_using [hj, this])]
    exact h.buffer.bytes j hj
  refine WP.mono (exponentByte_ok s (by omega_using [hj]) (by have := h.buffer.countFit; omega_using [this])
    h.ptr h.count input.read byte h.low h.high) ?_
  rintro t ⟨lo, hi, ptr, count, zero, mem, rest⟩
  have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [next] at lo hi
  refine ⟨⟨⟨h.buffer.countFit, h.buffer.sourceFit, ?_, ?_⟩, ?_, ?_, lo, hi⟩, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.buffer.read
  · rw [mem]; exact h.buffer.bytes
  · rw [ptr]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [count]; congr 1
  · rw [zero]; exact decide_eq_decide.mpr (by omega_using [])

theorem exponentInit_ready (s : State) {ep : BitVec 32} {eb : List Byte}
    (h : ExponentBuffer ep eb s) (ptr : s.gpr .r1 = ep) (count : s.gpr .lr = BitVec.ofNat 32 eb.length) :
    WP isa (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) s (ExponentState ep eb 0) := by
  refine wp_mov (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun t b => WP.block_nil ?_
  have rest : Rest [.r3, .r4] s t := (a.rest (by simp)).trans (b.rest (by simp))
  refine ⟨⟨h.countFit, h.sourceFit, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.read
  · rw [b.mem, a.mem]; exact h.bytes
  · simpa using (rest.gpr .r1 (by simp)).trans ptr
  · simpa using (rest.gpr .lr (by simp)).trans count
  · exact (b.other .r3 (by decide)).trans a.gpr
  · simpa [pre_zero, exponentHigh] using b.gpr

end VG.Proof.Bignum.Arm

end

end

/-! # Validation scans only public exponent bytes and public lengths -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem exponentLoop_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentState ep eb 0 s ∧ ExponentState ep eb 0 t)
      (.loop exponentByte .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb.length ∧ 0 < k ∧
    ExponentState ep eb j s ∧ ExponentState ep eb j t
  have step : ∀ k, RelCT isa (I k) exponentByte fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨j, jk, hk, hs, ht⟩ := h
    have hj : j < eb.length := by omega_using [jk, hk]
    have trace := (exponentByte_ct s t tr1 tr2 u v ⟨hs.input hj, ht.input hj⟩ e1 e2).1
    obtain ⟨_, _, run1, next1, zero1⟩ := exponentState_step s hs hj
    obtain ⟨_, _, run2, next2, zero2⟩ := exponentState_step t ht hj
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_ ) = some (!_ )
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ eb.length := by
        intro last
        change some (!_ ) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], next1, next2⟩
  exact (RelCT.loop I step eb.length).mono (fun _ _ h => ⟨0, by omega_using [], positive, h.1, h.2⟩) (fun _ _ h => h)

def ExponentInput (ep : BitVec 32) (eb : List Byte) (s : State) : Prop :=
  ExponentBuffer ep eb s ∧ s.gpr .r1 = ep ∧ s.gpr .lr = BitVec.ofNat 32 eb.length

theorem exponentScan_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      exponentScan (fun _ _ => True) := by
  have init : RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : ExponentInput ep eb s) :
      WP isa (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) s (ExponentState ep eb 0) :=
    exponentInit_ready s h.1 h.2.1 h.2.2
  exact (pair_posts init wp).seq (exponentLoop_ct positive)

end VG.Proof.Bignum.Arm

end

end

/-! # Public-exponent validation has no dependency on any secret memory -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem exponentTest_ct : RelCT isa
    (fun s t => s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4) exponentTest (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem exponentCheck_ct {ep : BitVec 32} {eb : List Byte} (positive : 0 < eb.length) :
    RelCT isa (fun s t => ExponentInput ep eb s ∧ ExponentInput ep eb t)
      exponentCheck (fun _ _ => True) := by
  let Q := fun s : State =>
    s.gpr .r3 = BitVec.ofNat 32 (Spec.Rsa.os2ip eb % 2 ^ 32) ∧
    s.gpr .r4 = BitVec.ofNat 32 (exponentHigh (Spec.Rsa.os2ip eb))
  have wp (s : State) (h : ExponentInput ep eb s) : WP isa exponentScan s Q := by
    refine WP.mono (exponentScan_ok s positive h.1.countFit h.1.sourceFit h.1.read h.1.bytes h.2.1 h.2.2) ?_
    rintro t ⟨lo, hi, _, _⟩
    exact ⟨lo, hi⟩
  exact (pair_posts (exponentScan_ct positive) wp).seq
    (exponentTest_ct.mono (fun _ _ h => ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm

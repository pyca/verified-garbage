module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Arithmetic adapters for the generator-two exponent loop

The numerical adapters use the existing Montgomery and doubling results.
The square action can be a shared call: only its arithmetic result, memory
frame, and persistent calling conditions are needed by the exponent loop.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

def twice : Prog isa := VG.Impl.Bignum.Arm.TwoExp.candidate

theorem twiceArgs_ready (s : State) {base : BitVec 32} {len w M E : Nat}
    (h : Power base len w M E s) :
    WP isa (.block (montOpArgs 1 5 6)) s (DoubleFnReady base len w 1 5 6) := by
  refine WP.mono (montOpArgs_ok s (o := 1) (a := 5) (b := 6) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨po, pa, pb, mem, rest⟩
  have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ready.ptr)
  refine ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, po, pa, pb, ready.inverse, ?_⟩, ?_⟩
  · rw [mem, h.modulus]; exact h.bound
  · rw [mem]; exact h.two_low

theorem header_of_keeps {base : BitVec 32} {len w o : Nat} {s t : State}
    (ready : ArithmeticReady base len w s) (keeps : Keeps (State.addr base) len w o s.mem t.mem) :
    HeaderKept base s t := by
  have fit : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  intro d hd
  exact keeps_header_readW keeps size (d := d) (bits := 32) (by omega)

theorem square_value {base : BitVec 32} {len w M E : Nat} {s t : State}
    (h : Power base len w M E s) (ready : ArithmeticReady base len w t)
    (modulus : numAt t.mem (State.addr base) w 0 = M)
    (bound : numAt t.mem (State.addr base) w 6 < M)
    (value : numAt t.mem (State.addr base) w 6 * 2 ^ (64 * w) % M =
      numAt s.mem (State.addr base) w 6 * numAt s.mem (State.addr base) w 6 % M)
    (keeps : Keeps (State.addr base) len w 6 s.mem t.mem) :
    Power base len w M (2 * E) t :=
  h.after_y ready modulus keeps bound (mont_sq h.coprime h.value value)

theorem twice_ok (s : State) {base : BitVec 32} {len w M E : Nat}
    (h : Power base len w M E s) :
    WP isa twice s fun t => Power base len w M E t ∧
      numAt t.mem (State.addr base) w 1 < M ∧
      numAt t.mem (State.addr base) w 1 % M = 2 ^ (E + 1) * 2 ^ (64 * w) % M ∧
      HeaderKept base s t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [twice, VG.Impl.Bignum.Arm.TwoExp.candidate, WP.seq_iff]
  refine WP.mono (montOpArgs_ok s (o := 1) (a := 5) (b := 6) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨po, pa, pb, memU, restU⟩
  have ready := h.ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans h.ready.ptr)
  have doubleReady : DoubleFnReady base len w 1 5 6 u := by
    refine ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, po, pa, pb,
      ready.inverse, ?_⟩, ?_⟩
    · rw [memU, h.modulus]; exact h.bound
    · rw [memU]; exact h.two_low
  refine WP.mono (doubleFnRestore_ok u doubleReady
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    ready.stackRead ready.stackSep ready.saved) ?_
  rintro t ⟨bound, value, keeps, frame, restT, ptr⟩
  rw [memU] at bound value keeps frame
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans restT
  obtain ⟨readyT, modulusT⟩ := h.ready.after_array (by decide : 1 ≠ 0) keeps frame rest ptr
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have unchanged (i : Nat) (hi : Proof.Rsa.Mont.Operand i) (hne : i ≠ 1) :=
    keeps_array_num keeps fits hi hne
  have powerT : Power base len w M E t := by
    refine ⟨readyT, modulusT.trans h.modulus, h.coprime, ?_, ?_, ?_, ?_, ?_⟩
    · rw [unchanged 6 (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.bound
    · rw [unchanged 6 (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.value
    · rw [unchanged 5 (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.two
    · rw [unchanged 7 (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.one
    · rw [unchanged 4 (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]; exact h.r2
  rw [h.modulus] at bound value
  have candidate : numAt t.mem (State.addr base) w 1 % M = 2 ^ (E + 1) * 2 ^ (64 * w) % M := by
    rw [value, Nat.mod_mod, Nat.mul_mod, h.value, ← Nat.mul_mod,
      Nat.pow_succ', Nat.mul_assoc]
  exact ⟨powerT, bound, candidate, header_of_keeps h.ready keeps, frame, rest⟩

def inlineKernel (base : BitVec 32) (len w : Nat) :
    Kernel base len w (fun _ => True) [⟨State.addr base, 8 * len⟩] where
  square := squareOp 6 6
  twice := twice
  workspace := by simp
  stable := fun _ _ _ => trivial
  square_ok := by
    intro s E M h _
    refine WP.mono (squareOp_ok s h.ready
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
      (by rw [h.modulus]; exact h.bound)) ?_
    rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
    rw [h.modulus] at modulus bound value
    exact ⟨square_value h ready modulus bound value keeps, trivial,
      header_of_keeps h.ready keeps, frame, rest⟩
  twice_ok := by
    intro s E M h _
    refine WP.mono (twice_ok s h) ?_
    rintro t ⟨power, bound, value, header, frame, rest⟩
    exact ⟨power, bound, value, trivial, header, frame, rest⟩

/-- Supply a shared square without changing the exponent loop or its
linear doubling operation. -/
def kernelOfSquare {base : BitVec 32} {len w : Nat} {P : State → Prop}
    {regions : List Region} (square : Prog isa)
    (workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions)
    (stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
      Rest roundClobbers s t → P s → P t)
    (square_ok : ∀ (s : State) (E : Nat) {M : Nat}, Power base len w M E s → P s →
      WP isa square s fun t => ArithmeticReady base len w t ∧
        numAt t.mem (State.addr base) w 0 = M ∧ numAt t.mem (State.addr base) w 6 < M ∧
        numAt t.mem (State.addr base) w 6 * 2 ^ (64 * w) % M =
          numAt s.mem (State.addr base) w 6 * numAt s.mem (State.addr base) w 6 % M ∧
        Keeps (State.addr base) len w 6 s.mem t.mem ∧ P t ∧
        Frame regions s.mem t.mem ∧ Rest roundClobbers s t) : Kernel base len w P regions where
  square := square
  twice := twice
  workspace := workspace
  stable := stable
  square_ok := by
    intro s E M h hp
    refine WP.mono (square_ok s E h hp) ?_
    rintro t ⟨ready, modulus, bound, value, keeps, pt, frame, rest⟩
    exact ⟨square_value h ready modulus bound value keeps, pt,
      header_of_keeps h.ready keeps, frame, rest⟩
  twice_ok := by
    intro s E M h hp
    refine WP.mono (twice_ok s h) ?_
    rintro t ⟨power, bound, value, header, frame, rest⟩
    exact ⟨power, bound, value, stable frame rest hp, header,
      frame.mono (by simpa using workspace), rest⟩

end VG.Proof.Bignum.Arm.TwoExp

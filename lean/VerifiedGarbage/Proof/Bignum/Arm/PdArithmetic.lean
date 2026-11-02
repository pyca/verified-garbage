module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicData
public import VerifiedGarbage.Proof.Bignum.Arm.PublicStack
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # Stable public-operation state after modulus precomputation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

/-- The numerical precomputation equation needed for RSA correctness. -/
def pdGood (k N R : Nat) : Prop := R = 2 ^ (128 * Spec.Rsa.modulusWords k) % N

structure PdArithmetic (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  buffers : PublicData base dst ep xp len k eLen eb xb s
  stack : PublicStack base dst np ep xp len k eLen s
  ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) s
  modulus : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 = N
  odd : N % 2 = 1
  r2 : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
    R
  r2bound : R < N

theorem PdArithmetic.of_mem {s t : State} {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg}
    (h : PdArithmetic base dst np ep xp len k eLen N R eb xb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    PdArithmetic base dst np ep xp len k eLen N R eb xb t := by
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest,
    h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus, h.odd, by rw [mem]; exact h.r2, h.r2bound⟩

theorem PdArithmetic.after_array {s t : State} {base dst np ep xp : BitVec 32} {len k eLen N R o : Nat}
    {eb xb : List Byte} {rs : List Reg}
    (h : PdArithmetic base dst np ep xp len k eLen N R eb xb s)
    (ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t)
    (keeps : Keeps (State.addr base) len (Spec.Rsa.modulusWords k) o s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t)
    (ho0 : o ≠ 0) (ho4 : o ≠ 4) :
    PdArithmetic base dst np ep xp len k eLen N R eb xb t := by
  have fits : arrAt (Spec.Rsa.modulusWords k) 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  exact ⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready,
    (keeps_array_num keeps fits op0 (Ne.symm ho0)).trans h.modulus, h.odd,
    (keeps_array_num keeps fits op4 (Ne.symm ho4)).trans h.r2, h.r2bound⟩

structure PdOperand (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop extends PdArithmetic base dst np ep xp len k eLen N R eb xb s where
  input : numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 1 = Spec.Rsa.os2ip xb

structure PdAccepted (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop extends PdOperand base dst np ep xp len k eLen N R eb xb s where
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 =
    BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < N)).toNat

end VG.Proof.Bignum.Arm

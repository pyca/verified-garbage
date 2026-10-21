module

public import VerifiedGarbage.Impl.Mont.X86.ContextSquares
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! Repeated Montgomery squaring with the shared fixed-base comb encoding. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem combSquares_ok {s : State} {base : Addr} {n size m o g E count : Nat}
    (C : Context n m base size s) (ho : o < 9) (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2)
    (hc : 0 < count) (hc32 : count < 2^32)
    (V : wordsVal s.mem base (slot n o) n = Spec.Rsa.powMod g E m * 2^(64*n) % m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.repeatSquares n o count) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n o) n = Spec.Rsa.powMod g (2^count*E) m * 2^(64*n) % m ∧
      Outs base [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)] s.mem t.mem ∧
      Keeps powerClob s t := by
  let ranges := [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)]
  let I (i : Nat) (t : State) : Prop :=
    Context n m base size t ∧ t.gpr .esi = BitVec.ofNat 32 (count-i) ∧
    wordsVal t.mem base (slot n o) n = Spec.Rsa.powMod g (2^i*E) m * 2^(64*n) % m ∧
    Outs base ranges s.mem t.mem ∧ Keeps powerClob s t
  unfold VG.Impl.Mont.X86.Dynamic.repeatSquares
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have K : Keeps powerClob s u := U.keeps.mono (by decide)
  have init : I 0 u := by
    refine ⟨⟨C.scr.of_keeps K (by decide), C.size_le, U.mem ▸ C.modulus, C.gt_one, U.mem ▸ C.inverse⟩,
      U.gpr, ?_, U.mem ▸ Outs.refl _ _ _, K⟩
    simpa only [U.mem, Nat.pow_zero, Nat.one_mul] using V
  refine WP.mono (countLoop hc I ?_ init) fun t ⟨Ct, _, Vt, Ot, Kt⟩ => ⟨Ct, Vt, Ot, Kt⟩
  rintro i t hi ⟨Ct, counter, value, O, Kt⟩
  unfold squareStep
  refine WP.seq (WP.mono (context_mul_ok Ct ho ho ho ho0 ho1 ho2 ho2 ho2
    (by rw [value]; exact Nat.mod_lt _ (by have := Ct.gt_one; omega)) ho1 ho1)
    fun v ⟨Cv, Kv, lt, product⟩ => ?_)
  have Vv : wordsVal v.mem base (slot n o) n = Spec.Rsa.powMod g (2^(i+1)*E) m * 2^(64*n) % m := by
    have step := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded Ct.coprime lt value product
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using step
  have Ov : Outs base ranges t.mem v.mem := by
    have length : accLen (contextMod n) = 16*n+4 := context_accLen n
    have frame := Kv.mem
    change Outs base [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, accLen (contextMod n))] t.mem v.mem at frame
    simpa only [length] using frame
  have counterv : v.gpr .esi = BitVec.ofNat 32 (count-i) := (Kv.gpr .esi (by decide)).trans counter
  refine wp_subS rfl fun w UW _ => wp_cmpS rfl fun z F Z => WP.block_nil ?_
  have mem : z.mem = v.mem := F.mem.trans UW.mem
  have keep : Keeps powerClob v z := (UW.keeps.mono (by decide)).trans (F.keeps _)
  have Cz : Context n m base size z :=
    ⟨Cv.scr.of_keeps keep (by decide), Cv.size_le, mem ▸ Cv.modulus, Cv.gt_one, mem ▸ Cv.inverse⟩
  refine ⟨⟨Cz, ?_, mem ▸ Vv, mem ▸ O.trans Ov,
    Kt.trans (((OpKeep.keeps Kv).mono (by decide)).trans keep)⟩, ?_⟩
  · rw [F.gpr, UW.gpr, counterv, counter_sub (by omega) (by omega)]
    congr 1
  · rw [Z, UW.gpr, counterv, counter_sub (by omega) (by omega), counter_zero (by omega) (by omega)]
    simp only [show (count-i = 1) ↔ i+1 = count by omega]

end VG.Proof.Mont.X86.Dynamic

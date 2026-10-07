import VerifiedGarbage.Proof.P256.VerifySparse.Ops
import VerifiedGarbage.Proof.P256.VerifySparse.Square

/-! The executable suffix replacement agrees with the proved sparse operation bodies.
The prefix is kept symbolic so the proof does not evaluate the full instruction list. -/
namespace VG.Proof.P256.VerifySparse
open VG.Proof.Mont.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem take_prefix {α : Type} (xs ys : List α) :
    (xs++ys).take ((xs++ys).length-ys.length)=xs := by
  simp only [List.length_append,Nat.add_sub_cancel,List.take_left]

theorem op_add (o a b : Nat) : Impl.P256.VerifySparse.op (.add o a b)=
    sparseAdd Impl.P256.VerifySparse.M o a b := by
  let pre := zero7 :: loads (low 4) a ++ chain (.adds .x) (.adcs .x) (low 4) b ++
    [.adc .x (top 4) .x7 .x7]
  let tail := csubR Impl.P256.VerifySparse.M (low 4) (top 4) ++ stores (low 4) o
  have raw : opCode Impl.P256.VerifySparse.M (.add o a b)=pre++tail := by
    simp only [opCode,Impl.Mont.AArch64.add,pre,tail,List.append_assoc,List.cons_append]
    rfl
  change (opCode Impl.P256.VerifySparse.M (.add o a b)).take
    ((opCode Impl.P256.VerifySparse.M (.add o a b)).length-tail.length) ++
    Impl.P256.VerifySparse.correct (low 4) (top 4) ++ stores (low 4) o = _
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseAdd,List.append_assoc]
  rfl


theorem op_mul (o a b : Nat) (hab : a≠b) : Impl.P256.VerifySparse.op (.mul o a b)=
    sparseMul Impl.P256.VerifySparse.M o a b := by
  have h : (a==b)=false := beq_eq_false_iff_ne.mpr hab
  let ts := (List.range 4).map (win 4 4)
  let pre := mulSetup Impl.P256.VerifySparse.M b ++
    (List.range 4).flatMap (round Impl.P256.VerifySparse.M a b)
  let tail := csubR Impl.P256.VerifySparse.M ts (win 4 4 4) ++ stores ts o
  have raw : opCode Impl.P256.VerifySparse.M (.mul o a b)=pre++tail := by
    rw [opCode,h]
    change mul Impl.P256.VerifySparse.M o a b=pre++tail
    rw [mul_eq]
    simp only [pre,tail,ts,List.append_assoc]
    rfl
  dsimp only [Impl.P256.VerifySparse.op]
  rw [h]
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseMul,List.append_assoc]
  rfl

theorem op_square (o a : Nat) : Impl.P256.VerifySparse.op (.mul o a a)=
    sparseSquare o a := by
  have h : P256Square.supported Impl.P256.VerifySparse.M=true := by decide
  let pre := VG.Proof.Mont.AArch64.P256Square.core a
  let tail := csubR Impl.P256.VerifySparse.M [.x8,.x9,.x10,.x11] .x12 ++ stores [.x8,.x9,.x10,.x11] o
  have raw : opCode Impl.P256.VerifySparse.M (.mul o a a)=pre++tail := by
    simp only [opCode,BEq.rfl,Bool.true_and,h,ite_true]
    simp only [P256Square.square,VG.Proof.Mont.AArch64.P256Square.core,pre,tail,List.append_assoc]
  dsimp only [Impl.P256.VerifySparse.op]
  rw [show (a==a)=true from beq_self_eq_true a]
  rw [raw]
  change (pre++tail).take ((pre++tail).length-tail.length) ++ _ ++ _ = _
  rw [take_prefix]
  simp only [pre,sparseSquare,List.append_assoc]
  rfl

end VG.Proof.P256.VerifySparse

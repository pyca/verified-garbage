module

public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.Proof.Camellia.Words
import Mathlib.Tactic.IntervalCases

/-! # Word-oriented descriptions of Camellia's substitution and diffusion

`f_eq`: Camellia's F-function is the S-boxes of the bytes (`substituted`)
and then the P-function on 32-bit halves by rotations (`linearWord`), as
the single-block cores compute it (AArch64's and PPC64LE's). -/

@[expose] public section
namespace VG.Proof.Camellia.Serial
open VG

def byte (x : BitVec 64) (j : Nat) : Byte := (x >>> (8*j)).setWidth 8

/-- Pack byte zero into the least significant octet. -/
def packed (t : Nat → Byte) : BitVec 64 :=
  t 7 ++ t 6 ++ t 5 ++ t 4 ++ t 3 ++ t 2 ++ t 1 ++ t 0

theorem byte_packed (t : Nat → Byte) (j : Nat) (hj : j < 8) :
    byte (packed t) j = t j := by
  interval_cases j <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    simp only [byte, packed, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append]
    simp +arith (disch := omega) only [Nat.reduceMul, Nat.reduceSub,
      ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and,
      Nat.add_sub_cancel, Nat.add_sub_assoc, ite_false]

def substitutedByte (x : BitVec 64) (j : Nat) : Byte :=
  match j with
  | 0 => Spec.Camellia.sbox1 (byte x 0)
  | 1 => Spec.Camellia.sbox4 (byte x 1)
  | 2 => Spec.Camellia.sbox3 (byte x 2)
  | 3 => Spec.Camellia.sbox2 (byte x 3)
  | 4 => Spec.Camellia.sbox4 (byte x 4)
  | 5 => Spec.Camellia.sbox3 (byte x 5)
  | 6 => Spec.Camellia.sbox2 (byte x 6)
  | _ => Spec.Camellia.sbox1 (byte x 7)

def substituted (x : BitVec 64) : BitVec 64 := packed (substitutedByte x)

def permuted (x : BitVec 64) : BitVec 64 :=
  let a := byte x 7; let b := byte x 6; let c := byte x 5; let d := byte x 4
  let e := byte x 3; let f := byte x 2; let g := byte x 1; let h := byte x 0
  (a ^^^ c ^^^ d ^^^ f ^^^ g ^^^ h) ++
  (a ^^^ b ^^^ d ^^^ e ^^^ g ^^^ h) ++
  (a ^^^ b ^^^ c ^^^ e ^^^ f ^^^ h) ++
  (b ^^^ c ^^^ d ^^^ e ^^^ f ^^^ g) ++
  (a ^^^ b ^^^ f ^^^ g ^^^ h) ++
  (b ^^^ c ^^^ e ^^^ g ^^^ h) ++
  (c ^^^ d ^^^ e ^^^ f ^^^ h) ++
  (a ^^^ d ^^^ e ^^^ f ^^^ g)

def linearWord (x : BitVec 64) : BitVec 64 :=
  let u := (x >>> 32).setWidth 32
  let l := x.setWidth 32
  let a := u ^^^ u.rotateRight 8 ^^^ u.rotateRight 16
  let b := l.rotateRight 8 ^^^ l.rotateRight 16 ^^^ l.rotateRight 24
  (a ^^^ b) ++ (u ^^^ u.rotateRight 24 ^^^ b)

theorem linearWord_byte (x : BitVec 64) (j : Nat) (hj : j < 8) :
    byte (linearWord x) j = byte (permuted x) j := by
  interval_cases j <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [linearWord, permuted, byte,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight]
    <;> simp +arith (disch := omega) only [Nat.reduceMul, Nat.reduceSub,
      Nat.reduceMod, ite_eq_left, ite_eq_right, decide_eq_true,
      Bool.true_and, ite_false, Nat.add_sub_cancel, Nat.add_sub_assoc]
    <;> simp +arith only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem linearWord_eq (x : BitVec 64) : linearWord x = permuted x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := congrArg (fun b : Byte => b.getLsbD (i % 8))
    (linearWord_byte x (i / 8) (by omega))
  simpa [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    Nat.mod_lt i (by decide : 0 < 8), Nat.div_add_mod] using h

theorem extract_self (x : BitVec 32) (r : Nat) (hr : r < 32) :
    (x ++ x).extractLsb' r 32 = x.rotateRight r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_append,
    BitVec.getLsbD_rotateRight,Nat.mod_eq_of_lt hr,hi,decide_true,Bool.true_and]
  by_cases h : i < 32-r
  · simp only [h,ite_true,show r+i < 32 by omega]
  · simp only [h,ite_false,show ¬r+i < 32 by omega]
    congr 1
    omega

/-- The scalar substitute/diffuse factorization is exactly the standard F function. -/
theorem f_eq (x k : BitVec 64) :
    Spec.Camellia.f x k = linearWord (substituted (x ^^^ k)) := by
  rw [linearWord_eq]
  simp only [permuted, substituted]
  simp only [byte_packed _ 0 (by decide),
    byte_packed _ 1 (by decide), byte_packed _ 2 (by decide),
    byte_packed _ 3 (by decide), byte_packed _ 4 (by decide),
    byte_packed _ 5 (by decide), byte_packed _ 6 (by decide),
    byte_packed _ 7 (by decide)]
  rfl

/-- `cryptWords` reads only the schedule's first `8 g + 2` words. -/
theorem cryptWords_congr (g : Nat) (hg : g = 3 ∨ g = 4)
    (E F : Nat → BitVec 64) (m : BitVec 128)
    (h : ∀ i < 8*g+2, E i = F i) :
    Proof.Camellia.cryptWords g E m = Proof.Camellia.cryptWords g F m := by
  rcases hg with rfl | rfl
  · simp only [Proof.Camellia.cryptWords,Proof.Camellia.groups,
      Proof.Camellia.group,Proof.Camellia.pair,List.range_succ,List.range_zero,
      List.foldl_append,List.foldl_cons,List.foldl_nil,List.nil_append,
      Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]
    simp only [h 0 (by decide),
      h 1 (by decide),
      h 2 (by decide),
      h 3 (by decide),
      h 4 (by decide),
      h 5 (by decide),
      h 6 (by decide),
      h 7 (by decide),
      h 8 (by decide),
      h 9 (by decide),
      h 10 (by decide),
      h 11 (by decide),
      h 12 (by decide),
      h 13 (by decide),
      h 14 (by decide),
      h 15 (by decide),
      h 16 (by decide),
      h 17 (by decide),
      h 18 (by decide),
      h 19 (by decide),
      h 20 (by decide),
      h 21 (by decide),
      h 22 (by decide),
      h 23 (by decide),
      h 24 (by decide),
      h 25 (by decide)]
  · simp only [Proof.Camellia.cryptWords,Proof.Camellia.groups,
      Proof.Camellia.group,Proof.Camellia.pair,List.range_succ,List.range_zero,
      List.foldl_append,List.foldl_cons,List.foldl_nil,List.nil_append,
      Nat.reduceAdd,Nat.reduceMul,Nat.reduceLT,ite_true,ite_false]
    simp only [h 0 (by decide),
      h 1 (by decide),
      h 2 (by decide),
      h 3 (by decide),
      h 4 (by decide),
      h 5 (by decide),
      h 6 (by decide),
      h 7 (by decide),
      h 8 (by decide),
      h 9 (by decide),
      h 10 (by decide),
      h 11 (by decide),
      h 12 (by decide),
      h 13 (by decide),
      h 14 (by decide),
      h 15 (by decide),
      h 16 (by decide),
      h 17 (by decide),
      h 18 (by decide),
      h 19 (by decide),
      h 20 (by decide),
      h 21 (by decide),
      h 22 (by decide),
      h 23 (by decide),
      h 24 (by decide),
      h 25 (by decide),
      h 26 (by decide),
      h 27 (by decide),
      h 28 (by decide),
      h 29 (by decide),
      h 30 (by decide),
      h 31 (by decide),
      h 32 (by decide),
      h 33 (by decide)]

end VG.Proof.Camellia.Serial

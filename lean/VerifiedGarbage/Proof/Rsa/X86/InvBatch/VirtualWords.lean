module

import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass

/-! # Scanning the modulus for the virtual replacement of one -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

 def seededOr (seed : BitVec 32) (f : Nat → BitVec 32) : Nat → BitVec 32
 | 0 => seed
 | n+1 => seededOr seed f n ||| f n

 theorem seededOr_zero (seed : BitVec 32) (f : Nat → BitVec 32) (n : Nat) :
    seededOr seed f n=0 ↔ seed=0 ∧ ∀ i<n,f i=0 := by
  induction n with
  | zero => simp [seededOr]
  | succ n ih =>
    have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x=0 ∧ y=0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [seededOr,hor,ih]
    constructor
    · rintro ⟨⟨seed,early⟩,last⟩
      refine ⟨seed,?_⟩
      intro i hi
      by_cases lt : i<n
      · exact early i lt
      · have e : i=n := by omega
        simpa only [e] using last
    · rintro ⟨seed,all⟩
      exact ⟨⟨seed,fun i hi => all i (by omega)⟩,all n (by omega)⟩

 theorem scanOne_ok {base : Addr} {size M : Nat} (count : Nat) (s : State)
    (hs : Scr s base size) (fits : M+4*(count+1)≤size) :
    WP isa (.block ((List.range count).map fun j => .alu .or .eax (.mem (sc (M+4*(j+1)))))) s fun t =>
      t.gpr .eax=seededOr (s.gpr .eax) (fun j => s.mem.readW (off base (M+4*(j+1))) 32) count ∧
      Keeps [.eax] s t ∧ t.mem=s.mem := by
  induction count with
  | zero => exact WP.block_nil ⟨rfl,Keeps.refl _ _,rfl⟩
  | succ count ih =>
    rw [List.range_succ,List.map_append]
    refine WP.block_append (WP.mono (ih (by omega)) fun u ⟨vu,ku,mu⟩ => ?_)
    have hu := hs.of_keeps ku (by decide)
    simp only [List.map_cons,List.map_nil]
    refine wp_orS (readSrc_sc hu (d:=M+4*(count+1)) (by omega)) fun t T => WP.block_nil ?_
    refine ⟨?_,ku.trans T.keeps,T.mem.trans mu⟩
    rw [T.gpr,vu,mu]
    rfl

end VG.Proof.Rsa.X86.InvBatch

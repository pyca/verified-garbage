module

import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
public import VerifiedGarbage.Proof.Mont.Words

/-! # Address the exponent word using the public native-word countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def wordPointer : List Instr :=
  ptr .ebp aExponent ++ [.mov .eax (.mem (slot sWords)), .alu .sub .eax (.imm 1),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebp (.reg .eax)]

theorem wordPointer_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q ≤ g.words)
    (count : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q) :
    WP isa (.block wordPointer) s fun t =>
      PtrAt t g.W .ebp (g.array aExponent + 4 * (q - 1)) ∧ t.mem = s.mem ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have header := v.headerFit
  have expFit := v.arrayFit (j := aExponent) (by decide)
  have small : q ≤ 256 := by have := v.maxWidth; unfold Geometry.words at bound; omega
  unfold wordPointer
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun u ⟨P, Mu, Ku⟩ => ?_)
  have Cu := C.keepMem Ku (by decide) Mu
  refine wp_movS (Cu.readScalar sWords (by unfold sWords; omega)) fun a A _ => ?_
  refine wp_subS rfl fun b B _ => wp_addS rfl fun c D _ => wp_addS rfl fun d H _ => ?_
  have Kd : Keeps [.eax, .edx, .ebp] s d :=
    ((((Ku.mono (by decide)).widen A.keeps).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := H.mem.trans (D.mem.trans (B.mem.trans (A.mem.trans Mu)))
  have bp : PtrAt d g.W .ebp (g.array aExponent) := by
    rw [PtrAt, H.other .ebp (by decide), D.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide)]; exact P
  have indexVal : (d.gpr .eax).toNat = 4 * (q - 1) := by
    rw [H.gpr, D.gpr, B.gpr, A.gpr, Mu, count]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 +
      ((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
    omega
  refine wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp] s e := Kd.widen I.keeps
  have Me : e.mem = s.mem := I.mem.trans Md
  have be : PtrAt e g.W .ebp (g.array aExponent + 4 * (q - 1)) := by
    rw [PtrAt, I.gpr, ptr_add bp, indexVal]
  exact WP.block_nil ⟨be, Me, Ke⟩

end VG.Proof.MillerRabin.X86

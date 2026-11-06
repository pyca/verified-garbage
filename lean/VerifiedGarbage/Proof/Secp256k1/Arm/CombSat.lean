module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Shared memory for satisfiable ARM comb contracts: tables at 1 MiB, scratch at zero. -/

@[expose] public section
namespace VG.Proof.Secp256k1.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm

theorem comb_words_length : secp256k1CombWords.length=18944 := by
  have len := VG.Proof.Weierstrass.tcombWords_length (n := 4) (R := 2^256)
    (p := Spec.Secp256k1.curve.p) (tbl := VG.Impl.Secp256k1.secp256k1Comb7)
    (J := 37) (H := 64) (by decide +kernel) (by decide +kernel)
  unfold secp256k1CombWords
  exact len

@[irreducible] def combSatMem : Mem := constMem 0x100000 secp256k1CombWords

theorem combSat_held : ∀ i<secp256k1CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=secp256k1CombWords.getD i 0 :=
  by
    unfold combSatMem
    exact constMem_held _ _ (by rw [comb_words_length]; decide)

def combSatState : State where
  gpr r := match r with
    | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | .r3 => 0x16000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem := combSatMem
  rd := [⟨0x12000,32⟩,⟨0x14000,32⟩,⟨0x16000,32⟩,⟨0x20000,4⟩,⟨0x100000,151552⟩]
  wr := [⟨0x10000,64⟩,⟨0,8192⟩]
  syms _ := 0x100000

end VG.Proof.Secp256k1.Arm

module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Existing hash variants supply the generator's instruction and stack checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64

theorem generationSafe_of_noSp {c : Prog isa} (hs : NoSp c)
    (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) : generationSafe c := by
  have sp := VG.Proof.RsaOaep.X86_64.SpSafe.of_noSp hs
  rw [generationSafe, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at hm
  apply List.all_eq_true.mpr
  intro i hi
  rw [sp i hi, Bool.not_false, Bool.and_true]
  exact List.all_eq_true.mp hm i hi

theorem hashCode_safe (v : MdHash) : HashSafety v.H.stream :=
  ⟨generationSafe_of_noSp v.ok.initSp v.K.iMx,
    generationSafe_of_noSp v.ok.updSp v.ok.updMx,
    generationSafe_of_noSp v.ok.finSp v.ok.finMx⟩

theorem hashCode_depth (v : MdHash) : HashDepth v.H.stream where
  init := by
    change v.H.initC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.initSp]
    have hd := v.ok.initDepth
    omega
  update := by
    change v.H.updC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.updSp]
    have hd := v.ok.updDepth
    omega
  finish := by
    change v.H.finC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.finSp]
    have hd := v.ok.finDepth
    omega

end VG.Proof.Dsa.X86_64.Generation

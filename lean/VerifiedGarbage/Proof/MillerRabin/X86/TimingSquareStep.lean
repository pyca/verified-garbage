module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.MillerRabin.X86.TimingEqual

/-! # Squaring and masked flag updates have a public-address trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem squareStep_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity aY p s ∧ MulInput g capacity aY p t)
      (squareStep name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (mulY name code aY)
    (.seq (equal sEq2 aY aMinusOne) (.block squareFlag))) _
  refine RelCT.seq (mulY_relCT verified noSp stack v length (by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide)) ?_
  exact RelCT.seq (equal_relCT v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp) (by decide) (by decide))
    (squareFlag_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H))

end VG.Proof.MillerRabin.X86

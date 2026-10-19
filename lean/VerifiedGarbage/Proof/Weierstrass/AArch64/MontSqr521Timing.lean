module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqrVerified
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSqrVerified
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst

/-! Constant-time execution of the P-521 square with public pointer and low32 offsets. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Spec.Weierstrass.Mont
open VG.Impl.Mont.AArch64.P521Square

private theorem entry_split : VG.Impl.Mont.AArch64.P521Square.entry =
    zextCode ++ VG.Impl.Mont.AArch64.P521Square.entry.drop 3 := by decide +kernel

private theorem square_exec {s t : State} {tr : List Leak}
    (h : Exec isa sqrFn521 s tr t) :
    Exec isa (.seq (.block zextCode)
      (.seq (.block (entry.drop 3)) (.block (core ++ exit)))) s tr t := by
  cases h with
  | seq a b =>
    rw [Exec.block_iff, entry_split, execBlock_append] at a
    obtain ⟨⟨ta,u⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp a
    obtain ⟨⟨tb,v⟩,hc,he⟩ := Option.map_eq_some_iff.mp hb
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    simpa only [List.append_assoc] using Exec.seq (.block ha) (.seq (.block hc) b)

theorem p521p_sqr_ct : ConstantTime isa (sqrA p521p).pre (sqrA p521p).pub sqrFn521 := by
  have h : ConstantTime isa (sqrA p521p).pre aPub
      (.seq (.block zextCode) (.seq (.block (entry.drop 3)) (.block (core ++ exit)))) :=
    ct_zext (VectorTaint.constantTime (Taint.ofRegs [.x0,.x1,.x2,.x3])
      (fun _ _ _ _ hp => hp) (by taint_decide))
  intro s u ts tu s' u' hs hu hp es eu
  exact h s u ts tu s' u' hs hu hp (square_exec es) (square_exec eu)

end VG.Proof.Weierstrass.AArch64.Mont

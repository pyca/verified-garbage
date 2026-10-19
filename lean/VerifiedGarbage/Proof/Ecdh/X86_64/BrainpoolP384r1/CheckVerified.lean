module

public import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
meta import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import Mathlib.Tactic.ClearExcept
meta import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86_64
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintMap
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.Exchange
meta import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.InvFnX
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Bswap
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Mont.Words128
meta import VerifiedGarbage.Proof.Mont.X86_64.Blocks
meta import VerifiedGarbage.Proof.Mont.X86_64.CsubS
meta import VerifiedGarbage.Proof.Mont.X86_64.Friendly
meta import VerifiedGarbage.Proof.Mont.X86_64.Ops
meta import VerifiedGarbage.Proof.Mont.X86_64.Round
meta import VerifiedGarbage.Proof.Mont.X86_64.Sparse
meta import VerifiedGarbage.Proof.Mont.X86_64.SparseX
meta import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
meta import VerifiedGarbage.Proof.Mont.X86_64.Wide
meta import VerifiedGarbage.Proof.Mont.X86_64.WideOps
meta import VerifiedGarbage.Proof.Weierstrass.JacAdd
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Spec.EcKey.Generic

/-!
# `vg_brainpoolp384r1_check_point` on x86-64: `Verified`

`CheckFn.correct` for brainpoolP384r1's configurations (`Inverse.cfg`), whose slots
are the curve's (`agree`); constant time by taint tracking, `rdi` and `rsp`
public, on the code's literals.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 VG.Proof.Ecdh.X86_64.CheckFn
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.BrainpoolP384r1.Inverse (cfg cfg_ok)

abbrev C : CP := Spec.Weierstrass.CheckPoint.brainpoolp384r1

/-- `vg_brainpoolp384r1_check_point`. -/
abbrev code : Prog isa := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody cfg)

theorem agree : Agree cfg C := ⟨rfl, rfl, by decide +kernel, keeps_of_covers (by decide +kernel), by decide +kernel⟩

theorem hvm : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).allInstrs
    (fun i => !KeepReg.writesVec i && !loadsMxcsr i) = true := by
  lit_decide

theorem hv : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).allInstrs (fun i => !KeepReg.writesVec i) = true :=
  (hv_hmx hvm).1

theorem hn : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).noCalls = true := by
  lit_decide

theorem hmx : code.allInstrs (fun i => !loadsMxcsr i) = true :=
  (hv_hmx hvm).2

theorem ct : ConstantTime isa (checkK C).pre (checkK C).pub code :=
  VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) (agreeK C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Spec.Weierstrass.CheckPoint.Curve.pre; decide +kernel

theorem verified (hI : InvSounds) : Verified X86_64.target code (C.checkContract X86_64.abi) :=
  Verified.of_correct (correct (cfg_ok hI) agree hv hn hmx) ct (implies C sat)

end VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check

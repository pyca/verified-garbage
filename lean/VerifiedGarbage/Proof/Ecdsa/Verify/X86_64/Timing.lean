module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Points
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy

/-! Verification lookups depend only on public digest and signature inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdsa.Verify.X86_64 (U V)
variable {c : Cfg}

def publicU (c : Cfg) (s : State) : Nat :=
  (Fin.ofNat c.C.n (dig c s) * Fin.ofNat c.C.n (sigS c s) ^ (c.C.n - 2)).val

theorem mid_publicU {s₀ s : State} {base : Addr} {g : Reg → BitVec 64}
    (h : Mid c s₀ base g s) : sv c base s U = publicU c s₀ := by
  have he := congrArg Fin.val h.u
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt h.u_lt,publicU] using he

def verifyPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.check c).inline <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c).inline <| .seq c.nPow.inline <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c).inline <|
  .seq (bits (c.sl U) (bitsAt c.n 0) (8*c.n)) <|
  .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) (.block [])

def verifySuffix (c : Cfg) : Prog isa :=
  .seq (.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.save c))
    (.seq (Impl.Ecdsa.Verify.X86_64.Cfg.mulV c) (Impl.Ecdsa.Verify.X86_64.Cfg.sum c)))
    (Impl.Ecdsa.Verify.X86_64.Cfg.tail c)

end VG.Proof.Ecdsa.Verify.X86_64

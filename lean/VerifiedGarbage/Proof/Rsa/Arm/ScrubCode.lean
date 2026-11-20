module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Impl.RsaPkcs1Sig.Arm.Wrap
import VerifiedGarbage.Proof.Framework.Lit

/-!
# What the cleanup needs of RSA's code on ARMv7

`CodeOk` (`Proof/Framework/Arm/ScrubProved.lean`) of the code RSA's
functions share, for the cleanup of the functions that call it: the frames of
the code use at most so many bytes and it makes no indirect call. Each is
proven once for any implementation of the private CRT's interface, from what
the implementation states of its own code (`CrtImpl.crtPOk`, `pdOk`), and
the code around it by `lit_decide`: `vg_rsa_private_checked_precomputed`'s
code (`privCodeP_ok`), and a function's body in its frame inside the push of
every register (`wrap_codeOk`).
-/

-- separate module: RSA's PKCS #1 v1.5, OAEP and PSS functions on ARMv7 use it too, without each other's proofs.

@[expose] public section

namespace VG.Proof.Rsa.Arm.Scrub

open VG.Arm VG.Arm.Scrub

/-- Code that `CodeOk` holds of with no stack holds of with any. -/
theorem CodeOk.zero {c : Prog isa} {n : Nat} (h : CodeOk c 0) : CodeOk c n := h.mono (Nat.zero_le n)

/-- `body` in a frame of `F` bytes, inside the push of every register. -/
theorem wrap_codeOk {F n : Nat} {body : Prog isa} (h : CodeOk body n) :
    CodeOk (Impl.RsaPkcs1Sig.Arm.wrap F body) (n + F + 56) :=
  CodeOk.push (CodeOk.seq (CodeOk.alloc h) (CodeOk.zero (CodeOk.block _)))

theorem checkP_tail_ok : CodeOk Impl.Rsa.Arm.PrivChecked.tail 0 := by lit_decide

theorem pcCopy_ok : CodeOk Impl.Rsa.Arm.PrivChecked.pcCopy 0 := by lit_decide

/-- `vg_rsa_private_checked_precomputed`'s code, over `v`. -/
theorem privCodeP_ok (v : CrtImpl) : CodeOk (privCodeP v) 3440 :=
  CodeOk.push (n := 3384) (CodeOk.seq (CodeOk.alloc (n := 56)
    (CodeOk.seq (CodeOk.zero (CodeOk.block _)) (CodeOk.seq (CodeOk.call v.crtPOk)
      (CodeOk.seq (CodeOk.zero (CodeOk.block _)) (CodeOk.seq (CodeOk.zero pcCopy_ok)
        (CodeOk.seq (CodeOk.zero (CodeOk.block _)) (CodeOk.seq (CodeOk.call v.pdOk)
          (CodeOk.zero checkP_tail_ok))))))))
    (CodeOk.zero (CodeOk.block _)))

end VG.Proof.Rsa.Arm.Scrub

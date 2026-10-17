module

public import VerifiedGarbage.Impl.Bignum.Arm.Setup

/-! # ARMv7 CRT storage

The main workspace and one workspace per factor use the modulus width, so a
full ciphertext can be reduced modulo either factor by Montgomery products.
Three separate extended buffers hold the full factor product, its comparison
scratch and the zero-extended modulus. A last, narrow workspace, sized for the
modulus width but set up at a factor's own width, holds each factor's
exponentiation in turn. Everything fits the shared RSA scratch API.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt

/-- Each arithmetic workspace contains a header and eight padded arrays. -/
def workspaceWords (w : Nat) : Nat := 8 * w + 48
def stride (w : Nat) : Nat := 8 * workspaceWords w
def pOffset (w : Nat) : Nat := stride w
def qOffset (w : Nat) : Nat := 2 * stride w
/-- Two native factor widths and two carry words. -/
def productWords (w : Nat) : Nat := 4 * w + 2
def productBytes (w : Nat) : Nat := 4 * productWords w
def productOffset (w : Nat) : Nat := 3 * stride w
def compareOffset (w : Nat) : Nat := productOffset w + productBytes w
def modulusOffset (w : Nat) : Nat := compareOffset w + productBytes w
def narrowOffset (w : Nat) : Nat := modulusOffset w + productBytes w
def totalBytes (w : Nat) : Nat := narrowOffset w + stride w

end VG.Impl.Bignum.Arm.Crt

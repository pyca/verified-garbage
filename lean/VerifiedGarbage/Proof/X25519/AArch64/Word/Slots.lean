module

public import VerifiedGarbage.Impl.X25519.AArch64.Word
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-! The four-word field backend in X25519's existing 4 KiB workspace. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev Scratch (s : State) (base : Addr) := Scr s base false

end VG.Proof.X25519.AArch64.Word

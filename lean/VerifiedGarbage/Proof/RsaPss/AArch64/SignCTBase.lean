module
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT

/-!
# RSASSA-PSS signing on AArch64: constant time, the public data

The pointers, the lengths, the tables' addresses and the bytes of `n` and
`e` are public (`PubS`); the digest, the salt and the private key are
secret. Two runs with the same public data as an anchor `a` (`E`) are
related at each point of the code by what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the bytes of `n` and `e`. -/
structure PubS (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 16, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat

theorem PubS.refl (s : State) : PubS s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- An entry state with the anchor's public data. -/
def E (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := PreS tsH tsG K s ∧ PubS a s

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem n0 : s.mem (s.gpr .x2) = a.mem (a.gpr .x2) := by
  have hk := h.1.k1
  have e3 := h.gpr (r := .x3) (by decide)
  have := h.2.bn
  rw [bytesAt_cons s.mem (s.gpr .x2) (k := (s.gpr .x3).toNat) (by omega),
    bytesAt_cons a.mem (a.gpr .x2) (k := (a.gpr .x3).toNat) (by rw [← e3]; omega)] at this
  exact (List.cons.inj this).1

theorem scr : scr s = scr a := h.2.args 12 (by decide)

end E

/-- The first byte of `n`. -/
abbrev nx (s : State) : Nat := (s.mem (s.gpr .x2)).toNat

end VG.Proof.RsaPss.AArch64.Sgn

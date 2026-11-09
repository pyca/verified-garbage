module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre

/-!
# RSAES-OAEP encryption on PPC64LE: two runs, and the label's hash

Untrusted: everything here is checked by Lean. Two runs are compared through
an anchor `a`, a state with their public data (`PubO`): the pointers and
lengths, `e`'s bytes and the precomputed values; `BO D a t`: `t` has `Base`
from an entry state with `a`'s public data (`B`, `Proof/RsaOaep/PPC64LE/CTBase.lean`,
with `oaepOk`). The label's hash is through its table, in two runs
`hashLabelT_ct` (`CTMgfT.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil)

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubO (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  args : ∀ i < 8, stackArg s i = stackArg a i
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat

theorem PubO.S {a s : State} (p : PubO a s) : S s = stackArg a 4 := p.args 4 (by decide)

/-- `PubO` gives what the shared code needs. -/
theorem oaepOk (D : Nat) : Ok S vO (PreO D) PubO where
  fits P := P.fits
  agree {a s} p := ⟨p.sp, p.S, fun r hr => by
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vO]
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.g _ (by decide)
    · exact p.args 6 (by decide)
    · exact p.args 7 (by decide)
    · exact p.args 5 (by decide)⟩

/-- `t` has `Base` from an entry state with `a`'s public data. -/
abbrev BO (D : Nat) : State → State → Prop := B S vO (PreO D) PubO

end VG.Proof.RsaOaep.PPC64LE

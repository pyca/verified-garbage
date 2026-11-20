module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ECDSA on x86 (32-bit), without secret residue

For every curve, the postconditions of `vg_ecdsa_<curve>_verify` and of
`vg_ecdsa_<curve>_sign` (generic over the HMAC implementations its table
holds) read the memory on return only within `out` (`X86.Scrub.PostOut`),
as on RISC-V (`Proof/EcKey/RISCV64/Scrub.lean`,
`Proof/Ecdsa/Rfc6979/RISCV64/Scrub.lean`): what
`X86.Scrub.verifiedScrubbedF` needs of each implementation followed by its
cleanup, the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail`. The registrations are each curve's `Scrub` module
(`Proof/Ecdsa/X86/<Curve>/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.HmacTable.X86 (HVar)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition of `vg_ecdsa_<curve>_verify` reads no memory on
return. -/
theorem verifyHashOut (J : Spec.Ecdsa.Instance) (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (J.verifyHashContract (X86.abi.withConsts cs) stack) (J.verifyHashSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    exact h

/-- The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return
only within `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List HVar) :
    PostOut (Rfc6979.X86.specK T cs vs) (T.signSig.retBits 32) :=
  postOut_of_local ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [out, d, dg, dl, sc, hm], _ =>
      simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
        forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
      intro H F h1 h2
      have h' := h H F h1 h2
      revert h'
      split
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩
      · exact fun h' => ⟨h'.1, e.trans h'.2⟩

/-- `Rfc6979.X86.cfgT` of a curve given by the fields its code reads, which
mention none of the curve's proofs: what each curve's `signSide` evaluates. -/
def cfgOf (E : Impl.Ecdsa.X86.Cfg) (big : Bool) (sh : Nat) (coreN : String) (coreC : Prog isa)
    (tries : Nat) (vs : List HVar) : Impl.Ecdsa.Rfc6979.X86.Cfg where
  f := HmacTable.X86.fnsOf vs
  w := 2 * E.n - (if E.C.len = 28 then 1 else 0)
  len := E.C.len
  big := big
  sh := sh
  n := E.C.n
  tries := tries
  coreN := coreN
  coreC := coreC

/-- `scrubFSide` of `vg_ecdsa_<curve>_sign`'s code from that of the code of
`cfgOf`, which the kernel evaluates without the curve's proofs. -/
theorem signSide_of {R : Rfc6979.X86.RfcCurve} {tries : Nat} {vs : List HVar}
    {ts : List (String × List FnTable)} {W : Nat}
    (h : scrubFSide (Impl.Ecdsa.Rfc6979.X86.signCode (cfgOf R.E R.big R.sh R.coreN R.coreC tries vs)) ts W = true) :
    scrubFSide (Rfc6979.X86.signCodeT R tries vs) ts W = true := h

end VG.Proof.Ecdsa.X86.Scrub

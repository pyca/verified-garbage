module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.SignP
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PSS on PPC64LE, without secret residue

`vg_rsa_pss_verify_precomputed` and `vg_rsa_pss_sign_precomputed`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`),
which clears the volatile registers each may write and zeroes the stack
their frames used. Each is generic over the hash functions its tables hold,
which it calls indirectly: those are the tables' functions, whose addresses
two runs agree on (`PPC64LE.Scrub.tablesCall`). Their postconditions read
the memory on return only within `out`: verification not at all, signing
the signature, given that `out` holds `n_len` bytes, as on AArch64
(`Proof/RsaPss/AArch64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Rsa.PPC64LE.Scrub
open VG.Proof.MdHashTable.PPC64LE (mvars tables fnsOf fns3)
open VG.Proof.RsaPss.PPC64LE (OK verify_ok' signP_ok')

/-! ## Postconditions -/

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

theorem signOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.signPrecomputedMdTableSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
        m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp,
        Elem.size] at hb
      change @Curry.apply (Mem → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol : (outLen.setWidth 64).toNat = (nLen.setWidth 64).toNat := hp.2.1
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hol
      have e' : Spec.Rsa.bytesAt m₂ out (nLen.setWidth 64).toNat =
          Spec.Rsa.bytesAt m₁ out (nLen.setWidth 64).toNat :=
        e _ (by rw [BitVec.setWidth_eq]; exact hol.symm)
      exact fun H G h1 h2 => writtenOutcome_of e' (h H G h1 h2)

theorem verifyOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

/-! ## The registrations -/

/-- `Spec.RsaPss.verifyPrecomputedMdTableApi`, with the tables of every hash
function. -/
def verifyReg (h : OK mvars mvars) :
    Registration Spec.RsaPss.verifyPrecomputedMdTableApi PPC64LE.target :=
  scrubOf {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaPss.PPC64LE.verifyPrecomputed (fnsOf mvars) (fns3 mvars)
      verified := verify_ok' h }
    304 .all
    (verifyOut _ _ _)
    (by dsimp only; lit_decide)

/-- `Spec.RsaPss.signPrecomputedMdTableApi`, with the tables of every hash
function. -/
def signReg (h : OK mvars mvars) :
    Registration Spec.RsaPss.signPrecomputedMdTableApi PPC64LE.target :=
  scrubOf {
      tables := [("hash", tables mvars), ("mgf1", tables mvars)]
      code := Impl.RsaPss.PPC64LE.Sign.signP (fnsOf mvars) (fns3 mvars)
      verified := signP_ok' h }
    3792 .all
    (signOut _ _ _)
    (by dsimp only; lit_decide)

end VG.Proof.RsaPss.PPC64LE.Scrub

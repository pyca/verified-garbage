module

public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha256.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_sha256_init` and `vg_sha224_init` on x86-64, without secret residue

Each followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`),
which clears the registers it writes. Their postconditions read the memory
on return only within the streaming state (`Stream.reprFrom_congr`).
HMAC, PBKDF2, DSA and RSA call their code as the internal
`vg_sha256_init_core` and `vg_sha224_init_core`
(`Proof.Pbkdf2.Md.X86_64.Sha256.hash`, `Proof.Pbkdf2.Md.X86_64.Sha224.hash`),
which clear what they leave themselves.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64

open VG.X86_64 VG.X86_64.Scrub

theorem initOut (iv : Spec.Sha256.HashValue)
    (K : Contract isa) (hK : K = Spec.Sha256.initSig.contract X86_64.abi
      (post := fun state _ m' _ => Spec.Sha256.ReprFrom iv m' state [])) :
    PostOut K (Spec.Sha256.initSig.retBits 64) := by
  subst hK
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Sha256.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq] at hb
    exact Stream.reprFrom_congr (fun i hi => (hb _ (Offset.contains_base _
      (by simp only [Elem.size]; omega) (by omega))).symm) h

def initKs : List Nat := keep_for% Spec.Sha256.initApi.sig 0 Impl.Sha256.X86_64.Stream.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha256.initApi.sig 0 []) (Impl.Sha256.X86_64.Stream.init)
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha256_init`. -/
def initReg : Registration Spec.Sha256.initApi X86_64.target :=
  withScrub { code := Impl.Sha256.X86_64.Stream.init, verified := Shared.init } (initOut Spec.Sha256.H0 _ rfl) []
    (pubOk_nil _) (some ⟨initKs, initOk⟩)

def init224Ks : List Nat := keep_for% Spec.Sha256.init224Api.sig 0 Impl.Sha256.X86_64.Stream.init224 []

theorem init224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha256.init224Api.sig 0 []) (Impl.Sha256.X86_64.Stream.init224)
      h).any (RScrub.resOkB · 0 init224Ks (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of init224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_sha224_init`. -/
def init224Reg : Registration Spec.Sha256.init224Api X86_64.target :=
  withScrub { code := Impl.Sha256.X86_64.Stream.init224, verified := Shared.init224 } (initOut Spec.Sha256.H0_224 _ rfl) []
    (pubOk_nil _) (some ⟨init224Ks, init224Ok⟩)

end VG.Proof.Sha256.X86_64

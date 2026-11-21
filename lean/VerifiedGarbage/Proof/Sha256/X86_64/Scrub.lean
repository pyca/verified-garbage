module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubSel
public import VerifiedGarbage.Impl.Sha256.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
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

Each followed by `Impl.Scrub.X86_64.scrubSel`
(`X86_64.Scrub.verifiedScrubbedSel`), which clears every caller-saved register
and the granules of its stack the residue analysis finds may hold secrets. Their
postconditions read the memory on return only within the streaming state
(`Stream.reprFrom_congr`). HMAC, PBKDF2, DSA and RSA call their code as the
internal `vg_sha256_init_core` and `vg_sha224_init_core`
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
      (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm) h

/-! ## The functions as emitted -/

theorem init_codeSp : (Impl.Sha256.X86_64.Stream.init).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha256.initApi`'s function as emitted (`Impl.Sha256.X86_64.Fn.init`) meets its contract in
constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sha256.X86_64.Fn.init (Spec.Sha256.initApi.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha256.initApi)
    { code := Impl.Sha256.X86_64.Stream.init
      verified := Shared.init
      spSafe := init_codeSp }
    .sse [] (initOut Spec.Sha256.H0 _ rfl) (RScrub.pubOk_nil _) (by taint_decide)

theorem init_spSafe : Impl.Sha256.X86_64.Fn.init.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init_codeSp

theorem init224_codeSp : (Impl.Sha256.X86_64.Stream.init224).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Sha256.init224Api`'s function as emitted (`Impl.Sha256.X86_64.Fn.init224`) meets its contract in
constant time and returns without secret residue. -/
theorem init224_scrubbed :
    VerifiedScrubbed target Impl.Sha256.X86_64.Fn.init224 (Spec.Sha256.init224Api.contract X86_64.abi 0) 0 :=
  verifiedScrubbedSel (api := Spec.Sha256.init224Api)
    { code := Impl.Sha256.X86_64.Stream.init224
      verified := Shared.init224
      spSafe := init224_codeSp }
    .sse [] (initOut Spec.Sha256.H0_224 _ rfl) (RScrub.pubOk_nil _) (by taint_decide)

theorem init224_spSafe : Impl.Sha256.X86_64.Fn.init224.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe init224_codeSp
end VG.Proof.Sha256.X86_64

module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Scrub
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Scrub
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20's `init` and `set_nonce` without secret residue (x86-64)

`vg_chacha20_init` and `vg_chacha20_set_nonce`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers that the residue analysis (`X86_64.RTaint`) finds may hold
secrets. Their postconditions read the memory on return only within the
streaming state (`Scrub.stream_congr`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Spec.ChaCha20

theorem initOut : PostOut (initContract X86_64.abi) (initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    obtain ⟨hk, hr, -⟩ := stream_congr hs
    show keyAt m₂ st = _ ∧ restAt m₂ st = _
    rw [hk, hr]; exact h

theorem setNonceOut : PostOut (setNonceContract X86_64.abi) (setNonceSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [setNonceSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    obtain ⟨hk, hr, -⟩ := stream_congr hs
    show keyAt m₂ st = _ ∧ restAt m₂ st = _
    rw [hk, hr]; exact h

def initKs : List Nat := keep_for% initApi.sig 0 Impl.ChaCha20.X86_64.Stream.init []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init initApi.sig 0 []) Impl.ChaCha20.X86_64.Stream.init
      h).any (RScrub.resOkB · 0 initKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

def setNonceKs : List Nat := keep_for% setNonceApi.sig 0 Impl.ChaCha20.X86_64.Stream.setNonce []

theorem setNonceOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init setNonceApi.sig 0 []) Impl.ChaCha20.X86_64.Stream.setNonce
      h).any (RScrub.resOkB · 0 setNonceKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of setNonceKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_chacha20_init`. -/
def initReg : Registration initApi X86_64.target :=
  withScrub { code := Impl.ChaCha20.X86_64.Stream.init, verified := Stream.init_verified } initOut []
    (pubOk_nil _) (some ⟨initKs, initOk⟩)

open VG.X86_64.RScrub in
/-- `vg_chacha20_set_nonce`. -/
def setNonceReg : Registration setNonceApi X86_64.target :=
  withScrub { code := Impl.ChaCha20.X86_64.Stream.setNonce, verified := Stream.setNonce_verified }
    setNonceOut [] (pubOk_nil _) (some ⟨setNonceKs, setNonceOk⟩)

end VG.Proof.ChaCha20.X86_64.Scrub

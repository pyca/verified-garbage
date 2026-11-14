module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out

/-!
# Deterministic ECDSA on x86-64: the postcondition local to the buffers

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return
only within `out` (`X86_64.Scrub.PostOut`), for any tables of constants,
tables of `hmac` and stack, as `X86_64.Scrub.withScrubAllUp` needs to scrub
its implementations.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG.X86_64 VG.X86_64.Scrub

/-- `TableInstance.signContract`'s postcondition reads the memory on return
only in `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (ts : List FnTable) (stack : Nat) :
    PostOut (T.signContract ((X86_64.abi.withConsts cs).withTables T.signSig [("hmac", ts)]) stack)
      (T.signSig.retBits ((X86_64.abi.withConsts cs).withTables T.signSig [("hmac", ts)]).ptrBits) :=
  postOut_of_local (leak := some _) ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨hm, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have e := EcKey.X86_64.Scrub.bytesAt_congr (n := 2 * T.ecdsa.curve.len) (by simp only [Elem.size]; omega)
      hb.1
    intro H F hH hF
    have h := h H F hH hF
    revert h
    split <;> exact fun h => ⟨h.1, e.trans h.2⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

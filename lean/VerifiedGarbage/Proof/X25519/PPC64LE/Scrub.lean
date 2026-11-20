module

public import VerifiedGarbage.Impl.X25519.PPC64LE.Fn
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Proof.X25519.PPC64LE.BaseVerified
public import VerifiedGarbage.Proof.X25519.PPC64LE.Exchange
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit

/-!
# X25519 on PPC64LE, without secret residue

`vg_x25519_exchange` and `vg_x25519_base`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers they write and the stack their frames use (the 48 bytes
of the exchange's frame; the base has none). Their postconditions read the
memory on return only within `out` (`PPC64LE.Scrub.PostOut`), whatever
tables of constants their code takes, by RISC-V's proofs
(`Proof/X25519/RISCV64/Scrub.lean`). `scrubOf`'s side condition
(`scrubSide`) is proved at each registration, by the kernel's evaluation of
it when this module is built.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

/-- The 32 bytes at `o` read the memory only within `⟨o, n⟩`, for `32 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 32 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X25519.bytesAt m₂ o 32 = Spec.X25519.bytesAt m₁ o 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.x25519BaseContract (PPC64LE.abi.withConsts cs) stack) (Spec.X25519.x25519BaseSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.x25519BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

theorem exchangeOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.exchangeContract (PPC64LE.abi.withConsts cs) stack) (Spec.X25519.exchangeSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X25519.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X25519.bytesAt m₂ o 32 = _ ∧ _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

/-! ## The functions as emitted -/

/-- `vg_x25519_exchange` as emitted (`Impl.X25519.PPC64LE.Fn.exchange`) meets its
contract in constant time and returns without secret residue. -/
theorem exchange_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.X25519.PPC64LE.Fn.exchange
      (Spec.X25519.exchangeContract PPC64LE.abi 48) 32 :=
  verifiedScrubbedAll (api := Spec.X25519.exchangeApi) {
      code := Impl.Xdh.PPC64LE.exchange "vg_x25519" Impl.X25519.PPC64LE.Fe51.x25519 32
      verified := Proof.X25519.PPC64LE.Exchange.exchange_verified }
    48 ⟨true, true, [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (exchangeOut [] _)
    (by dsimp only; lit_decide)

/-- `vg_x25519_base` as emitted (`Impl.X25519.PPC64LE.Fn.base`) meets its contract
in constant time and returns without secret residue. -/
theorem base_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.X25519.PPC64LE.Fn.base
      (Spec.X25519.x25519BaseContract (PPC64LE.abi.withConsts Impl.Ed25519.PPC64LE.combConsts)) 0 :=
  verifiedScrubbedAll (api := Spec.X25519.x25519BaseApi) {
      code := Impl.X25519.PPC64LE.Base.x25519Base
      verified := Proof.X25519.PPC64LE.Base.x25519Base_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (baseOut Impl.Ed25519.PPC64LE.combConsts _)
    (by dsimp only; lit_decide)

end VG.Proof.X25519.PPC64LE.Scrub

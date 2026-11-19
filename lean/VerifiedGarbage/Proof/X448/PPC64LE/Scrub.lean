module

public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Proof.X448.PPC64LE.Exchange
import VerifiedGarbage.Proof.X448.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit

/-!
# X448 on PPC64LE, without secret residue

`vg_x448_exchange` and `vg_x448_base`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers they write and the stack their frames use (the 48 bytes
of the exchange's frame; the base has none). Their postconditions read the
memory on return only within `out` (`PPC64LE.Scrub.PostOut`), whatever
tables of constants their code takes, by RISC-V's proofs
(`Proof/X448/RISCV64/Scrub.lean`). `scrubOf`'s side condition
(`scrubSide`) is proved at each registration, by the kernel's evaluation of
it when this module is built.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Postconditions -/

/-- The 56 bytes at `o` read the memory only within `⟨o, n⟩`, for `56 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 56 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X448.bytesAt m₂ o 56 = Spec.X448.bytesAt m₁ o 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X448.x448BaseContract (PPC64LE.abi.withConsts cs) stack) (Spec.X448.x448BaseSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.x448BaseSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

theorem exchangeOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X448.exchangeContract (PPC64LE.abi.withConsts cs) stack) (Spec.X448.exchangeSig.retBits 64) :=
  postOut_of_local (leak := none) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨u, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.X448.bytesAt m₂ o 56 = _ ∧ _
    rw [bytesAt_of (by simp only [Elem.size]; omega_using []) hb.1]; exact h

/-! ## The registrations -/

/-- `Spec.X448.exchangeApi`. -/
def exchangeReg : Registration Spec.X448.exchangeApi PPC64LE.target :=
  scrubOf {
      code := Impl.Xdh.PPC64LE.exchange "vg_x448" Impl.X448.PPC64LE.x448 56
      verified := Proof.X448.PPC64LE.Exchange.exchange_verified }
    48 ⟨true, true, [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (exchangeOut [] _)
    (by dsimp only; lit_decide)

/-- `Spec.X448.x448BaseApi`. -/
def baseReg : Registration Spec.X448.x448BaseApi PPC64LE.target :=
  scrubOf {
      code := Impl.X448.PPC64LE.x448Base
      verified := Proof.X448.PPC64LE.x448Base_verified }
    0 ⟨true, false, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (baseOut [] _)
    (by dsimp only; lit_decide)

end VG.Proof.X448.PPC64LE.Scrub

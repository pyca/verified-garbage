module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Verified
public import VerifiedGarbage.Proof.X25519.RISCV64.BaseVerified
public import VerifiedGarbage.Proof.X25519.RISCV64.Exchange
public import VerifiedGarbage.Impl.X25519.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on RISC-V, without secret residue

`vg_x25519_base` and `vg_x25519_exchange` as emitted (`Impl.X25519.RISCV64.Fn`), each
followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the caller-saved registers and the
stack its frames used: the theorems their registrations bind
(`RISCV64.Scrub.verifiedScrubbed`). Their postconditions read the memory on return only
within `out` (`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/X25519/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

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
    PostOut (Spec.X25519.x25519BaseContract (RISCV64.abi.withConsts cs) stack) (Spec.X25519.x25519BaseSig.retBits 64) :=
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
    PostOut (Spec.X25519.exchangeContract (RISCV64.abi.withConsts cs) stack) (Spec.X25519.exchangeSig.retBits 64) :=
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

/-- `vg_x25519_exchange` as emitted (`Impl.X25519.RISCV64.Fn.exchange`) meets its contract in
constant time and returns without secret residue: the theorem its registration binds. -/
theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.X25519.RISCV64.Fn.exchange
      (Spec.X25519.exchangeContract RISCV64.abi 16) 32 :=
  verifiedScrubbed (api := Spec.X25519.exchangeApi) (W := 16)
    { code := Impl.Xdh.RISCV64.exchange "vg_x25519" Impl.X25519.RISCV64.R64.x25519 32
      verified := Proof.X25519.RISCV64.Exchange.exchange_verified }
    (exchangeOut [] _) (by lit_decide)

/-- `vg_x25519_base` as emitted (`Impl.X25519.RISCV64.Fn.base`) meets its contract in constant
time and returns without secret residue: the theorem its registration binds. -/
theorem base_scrubbed :
    VerifiedScrubbed target Impl.X25519.RISCV64.Fn.base
      (Spec.X25519.x25519BaseContract (RISCV64.abi.withConsts Impl.Ed25519.RISCV64.combConsts)) 0 :=
  verifiedScrubbed (api := Spec.X25519.x25519BaseApi) (W := 0)
    { code := Impl.X25519.RISCV64.Base.x25519Base
      verified := Proof.X25519.RISCV64.Base.x25519Base_verified }
    (baseOut Impl.Ed25519.RISCV64.combConsts 0) (by lit_decide)

end VG.Proof.X25519.RISCV64.Scrub

module

import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Ifma
import VerifiedGarbage.Proof.X25519.X86_64.Base.Adx
public import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Exchange
public import VerifiedGarbage.Impl.Xdh.X86_64
public import VerifiedGarbage.Impl.X25519.X86_64.Base
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on x86-64, without secret residue

The postconditions of `vg_x25519_base` and `vg_x25519_exchange` read the
memory on return only within `out` (`X86_64.Scrub.PostOut`), whatever tables
of constants the code takes: each implementation returns with its whole
stack wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-- The 32 bytes at `o` read the memory only within `⟨o, n⟩`, for `32 ≤ n`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} (hn : 32 ≤ n)
    (h : ∀ a, Region.Contains ⟨o, n⟩ a 1 → m₁ a = m₂ a) :
    Spec.X25519.bytesAt m₂ o 32 = Spec.X25519.bytesAt m₁ o 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [this]))).symm

theorem baseOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts cs) stack) (Spec.X25519.x25519BaseSig.retBits 64) :=
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
    PostOut (Spec.X25519.exchangeContract (X86_64.abi.withConsts cs) stack) (Spec.X25519.exchangeSig.retBits 64) :=
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

theorem exchangeIfma_codeSp : (Impl.Xdh.X86_64.exchange "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_exchange_ifma` as emitted (`Impl.Xdh.X86_64.Fn.exchangeEvex`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem exchangeIfma_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.Xdh.X86_64.Fn.exchangeEvex "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32)
      (Spec.X25519.exchangeApi.contract X86_64.abi 24) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.exchangeApi)
    { code := Impl.Xdh.X86_64.exchange "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32
      stack := 24
      verified := Proof.X25519.X86_64.Exchange.exchange_ifma
      spSafe := exchangeIfma_codeSp } .evex (exchangeOut [] 24)

theorem exchangeIfma_spSafe : (Impl.Xdh.X86_64.Fn.exchangeEvex "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe exchangeIfma_codeSp

theorem exchangeAdx_codeSp : (Impl.Xdh.X86_64.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_exchange_adx` as emitted (`Impl.Xdh.X86_64.Fn.exchange`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem exchangeAdx_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.Xdh.X86_64.Fn.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32)
      (Spec.X25519.exchangeApi.contract X86_64.abi 24) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.exchangeApi)
    { code := Impl.Xdh.X86_64.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32
      stack := 24
      verified := Proof.X25519.X86_64.Exchange.exchange_adx
      spSafe := exchangeAdx_codeSp } .sse (exchangeOut [] 24)

theorem exchangeAdx_spSafe : (Impl.Xdh.X86_64.Fn.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe exchangeAdx_codeSp

theorem exchange_codeSp : (Impl.Xdh.X86_64.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_exchange` as emitted (`Impl.Xdh.X86_64.Fn.exchange`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem exchange_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.Xdh.X86_64.Fn.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32)
      (Spec.X25519.exchangeApi.contract X86_64.abi 24) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.exchangeApi)
    { code := Impl.Xdh.X86_64.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32
      stack := 24
      verified := Proof.X25519.X86_64.Exchange.exchange_baseline
      spSafe := exchange_codeSp } .sse (exchangeOut [] 24)

theorem exchange_spSafe : (Impl.Xdh.X86_64.Fn.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe exchange_codeSp

theorem baseIfma_codeSp : (Impl.X25519.X86_64.Base.x25519BaseIfma).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_base_ifma` as emitted (`Impl.X25519.X86_64.Base.Fn.x25519BaseIfma`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem baseIfma_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.X25519.X86_64.Base.Fn.x25519BaseIfma)
      (Spec.X25519.x25519BaseApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 8) 0 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.x25519BaseApi)
    { code := Impl.X25519.X86_64.Base.x25519BaseIfma
      stack := 8
      verified := Proof.X25519.X86_64.Base.x25519BaseIfma_verified
      spSafe := baseIfma_codeSp } .avx (baseOut Impl.Ed25519.X86_64.combConsts 8)

theorem baseIfma_spSafe : (Impl.X25519.X86_64.Base.Fn.x25519BaseIfma).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe baseIfma_codeSp

theorem baseAdx_codeSp : (Impl.X25519.X86_64.Base.x25519BaseAdx).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_base_adx` as emitted (`Impl.X25519.X86_64.Base.Fn.x25519BaseAdx`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem baseAdx_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.X25519.X86_64.Base.Fn.x25519BaseAdx)
      (Spec.X25519.x25519BaseApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 8) 0 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.x25519BaseApi)
    { code := Impl.X25519.X86_64.Base.x25519BaseAdx
      stack := 8
      verified := Proof.X25519.X86_64.Base.x25519BaseAdx_verified
      spSafe := baseAdx_codeSp } .avx (baseOut Impl.Ed25519.X86_64.combConsts 8)

theorem baseAdx_spSafe : (Impl.X25519.X86_64.Base.Fn.x25519BaseAdx).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe baseAdx_codeSp

theorem base_codeSp : (Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.baseline).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_x25519_base` as emitted (`Impl.X25519.X86_64.Base.Fn.x25519Base`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem base_scrubbed [VG.Proof.X25519.X86_64.DivstepInv] :
    VerifiedScrubbed X86_64.target (Impl.X25519.X86_64.Base.Fn.x25519Base)
      (Spec.X25519.x25519BaseApi.contract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts) 8) 0 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.X25519.x25519BaseApi)
    { code := Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.baseline
      stack := 8
      verified := Proof.X25519.X86_64.Base.x25519Base_verified (fld := Impl.X25519.X86_64.baseline)
      spSafe := base_codeSp } .sse (baseOut Impl.Ed25519.X86_64.combConsts 8)

theorem base_spSafe : (Impl.X25519.X86_64.Base.Fn.x25519Base).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe base_codeSp


end VG.Proof.X25519.X86_64.Scrub

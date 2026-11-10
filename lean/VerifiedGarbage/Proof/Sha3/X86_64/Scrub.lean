module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.X86_64.Instances
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.X86_64.Instances
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

/-!
# SHA-3 and SHAKE's functions on x86-64, without secret residue

Each instance's `update`, and SHAKE's `finalize` and `squeeze`, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the state
(`Proof.Sha3.stateAt_congr`) and the output (`bytesAt_congr`).

SHA-3's `finalize` is not here: the analysis loses that `r12` points into
its frame across its call of `squeeze` (whose stores to `out` it cannot
bound), so it cannot follow `finRestore`'s loads through it.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Scrub

open VG.Spec.Sha3 VG.X86_64 VG.X86_64.Scrub

theorem agreeBuf {m₁ m₂ : Mem} {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := fun i hi =>
  (h _ (Offset.contains_base _ (by omega) (by omega))).symm

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem stateAgree {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ a, Region.Contains ⟨p, 25 * Elem.size .u64⟩ a 1 → m₁ a = m₂ a) :
    stateAt m₂ p = stateAt m₁ p :=
  Proof.Sha3.stateAt_congr fun i hi =>
    agreeBuf (n := 25 * Elem.size .u64) (by decide) h i (by simp only [Elem.size]; omega)

theorem updateOut (rate stack : Nat) :
    PostOut (updateContract X86_64.abi rate stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    refine ⟨fun msg hr hc => ?_, h.2⟩
    show stateAt m₂ st = _
    rw [stateAgree hb.1]
    exact h.1 msg hr hc

theorem xofFinalizeOut (X : Xof) (stack : Nat) :
    PostOut (xofFinalizeContract X86_64.abi X stack) (xofFinalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 1) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [xofFinalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hb
    intro msg hr hc d
    show squeezeFrom X.rate (stateAt m₂ st) 0 d = _
    rw [stateAgree hb]
    exact h msg hr hc d

theorem xofSqueezeOut (X : Xof) (stack : Nat) :
    PostOut (xofSqueezeContract X86_64.abi X stack) (xofSqueezeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ps, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ol, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [xofSqueezeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    refine ⟨fun msg n hx => ?_, h.2⟩
    obtain ⟨h1, h2⟩ := h.1 msg n hx
    refine ⟨?_, fun d => ?_⟩
    · show bytesAt m₂ ot ol.toNat = _
      rw [bytesAt_congr fun i hi => agreeBuf (n := ol.toNat * Elem.size .u8)
        (by simp only [Elem.size]; have := ol.isLt; omega) hb.2 i
        (by simp only [Elem.size]; omega)]
      exact h1
    · show squeezeFrom X.rate (stateAt m₂ st) _ d = _
      rw [stateAgree hb.1]
      exact h2 d

/-! ## The registrations -/
def updateSha3_224Ks : List Nat := keep_for% Spec.Sha3.updateSha3_224Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate) []

theorem updateSha3_224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_224Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate)
      h).any (RScrub.resOkB · 8 updateSha3_224Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_224Api`'s function. -/
def updateSha3_224Reg : Registration Spec.Sha3.updateSha3_224Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_224 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_224Ks, updateSha3_224Ok⟩)
def updateSha3_256Ks : List Nat := keep_for% Spec.Sha3.updateSha3_256Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate) []

theorem updateSha3_256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_256Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate)
      h).any (RScrub.resOkB · 8 updateSha3_256Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_256Api`'s function. -/
def updateSha3_256Reg : Registration Spec.Sha3.updateSha3_256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_256 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_256Ks, updateSha3_256Ok⟩)
def updateSha3_384Ks : List Nat := keep_for% Spec.Sha3.updateSha3_384Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate) []

theorem updateSha3_384Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_384Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate)
      h).any (RScrub.resOkB · 8 updateSha3_384Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_384Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_384Api`'s function. -/
def updateSha3_384Reg : Registration Spec.Sha3.updateSha3_384Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_384 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_384Ks, updateSha3_384Ok⟩)
def updateSha3_512Ks : List Nat := keep_for% Spec.Sha3.updateSha3_512Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate) []

theorem updateSha3_512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_512Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate)
      h).any (RScrub.resOkB · 8 updateSha3_512Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_512Api`'s function. -/
def updateSha3_512Reg : Registration Spec.Sha3.updateSha3_512Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_512 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_512Ks, updateSha3_512Ok⟩)
def updateShake128Ks : List Nat := keep_for% Spec.Sha3.updateShake128Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate) []

theorem updateShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateShake128Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 8 updateShake128Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateShake128Api`'s function. -/
def updateShake128Reg : Registration Spec.Sha3.updateShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_shake128 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateShake128Ks, updateShake128Ok⟩)
def finalizeShake128Ks : List Nat := keep_for% Spec.Sha3.finalizeShake128Api.sig 656 (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate) []

theorem finalizeShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.finalizeShake128Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 656 finalizeShake128Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of finalizeShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `finalizeShake128Api`'s function. -/
def finalizeShake128Reg : Registration Spec.Sha3.finalizeShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake128 } (xofFinalizeOut _ _) [] (pubOk_nil _)
    (some ⟨finalizeShake128Ks, finalizeShake128Ok⟩)
def squeezeShake128Ks : List Nat := keep_for% Spec.Sha3.squeezeShake128Api.sig 656 (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate) []

theorem squeezeShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.squeezeShake128Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 656 squeezeShake128Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of squeezeShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `squeezeShake128Api`'s function. -/
def squeezeShake128Reg : Registration Spec.Sha3.squeezeShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake128 } (xofSqueezeOut _ _) [] (pubOk_nil _)
    (some ⟨squeezeShake128Ks, squeezeShake128Ok⟩)
def finalizeShake256Ks : List Nat := keep_for% Spec.Sha3.finalizeShake256Api.sig 656 (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate) []

theorem finalizeShake256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.finalizeShake256Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate)
      h).any (RScrub.resOkB · 656 finalizeShake256Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of finalizeShake256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `finalizeShake256Api`'s function. -/
def finalizeShake256Reg : Registration Spec.Sha3.finalizeShake256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake256 } (xofFinalizeOut _ _) [] (pubOk_nil _)
    (some ⟨finalizeShake256Ks, finalizeShake256Ok⟩)
def squeezeShake256Ks : List Nat := keep_for% Spec.Sha3.squeezeShake256Api.sig 656 (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate) []

theorem squeezeShake256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.squeezeShake256Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate)
      h).any (RScrub.resOkB · 656 squeezeShake256Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of squeezeShake256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `squeezeShake256Api`'s function. -/
def squeezeShake256Reg : Registration Spec.Sha3.squeezeShake256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake256 } (xofSqueezeOut _ _) [] (pubOk_nil _)
    (some ⟨squeezeShake256Ks, squeezeShake256Ok⟩)

end VG.Proof.Sha3.X86_64.Scrub

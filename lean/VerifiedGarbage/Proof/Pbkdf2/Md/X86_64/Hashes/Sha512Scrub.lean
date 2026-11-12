module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on x86-64, without secret residue

What `StreamFn.scrub` needs of their streaming and one-shot functions
beyond their code: their postconditions read the memory on return only
within the buffers (`X86_64.Scrub.PostOut`). Each variant scrubs them with
the granules the residue analysis of its own code selects
(`Proof/Variants/MdHash/X86_64/Sha512*.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512

open VG.Spec.Sha512

/-! The streaming state (`repr_congr`) and the digest (`Stream.bytesAt_congr`)
are bytes of the function's buffers. -/

theorem updatePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs (updateSig).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro iv msg hr hc
  exact Stream.repr_congr hs (h iv msg hr hc)

theorem finalizePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs (finalizeSig).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₁ r →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < 64, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro iv msg hr hl hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h iv msg hr hl hc)

theorem finalizeDigestPost_out (iv : HashValue) (D : Nat) (digest : List Byte → List Byte) (pb : Nat)
    (hD : D < 2 ^ 64) : ∀ vs m m₁ m₂ r, vs.length = ((finalizeDigestSig D).words pb).length →
    (∀ b ∈ Sig.bufs ((finalizeDigestSig D)).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((finalizeDigestSig D).words pb) (finalizeDigestPost iv D digest pb) vs m m₁ r →
      Curry.apply ((finalizeDigestSig D).words pb) (finalizeDigestPost iv D digest pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeDigestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < D, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  intro msg hr hl hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h msg hr hl hc)

theorem digestPost_out (D : Nat) (digest : List Byte → List Byte) (pb : Nat) (hD : D < 2 ^ 64) : ∀ vs m m₁ m₂ r, vs.length = ((digestSig D).words pb).length →
    (∀ b ∈ Sig.bufs ((digestSig D)).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₁ r →
      Curry.apply ((digestSig D).words pb) (digestPost D digest pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [digestSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < D, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
  show bytesAt m₂ ot D = _
  rw [Stream.bytesAt_congr ho]
  exact h

end VG.Proof.Sha512

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Sha512.X86_64 (Compress)
open Spec.Sha512 (H0_384 H0_512_224 H0_512_256)

theorem updOut (v : Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out 64)

theorem finOut (v : Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out 64)

theorem digOut (v : Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide))

theorem fin384Out (v : Compress) : PostOut (fin384Fn v).contract (fin384Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_384 48 Spec.Sha512.sha384 64 (by decide))

theorem dig384Out (v : Compress) : PostOut (dig384Fn v).contract (dig384Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide))

theorem fin512_256Out (v : Compress) : PostOut (fin512_256Fn v).contract (fin512_256Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_256 32 Spec.Sha512.sha512_256 64 (by decide))

theorem dig512_256Out (v : Compress) : PostOut (dig512_256Fn v).contract (dig512_256Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide))

theorem fin512_224Out (v : Compress) : PostOut (fin512_224Fn v).contract (fin512_224Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_224 28 Spec.Sha512.sha512_224 64 (by decide))

theorem dig512_224Out (v : Compress) : PostOut (dig512_224Fn v).contract (dig512_224Fn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide))

section S
variable (v : Compress) {so : Nat} (h : so = 0 ∨ so = 192)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha512.compressWideX86_64S so))

theorem updOutS : PostOut (updFnS v h hv).contract (updFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out 64)

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 64 (by decide))

theorem fin384OutS : PostOut (fin384FnS v h hv).contract (fin384FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_384 48 Spec.Sha512.sha384 64 (by decide))

theorem dig384OutS : PostOut (dig384FnS v h hv).contract (dig384FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 64 (by decide))

theorem fin512_256OutS : PostOut (fin512_256FnS v h hv).contract (fin512_256FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_256 32 Spec.Sha512.sha512_256 64 (by decide))

theorem dig512_256OutS : PostOut (dig512_256FnS v h hv).contract (dig512_256FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 64 (by decide))

theorem fin512_224OutS : PostOut (fin512_224FnS v h hv).contract (fin512_224FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.finalizeDigestPost_out H0_512_224 28 Spec.Sha512.sha512_224 64 (by decide))

theorem dig512_224OutS : PostOut (dig512_224FnS v h hv).contract (dig512_224FnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain
    (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha512

module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-224's and SHA-256's streaming and one-shot functions on x86-64, without secret residue

What `StreamFn.scrub` needs of SHA-256's `updFn`, `finFn` and `digFn`, and
SHA-224's `finFn` and `digFn`, beyond their code: their postconditions read
the memory on return only within the buffers (`X86_64.Scrub.PostOut`). Each variant
(`Proof/Variants/MdHash/X86_64/Sha256*.lean`) scrubs them with the granules
the residue analysis of its own code selects.
-/

@[expose] public section

namespace VG.Proof.Sha256

open VG.Spec.Sha256

/-! The streaming state (`reprFrom_congr`) and the digest
(`Stream.bytesAt_congr`) are bytes of the function's buffers. -/

theorem updatePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
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
  have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  intro iv msg hr hc
  exact reprFrom_congr hs (h iv msg hr hc)

theorem finalizePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
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
  have ho : ∀ i < 32, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  intro iv msg hr hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h iv msg hr hc)

theorem finalize224Post_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalize224Sig.words pb).length →
    (∀ b ∈ Sig.bufs finalize224Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalize224Sig.words pb) (finalize224Post pb) vs m m₁ r →
      Curry.apply (finalize224Sig.words pb) (finalize224Post pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ct, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ot, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalize224Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have ho : ∀ i < 28, m₂ (ot + BitVec.ofNat 64 i) = m₁ (ot + BitVec.ofNat 64 i) := fun i hi =>
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  intro msg hr hc
  exact (Stream.bytesAt_congr (p := ArgWord.addr.ofRaw ot) ho).trans (h msg hr hc)

theorem digestPost_out (D : Nat) (digest : List Byte → List Byte) (pb : Nat) (hD : D < 2 ^ 64) :
    ∀ vs m m₁ m₂ r, vs.length = ((digestSig D).words pb).length →
    (∀ b ∈ Sig.bufs (digestSig D).params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
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
    (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hD, hi]))).symm
  show bytesAt m₂ ot D = _
  rw [Stream.bytesAt_congr ho]
  exact h

end VG.Proof.Sha256

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha256

open VG.X86_64 VG.X86_64.Scrub

theorem updOut (v : Proof.Sha256.X86_64.Compress) : PostOut (updFn v).contract (updFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64)

theorem finOut (v : Proof.Sha256.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64)

theorem digOut (v : Proof.Sha256.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide))

section S
variable (v : Proof.Sha256.X86_64.Compress) {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

theorem updOutS : PostOut (updFnS v h hv).contract (updFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64)

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha256

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha224

open VG.X86_64 VG.X86_64.Scrub

theorem finOut (v : Proof.Sha256.X86_64.Compress) : PostOut (finFn v).contract (finFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64)

theorem digOut (v : Proof.Sha256.X86_64.Compress) : PostOut (digFn v).contract (digFn v).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide))

section S
variable (v : Proof.Sha256.X86_64.Compress) {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

theorem finOutS : PostOut (finFnS v h hv).contract (finFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64)

theorem digOutS : PostOut (digFnS v h hv).contract (digFnS v h hv).retBits :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide))

end S

end VG.Proof.Pbkdf2.Md.X86_64.Sha224

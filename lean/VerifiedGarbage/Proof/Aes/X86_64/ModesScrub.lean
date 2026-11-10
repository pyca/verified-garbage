module

public import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CFB8 and AES-OCB's key setup on x86-64, without secret residue

`vg_aes_cfb8_encrypt`, `vg_aes_cfb8_decrypt` and `vg_aes_ocb_init` over an
implementation of the AES block functions (`Aes.X86_64.BlocksImpl`), each
followed by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`) where the
implementation gives the residue analysis of the instance (`cfb8EncRes`,
`cfb8DecRes`, `ocbInitRes`). Their postconditions read the memory on return
only within the buffers (`X86_64.Scrub.PostOut`): the data and the input
block, or the key context (for a key of the lengths the precondition allows).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.ModesScrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega)

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega)
  simpa using this

end

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem cfb8EncryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract X86_64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfb8DecryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesDecryptContract X86_64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ocbInitOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract X86_64.abi stack) (Spec.Ocb.initSig.retBits 64) :=
  Scrub.postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Ocb.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Ocb.KeyRepr m₁ ctx _ at h
      change Spec.Ocb.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Ocb.ctxLstar, Spec.Ocb.blockAtMem] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.Aes.X86_64

/-- `vg_aes_cfb8_encrypt` over `v`. -/
def cfb8EncryptReg (v : BlocksImpl) : Registration Spec.Cfb8.aesEncryptApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.encrypt v.enc
    stack := 8
    verified := Proof.AesCfb8.encrypt_keyed (Proof.AesCfb8.X86_64.encrypt_verified v)
    spSafe := Proof.AesCfb8.X86_64.encrypt_spSafe v } (cfb8EncryptOut _) [] (pubOk_nil _) v.cfb8EncRes

/-- `vg_aes_cfb8_decrypt` over `v`. -/
def cfb8DecryptReg (v : BlocksImpl) : Registration Spec.Cfb8.aesDecryptApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.decrypt v.enc
    stack := 8
    verified := Proof.AesCfb8.decrypt_keyed (Proof.AesCfb8.X86_64.decrypt_verified v)
    spSafe := Proof.AesCfb8.X86_64.decrypt_spSafe v } (cfb8DecryptOut _) [] (pubOk_nil _) v.cfb8DecRes

/-- `vg_aes_ocb_init` over `v`. -/
def ocbInitReg (v : BlocksImpl) : Registration Spec.Ocb.initApi X86_64.target :=
  withScrub {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init ⟨v.enc, v.dec, v.expand⟩)
    stack := 2576
    verified := Proof.AesOcb.X86_64.init_framed v
    spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.AesOcb.X86_64.init_spSafe v) }
    (ocbInitOut _) [] (pubOk_nil _) v.ocbInitRes

end VG.Proof.Aes.X86_64.ModesScrub

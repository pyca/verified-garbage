module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM's key setup on x86-64, without secret residue

`vg_aes_gcm_init` over an implementation of `vg_aes_ctr32`, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`) where the
implementation gives its residue analysis (`Aes.X86_64.Ctr32Impl.gcmInitRes`,
on its code `Aes.X86_64.gcmInitCode`, which is the code of `init_framed`:
`initCode_eq`). Its postcondition reads the memory on return only within the
key context, for a key of the lengths the precondition allows
(`X86_64.Scrub.PostOut`). `vg_aes_gcm_stream_init` and
`vg_aes_gcm_stream_aad` are not here, though the analysis handles them:
`vg_aes_gcm_seal_gather_prepared` calls them by name, with their code as it is.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl gcmInitCode gcmKey)

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

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

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract X86_64.abi stack) (Spec.Gcm.initSig.retBits 64) :=
  Proof.Aes.X86_64.Scrub.postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Gcm.KeyRepr m₁ ctx _ at h
      change Spec.Gcm.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

/-! ## `vg_aes_gcm_init` -/

/-- The implementations `vg_aes_gcm_init` calls with `c`: `c`, the key
expansion for the same CPUs, and no GHASH (as the registration file's). -/
def gcmOf (c : Ctr32Impl) : GcmImpl :=
  { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni,
    gh := GhashName.scalar.impl }

/-- `init_framed`'s code is `gcmInitCode`: `init` calls only the
implementation of `vg_aes_ctr32` and the key expansion. -/
theorem initCode_eq (c : Ctr32Impl) :
    Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init (gcmOf c).callees) =
      gcmInitCode c.callee c.features := by
  unfold gcmInitCode gcmKey gcmOf
  cases c.features.isEmpty <;> rfl

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_init` over `c`. -/
def initReg (c : Ctr32Impl) : Registration Spec.Gcm.initApi X86_64.target :=
  withScrub {
    suffix := c.suffix
    code := gcmInitCode c.callee c.features
    stack := 2576
    verified := initCode_eq c ▸ init_framed (gcmOf c)
    spSafe := initCode_eq c ▸ VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOf c)) }
    (initOut _) [] (pubOk_nil _) c.gcmInitRes

end VG.Proof.AesGcm.X86_64.Scrub

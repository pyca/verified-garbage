import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Poly1305 with its working space as an argument

`vg_poly1305_update` and `vg_poly1305_finalize` keep their working space in
a frame of their own (`Verified.stackScratch`), around code proved with the
working space as an argument: `updateScratchContract` is `update`'s shared
contract with a 128-byte `scratch` buffer appended, whatever it holds (and
`Spec.Poly1305.finalizeScratchContract` is `finalize`'s, which
ChaCha20-Poly1305's code calls).

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the postconditions to read the memory on entry only
within the function's buffers (`updatePost_local`, `finalizePost_local`):
the data, and the state through `Buffered`, which reads only its first 72
bytes (`buffered_congr`).
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

/-- `vg_poly1305_update` with `scratch: *mut [u64; 16]`. -/
def updateScratchSig : Sig where
  params := [("state", .array true .u64 16), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 16)]

/-- `updateContract`, whatever `scratch` is. -/
def updateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateScratchSig.contract A
    (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (stack := stack)

/-! ## Locality -/

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem bytesAt_congr_off {m₁ m₂ : Mem} {p : Addr} {d n N : Nat} (hn : d + n ≤ N)
    (h : ∀ i < N, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ (p + BitVec.ofNat 64 d) n = bytesAt m₁ (p + BitVec.ofNat 64 d) n :=
  bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

/-- A state represents a message by its first 72 bytes alone. -/
theorem buffered_congr {m₁ m₂ : Mem} {p : Addr} {key msg : List Byte}
    (h : ∀ i < 128, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hb : Buffered m₁ p key msg) : Buffered m₂ p key msg := by
  obtain ⟨⟨h0, h1, h2⟩, h3⟩ := hb
  refine ⟨⟨h0, ?_, ?_⟩, ?_⟩
  · rw [show p + 24 = p + BitVec.ofNat 64 24 from rfl, bytesAt_congr_off (N := 128) (by omega) h]
    exact h1
  · rw [bytesAt_congr fun i hi => h i (by omega)]; exact h2
  · rw [show p + 56 = p + BitVec.ofNat 64 56 from rfl,
      bytesAt_congr_off (N := 128) (by have := Nat.mod_lt msg.length (show 16 > 0 by omega); omega) h]
    exact h3

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (pb : Nat)

theorem updatePost_local : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m₁ m' r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m₂ m' r
  | [st, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (updatePost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (updatePost pb) _ m₂ m' r
    dsimp only [Curry.apply, updatePost, ArgWord.ofRaw] at h ⊢
    intro key msg hbuf hc
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h key msg (buffered_congr (fun i hi => (hs i (by omega)).symm) hbuf) hc

theorem finalizePost_local : ∀ vs m₁ m₂ m' r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₁ m' r →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₂ m' r
  | [st, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (finalizePost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (finalizePost pb) _ m₂ m' r
    dsimp only [Curry.apply, finalizePost, ArgWord.ofRaw] at h ⊢
    intro key msg hbuf hc
    exact h key msg (buffered_congr (fun i hi => (hs i (by omega)).symm) hbuf) hc

end VG.Proof.Poly1305

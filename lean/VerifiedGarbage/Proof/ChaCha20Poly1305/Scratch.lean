import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ChaCha20-Poly1305 with its working space as an argument

`vg_chacha20_poly1305_seal` and `vg_chacha20_poly1305_open` keep their
working space in a frame of their own (`Impl/StackScratch/`), around code
proved with the working space as a last argument: `sealScratchContract n`
and `openScratchContract n` are the shared contracts with an `n`-word `work`
buffer appended, whatever it holds. Each target sizes it for its code.

The frames copy the arguments passed on the stack and wipe the working space
after the code, which needs the postconditions to read the memory on entry
and on return only within the functions' buffers (`sealPost_local`,
`openPost_local`, `sealPost_out`, `openPost_out`): the key, the nonce, the
additional data, the data and the tag.
-/

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec.ChaCha20Poly1305

/-- `vg_chacha20_poly1305_seal` with `work: *mut [u64; n]`. -/
def sealScratchSig (n : Nat) : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("work", .array true .u64 n)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (sealScratchSig n).contract A
    (post := fun key nonce aad aadLen data len tag _work =>
      sealPost A.ptrBits key nonce aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_chacha20_poly1305_open` with `work: *mut [u64; n]`. -/
def openScratchSig (n : Nat) : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("data", .slice true .u8 "len"),
    ("tag", .array false .u8 16), ("work", .array true .u64 n)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (openScratchSig n).contract A
    (post := fun key nonce aad aadLen data len tag _work =>
      openPost A.ptrBits key nonce aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-! ## Locality -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Poly1305.bytesAt m₂ p n = Spec.Poly1305.bytesAt m₁ p n := by
  simp only [Spec.Poly1305.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- The `len`-byte buffer at `p`, for a length argument `l`. -/
theorem bytesAt_congr_len {pb : Nat} {m₁ m₂ : Mem} {p l : BitVec 64}
    (h : ∀ i < l.toNat, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Poly1305.bytesAt m₂ p (l.setWidth pb).toNat = Spec.Poly1305.bytesAt m₁ p (l.setWidth pb).toNat :=
  bytesAt_congr fun i hi => h i (by
    have := Nat.mod_le l.toNat (2 ^ pb)
    rw [BitVec.toNat_setWidth] at hi; omega)

variable (pb : Nat)

theorem pre_local (sig : Sig) : ∀ vs (m₁ m₂ : Mem), vs.length = (sig.words pb).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words pb) (Curry.const (fun _ => True) _) vs m₁ →
      Curry.apply (sig.words pb) (Curry.const (fun _ => True) _) vs m₂ := by
  intro vs _ _ _ _ _
  rw [Curry.apply_const]
  trivial

theorem sealPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealSig.words pb) (sealPost pb) vs m₂ m' r
  | [key, nonce, aad, al, data, len, _], m₁, m₂, m', r, _, hb, h => by
    simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₂ m' r
    dsimp only [Curry.apply, sealPost, ArgWord.ofRaw] at h ⊢
    rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
      bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := data) (agree_of hb.2.2.2.1)]
    exact h

theorem sealPost_out : ∀ vs m m₁ m₂ r, vs.length = (sealSig.words pb).length →
    (∀ b ∈ Sig.bufs sealSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealSig.words pb) (sealPost pb) vs m m₁ r →
      Curry.apply (sealSig.words pb) (sealPost pb) vs m m₂ r
  | [_, _, _, _, data, _, tag], m, m₁, m₂, r, _, hb, h => by
    simp only [sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m m₂ r
    dsimp only [Curry.apply, sealPost, ArgWord.ofRaw] at h ⊢
    rw [bytesAt_congr_len (p := data) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
    exact h

theorem openPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openSig.words pb) (openPost pb) vs m₂ m' r
  | [key, nonce, aad, al, data, len, tag], m₁, m₂, m', r, _, hb, h => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (openPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (openPost pb) _ m₂ m' r
    dsimp only [Curry.apply, openPost, ArgWord.ofRaw] at h ⊢
    rw [bytesAt_congr (agree_of hb.1), bytesAt_congr (agree_of hb.2.1),
      bytesAt_congr_len (agree_of hb.2.2.1), bytesAt_congr_len (p := data) (agree_of hb.2.2.2.1),
      bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
    exact h

theorem openPost_out : ∀ vs m m₁ m₂ r, vs.length = (openSig.words pb).length →
    (∀ b ∈ Sig.bufs openSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openSig.words pb) (openPost pb) vs m m₁ r →
      Curry.apply (openSig.words pb) (openPost pb) vs m m₂ r
  | [_, _, _, _, data, _, _], m, m₁, m₂, r, _, hb, h => by
    simp only [openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (openPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (openPost pb) _ m m₂ r
    dsimp only [Curry.apply, openPost, ArgWord.ofRaw] at h ⊢
    rw [bytesAt_congr_len (p := data) (agree_of hb.2.2.2.1)]
    exact h

end VG.Proof.ChaCha20Poly1305

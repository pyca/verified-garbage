module

public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CFB of a message's last piece, with its working space as an argument

A final function's signature (`finalSig`): a key schedule, the block at
`iv` and the `len` bytes at `data`, the same for every block cipher but
their names and sizes, and its postconditions on it (`encFinalPost`,
`decFinalPost`), which read the memory on return only within the function's
buffers (`encFinalPost_local`, `decFinalPost_local`), and the memory on entry
likewise for a cipher that reads only the schedule (`encFinalPost_inLocal`,
`decFinalPost_inLocal`, which 32-bit x86's frame needs too), as the frame that
keeps a scratch buffer on the stack needs (`Verified.stackScratchWiped`). Nothing
here depends on a cipher or a target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

/-- A final CFB function's signature: `(nk: *const [ek; nkLen], iv: *mut [u8; b], data: *mut u8, len: usize)`. -/
def finalSig (nk : String) (ek : Elem) (nkLen b : Nat) : Sig where
  params := [(nk, .array false ek nkLen), ("iv", .array true .u8 b), ("data", .slice true .u8 "len")]

variable {nk : String} {ek : Elem} {nkLen : Nat}

/-- The final encryption's postcondition, for the cipher `ciph m k` of the
schedule at `k`. -/
def encFinalPost (ciph : Mem → Addr → Spec.Cbc.Cipher) (b pb : Nat) : (finalSig nk ek nkLen b).Post pb :=
  fun k iv data len m m' _ => Spec.Cfb.EncryptFinal (ciph m k) b m m' iv data len.toNat

/-- The final decryption's postcondition. -/
def decFinalPost (ciph : Mem → Addr → Spec.Cbc.Cipher) (b pb : Nat) : (finalSig nk ek nkLen b).Post pb :=
  fun k iv data len m m' _ => Spec.Cfb.DecryptFinal (ciph m k) b m m' iv data len.toNat

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr {n : Nat} (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem agree_of {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- The memory on return, within the data and the block. -/
private theorem final_bufs {b pb : Nat} {vs : List (BitVec 64)} (hlen : vs.length = 4)
    (hb : ∀ r ∈ Sig.bufs (finalSig nk ek nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) :
    ∃ k iv data len, vs = [k, iv, data, len] ∧
      bytesAt m₂ iv b = bytesAt m₁ iv b ∧
      bytesAt m₂ data (len.setWidth pb).toNat = bytesAt m₁ data (len.setWidth pb).toNat := by
  match vs, hlen with
  | [k, iv, data, len], _ =>
    simp only [finalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    have hv := agree_of hb.2.1
    have := Nat.mod_le len.toNat (2 ^ pb)
    exact ⟨k, iv, data, len, rfl, bytesAt_congr hv, bytesAt_congr fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)⟩

/-- The memory on entry, within the schedule (of bytes), the data and the
block. -/
private theorem final_bufsIn {b pb nkLen : Nat} {vs : List (BitVec 64)} (hlen : vs.length = 4)
    (hb : ∀ r ∈ Sig.bufs (finalSig nk .u8 nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) :
    ∃ k iv data len, vs = [k, iv, data, len] ∧
      (∀ i < nkLen, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) ∧
      bytesAt m₂ iv b = bytesAt m₁ iv b ∧
      bytesAt m₂ data (len.setWidth pb).toNat = bytesAt m₁ data (len.setWidth pb).toNat := by
  match vs, hlen with
  | [k, iv, data, len], _ =>
    simp only [finalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hd := agree_of hb.2.2
    have hv := agree_of hb.2.1
    have := Nat.mod_le len.toNat (2 ^ pb)
    exact ⟨k, iv, data, len, rfl, agree_of hb.1, bytesAt_congr hv, bytesAt_congr fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)⟩

end

variable (pb : Nat)

theorem encFinalPost_local {ciph : Mem → Addr → Spec.Cbc.Cipher} {b : Nat} :
    ∀ vs m m₁ m₂ r, vs.length = ((finalSig nk ek nkLen b).words pb).length →
      (∀ r ∈ Sig.bufs (finalSig nk ek nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply ((finalSig nk ek nkLen b).words pb) (encFinalPost ciph b pb) vs m m₁ r →
        Curry.apply ((finalSig nk ek nkLen b).words pb) (encFinalPost ciph b pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨k, iv, data, len, rfl, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (encFinalPost ciph b pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (encFinalPost ciph b pb) _ m m₂ r
  dsimp only [Curry.apply, encFinalPost, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  rw [hv, hd]
  exact h

theorem decFinalPost_local {ciph : Mem → Addr → Spec.Cbc.Cipher} {b : Nat} :
    ∀ vs m m₁ m₂ r, vs.length = ((finalSig nk ek nkLen b).words pb).length →
      (∀ r ∈ Sig.bufs (finalSig nk ek nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply ((finalSig nk ek nkLen b).words pb) (decFinalPost ciph b pb) vs m m₁ r →
        Curry.apply ((finalSig nk ek nkLen b).words pb) (decFinalPost ciph b pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨k, iv, data, len, rfl, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (decFinalPost ciph b pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (decFinalPost ciph b pb) _ m m₂ r
  dsimp only [Curry.apply, decFinalPost, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  rw [hv, hd]
  exact h

/-- `encFinalPost` reads the memory on entry only within the function's
buffers, for a cipher that reads only the schedule (`hc`). -/
theorem encFinalPost_inLocal {ciph : Mem → Addr → Spec.Cbc.Cipher} {b : Nat}
    (hc : ∀ m₁ m₂ k, (∀ i < nkLen, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) → ciph m₂ k = ciph m₁ k) :
    ∀ vs m₁ m₂ m' r, vs.length = ((finalSig nk .u8 nkLen b).words pb).length →
      (∀ r ∈ Sig.bufs (finalSig nk .u8 nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply ((finalSig nk .u8 nkLen b).words pb) (encFinalPost ciph b pb) vs m₁ m' r →
        Curry.apply ((finalSig nk .u8 nkLen b).words pb) (encFinalPost ciph b pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨k, iv, data, len, rfl, hk, hv, hd⟩ := final_bufsIn (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (encFinalPost ciph b pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (encFinalPost ciph b pb) _ m₂ m' r
  dsimp only [Curry.apply, encFinalPost, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  rw [hc m₁ m₂ _ hk, hv, hd]
  exact h

/-- `decFinalPost` reads the memory on entry only within the function's
buffers, for a cipher that reads only the schedule (`hc`). -/
theorem decFinalPost_inLocal {ciph : Mem → Addr → Spec.Cbc.Cipher} {b : Nat}
    (hc : ∀ m₁ m₂ k, (∀ i < nkLen, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) → ciph m₂ k = ciph m₁ k) :
    ∀ vs m₁ m₂ m' r, vs.length = ((finalSig nk .u8 nkLen b).words pb).length →
      (∀ r ∈ Sig.bufs (finalSig nk .u8 nkLen b).params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply ((finalSig nk .u8 nkLen b).words pb) (decFinalPost ciph b pb) vs m₁ m' r →
        Curry.apply ((finalSig nk .u8 nkLen b).words pb) (decFinalPost ciph b pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨k, iv, data, len, rfl, hk, hv, hd⟩ := final_bufsIn (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (decFinalPost ciph b pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb] (decFinalPost ciph b pb) _ m₂ m' r
  dsimp only [Curry.apply, decFinalPost, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  rw [hc m₁ m₂ _ hk, hv, hd]
  exact h

end VG.Proof.Modes

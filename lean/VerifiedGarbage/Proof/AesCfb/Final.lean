module

public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Proof.Framework.PostMono
public import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: shared by the final functions' proofs of every target.

/-!
# AES-CFB128 of a message's last piece: the contracts on the key schedule they are given

Not trusted, and the same on every target. `encryptFinalRoundsContract` and
`decryptFinalRoundsContract`: the contracts of `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` for the key schedule and the number of
rounds they are given, as `Rounds.lean`'s for the whole-block functions,
from which the shared contracts of `Spec/Cfb/Final.lean` follow
(`encryptFinal_keyed`, `decryptFinal_keyed`). Their postconditions read the
memory, on entry and on return, only within the function's buffers
(`encryptFinalPost_local`, `encryptFinalPost_localOut`, …), as a frame that
keeps more working space on the stack needs.

A final function calls the whole-block function on the `n = len / L` whole
blocks of its data, then, if `u = len % L` bytes are left, enciphers the
block it leaves, `c` (the last ciphertext block), in place, and XORs the
first `u` bytes of `CIPH_K(c)` into them. `encryptFinal_of` and
`decryptFinal_of`: what that leaves is `Spec.Cfb.EncryptFinal` (or
`DecryptFinal`).
-/

@[expose] public section

namespace VG.Proof.AesCfb

open VG
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-! ## From what a final function leaves -/

/-- The `u` bytes at `T` XORed with the first `u` of `o`, a byte at a time. -/
theorem bytesAt_xor {m₀ m' : Mem} {T : Addr} {u : Nat} {o : List Byte} (hu : u ≤ o.length)
    (h : ∀ q < u, m' (T + BitVec.ofNat 64 q) = m₀ (T + BitVec.ofNat 64 q) ^^^ o.getD q 0) :
    bytesAt m' T u = Spec.Cbc.xor (bytesAt m₀ T u) o := by
  apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor]; omega)
  intro q h₁ h₂
  have hq : q < u := by simpa [bytesAt] using h₁
  simp only [bytesAt, Spec.Cbc.xor, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rw [h q hq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

section
variable {L : Nat} {ciph : Spec.Cbc.Cipher} {m₀ m' : Mem} {D P : Addr} {len : Nat}

/-- CFB encryption of the `len` bytes at `D` from the block at `P`, from the
whole blocks a final function leaves, its partial last segment XORed a byte
at a time with `CIPH_K(c)`, `c` the last ciphertext block, and the block it
leaves at `P`. -/
theorem encryptFinal_of (hc : ∀ b, (ciph b).length = L) (hL : 0 < L)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.encrypt ciph (bytesAt m₀ P L) (blocksOf L m₀ D (len / L)))
    (htail : ∀ q < len % L, m' (D + BitVec.ofNat 64 (L * (len / L)) + BitVec.ofNat 64 q) =
      m₀ (D + BitVec.ofNat 64 (L * (len / L)) + BitVec.ofNat 64 q) ^^^
        (ciph (Spec.Cbc.next (bytesAt m₀ P L)
          (Spec.Cfb.encrypt ciph (bytesAt m₀ P L) (blocksOf L m₀ D (len / L))))).getD q 0)
    (hiv : bytesAt m' P L =
      let c := Spec.Cbc.next (bytesAt m₀ P L) (Spec.Cfb.encrypt ciph (bytesAt m₀ P L) (blocksOf L m₀ D (len / L)))
      if len % L = 0 then c else ciph c) :
    Spec.Cfb.EncryptFinal ciph L m₀ m' P D len :=
  ⟨Proof.Modes.cfbEncFinal_of ciph m₀ m' D _ len hblocks
      (bytesAt_xor (by rw [hc]; exact Nat.le_of_lt (Nat.mod_lt _ hL)) htail),
    hiv.trans (Proof.Modes.cfbEncFinalNext_of ciph m₀ D _ len)⟩

/-- CFB decryption of the `len` bytes at `D` from the block at `P`, from what
a final function leaves, as `encryptFinal_of`. -/
theorem decryptFinal_of (hc : ∀ b, (ciph b).length = L) (hL : 0 < L)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.decrypt ciph (bytesAt m₀ P L) (blocksOf L m₀ D (len / L)))
    (htail : ∀ q < len % L, m' (D + BitVec.ofNat 64 (L * (len / L)) + BitVec.ofNat 64 q) =
      m₀ (D + BitVec.ofNat 64 (L * (len / L)) + BitVec.ofNat 64 q) ^^^
        (ciph (Spec.Cbc.next (bytesAt m₀ P L) (blocksOf L m₀ D (len / L)))).getD q 0)
    (hiv : bytesAt m' P L =
      let c := Spec.Cbc.next (bytesAt m₀ P L) (blocksOf L m₀ D (len / L))
      if len % L = 0 then c else ciph c) :
    Spec.Cfb.DecryptFinal ciph L m₀ m' P D len :=
  ⟨Proof.Modes.cfbDecFinal_of ciph m₀ m' D _ len hblocks
      (bytesAt_xor (by rw [hc]; exact Nat.le_of_lt (Nat.mod_lt _ hL)) htail),
    hiv.trans (Proof.Modes.cfbDecFinalNext_of ciph m₀ D _ len)⟩

end

theorem aesWith_length (nr : Nat) (w : List Byte) (b : List Byte) : (Spec.Cbc.aesWith nr w b).length = 16 := by
  simp [Spec.Cbc.aesWith]

/-! ## The contracts -/

open VG.Spec.Cfb

/-- The final functions' precondition: 10, 12 or 14 rounds. -/
def finalPre (pb : Nat) : Curry (aesFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _len _scratch _ => rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- AES with the key schedule in the first `16 (rounds + 1)` bytes at
`schedule`. -/
abbrev ciphAt (m : Mem) (schedule : Addr) (rounds : Nat) : Spec.Cbc.Cipher :=
  Spec.Cbc.aesWith rounds (bytesAt m schedule (16 * (rounds + 1)))

/-- The final encryption's postcondition, by AES with the key schedule it is
given, for 10, 12 or 14 rounds (so that it reads only the schedule's 240
bytes). -/
def encryptFinalPost (pb : Nat) : aesFinalSig.Post pb :=
  fun schedule rounds iv data len _scratch m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
      EncryptFinal (ciphAt m schedule rounds.toNat) 16 m m' iv data len.toNat

/-- The final decryption's postcondition. -/
def decryptFinalPost (pb : Nat) : aesFinalSig.Post pb :=
  fun schedule rounds iv data len _scratch m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
      DecryptFinal (ciphAt m schedule rounds.toNat) 16 m m' iv data len.toNat

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CFB128 encryption by AES with `w`, a partial last segment
included, from the block at `iv`, and that block with the one the
encryption leaves (`Spec.Cfb.EncryptFinal`). -/
def encryptFinalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A (pre := finalPre A.ptrBits) (post := encryptFinalPost A.ptrBits) (stack := stack)

/-- The same for decryption (`Spec.Cfb.DecryptFinal`). -/
def decryptFinalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A (pre := finalPre A.ptrBits) (post := decryptFinalPost A.ptrBits) (stack := stack)

/-- `Spec.Cfb.aesEncryptFinalContract` from `encryptFinalRoundsContract`. -/
theorem encryptFinal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (encryptFinalRoundsContract A stack)) :
    Verified T c (Spec.Cfb.aesEncryptFinalContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨hk, hr, hw⟩ => by
    dsimp only [encryptFinalPost, ciphAt] at hp
    have h' := hp (by rw [hr]; rcases hk with h | h | h <;> rw [h] <;> decide)
    rw [hw, hr] at h'
    exact h'

/-- `Spec.Cfb.aesDecryptFinalContract` from `decryptFinalRoundsContract`. -/
theorem decryptFinal_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (decryptFinalRoundsContract A stack)) :
    Verified T c (Spec.Cfb.aesDecryptFinalContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨hk, hr, hw⟩ => by
    dsimp only [decryptFinalPost, ciphAt] at hp
    have h' := hp (by rw [hr]; rcases hk with h | h | h <;> rw [h] <;> decide)
    rw [hw, hr] at h'
    exact h'

/-! ## Locality -/

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

/-- Memories that agree within the final functions' buffers agree on the
schedule, the block and the data. -/
private theorem final_bufs {pb : Nat} {vs : List (BitVec 64)} (hlen : vs.length = 6)
    (hb : ∀ r ∈ Sig.bufs aesFinalSig.params vs, ∀ a, r.1.Contains a 1 → m₁ a = m₂ a) :
    ∃ k rounds iv data len scr, vs = [k, rounds, iv, data, len, scr] ∧
      (∀ n ≤ 240, bytesAt m₂ k n = bytesAt m₁ k n) ∧
      bytesAt m₂ iv 16 = bytesAt m₁ iv 16 ∧
      bytesAt m₂ data (len.setWidth pb).toNat = bytesAt m₁ data (len.setWidth pb).toNat := by
  match vs, hlen with
  | [k, rounds, iv, data, len, scr], _ =>
    simp only [aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    have hv := agree_of hb.2.1
    have hd := agree_of hb.2.2.1
    have := Nat.mod_le len.toNat (2 ^ pb)
    exact ⟨k, rounds, iv, data, len, scr, rfl, fun n hn => bytesAt_congr fun i hi => hk i (by omega),
      bytesAt_congr hv, bytesAt_congr fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega)⟩

end

variable (pb : Nat)

theorem finalPre_local : ∀ vs m₁ m₂, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (finalPre pb) vs m₁ → Curry.apply (aesFinalSig.words pb) (finalPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  match vs, hlen with
  | [_, _, _, _, _, _], _ => exact h

/-- `encryptFinalPost` reads the memory on entry only within the buffers. -/
theorem encryptFinalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (encryptFinalPost pb) vs m₁ m' r →
      Curry.apply (aesFinalSig.words pb) (encryptFinalPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, hk, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (encryptFinalPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (encryptFinalPost pb) _ m₂ m' r
  dsimp only [Curry.apply, encryptFinalPost, ArgWord.ofRaw, Spec.Cfb.EncryptFinal, ciphAt] at h ⊢
  intro hr
  obtain ⟨h1, h2⟩ := h hr
  rw [hk _ (by rcases hr with h | h | h <;> omega), hv, hd]
  exact ⟨h1, h2⟩


/-- `decryptFinalPost` reads the memory on entry only within the buffers. -/
theorem decryptFinalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (decryptFinalPost pb) vs m₁ m' r →
      Curry.apply (aesFinalSig.words pb) (decryptFinalPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, hk, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (decryptFinalPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (decryptFinalPost pb) _ m₂ m' r
  dsimp only [Curry.apply, decryptFinalPost, ArgWord.ofRaw, Spec.Cfb.DecryptFinal, ciphAt] at h ⊢
  intro hr
  obtain ⟨h1, h2⟩ := h hr
  rw [hk _ (by rcases hr with h | h | h <;> omega), hv, hd]
  exact ⟨h1, h2⟩

/-- `encryptFinalPost` reads the memory on return only within the buffers. -/
theorem encryptFinalPost_localOut : ∀ vs m m₁ m₂ r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (encryptFinalPost pb) vs m m₁ r →
      Curry.apply (aesFinalSig.words pb) (encryptFinalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, -, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (encryptFinalPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (encryptFinalPost pb) _ m m₂ r
  dsimp only [Curry.apply, encryptFinalPost, ArgWord.ofRaw, Spec.Cfb.EncryptFinal] at h ⊢
  intro hr
  rw [hv, hd]
  exact h hr

/-- `decryptFinalPost` reads the memory on return only within the buffers. -/
theorem decryptFinalPost_localOut : ∀ vs m m₁ m₂ r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (decryptFinalPost pb) vs m m₁ r →
      Curry.apply (aesFinalSig.words pb) (decryptFinalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, -, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (decryptFinalPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (decryptFinalPost pb) _ m m₂ r
  dsimp only [Curry.apply, decryptFinalPost, ArgWord.ofRaw, Spec.Cfb.DecryptFinal] at h ⊢
  intro hr
  rw [hv, hd]
  exact h hr

end VG.Proof.AesCfb

module

public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Proof.Framework.PostMono
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: shared by the final functions' proofs of every target.

/-!
# AES-OFB of a message's last piece: the contract on the key schedule it is given

Not trusted, and the same on every target. `finalRoundsContract`: the
contract of `vg_aes_ofb_final` for the key schedule and the number of rounds
it is given, as `Rounds.lean`'s for the whole-block function, from which the
shared contract of `Spec/Ofb/Final.lean` follows (`final_keyed`). Its
postcondition reads the memory, on entry and on return, only within the
function's buffers (`finalPost_local`, `finalPost_localOut`), as a frame that
keeps more working space on the stack needs.

A final function calls the whole-block function on the `n = len / 16` whole
blocks of its data, which leaves the last output block `Oₙ` in the IV, then,
if `u = len % 16` bytes are left, enciphers the IV in place, giving
`Oₙ₊₁ = CIPH_K(Oₙ)`, and XORs its first `u` bytes into them.
`cryptFinal_of`: what that leaves is `Spec.Ofb.CryptFinal`.
-/

@[expose] public section

namespace VG.Proof.AesOfb

open VG
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes.CtrFinal (bytesAt_length bytesAt_blocks_tail bytesAt_blocks bytesAt_xor xor_flatten
  blocksAt_length16)

/-! ## From what a final function leaves -/

section
variable {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = 16)
include hc

theorem outputs_length16 (iv : List Byte) (n : Nat) : ∀ o ∈ Spec.Ofb.outputs ciph iv n, o.length = 16 := by
  induction n generalizing iv with
  | zero => simp [Spec.Ofb.outputs]
  | succ n ih =>
    intro o ho
    simp only [Spec.Ofb.outputs, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact hc _
    · exact ih _ o ho

theorem outputs_flatten_length (iv : List Byte) (n : Nat) : (Spec.Ofb.outputs ciph iv n).flatten.length = 16 * n := by
  induction n generalizing iv with
  | zero => rfl
  | succ n ih =>
    simp only [Spec.Ofb.outputs, List.flatten_cons, List.length_append, hc, ih]
    omega

/-- OFB of the `len` bytes at `D` from the block at `P`, from what a final
function leaves: its `n = len / 16` whole blocks as OFB's, its last
`len % 16` bytes XORed a byte at a time with `CIPH_K(Oₙ)`, `Oₙ` the last
output block of the whole blocks, and the block at `P` the last output
block used. -/
theorem cryptFinal_of {m₀ m' : Mem} {P D : Addr} {len : Nat}
    (hblocks : Spec.Cbc.blocksAt m' D (len / 16) =
      Spec.Ofb.crypt ciph (bytesAt m₀ P 16) (Spec.Cbc.blocksAt m₀ D (len / 16)))
    (htail : ∀ q < len % 16, m' (D + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 q) =
      m₀ (D + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 q) ^^^
        (ciph (Spec.Ofb.next ciph (bytesAt m₀ P 16) (len / 16))).getD q 0)
    (hiv : bytesAt m' P 16 =
      let c := Spec.Ofb.next ciph (bytesAt m₀ P 16) (len / 16)
      if len % 16 = 0 then c else ciph c) :
    Spec.Ofb.CryptFinal ciph 16 m₀ m' P D len := by
  have hu : len % 16 < 16 := Nat.mod_lt _ (by decide)
  have ecount : Spec.Ofb.blockCount 16 len = if len % 16 = 0 then len / 16 else len / 16 + 1 := by
    unfold Spec.Ofb.blockCount; split <;> omega
  have ht := bytesAt_xor (o := ciph (Spec.Ofb.next ciph (bytesAt m₀ P 16) (len / 16))) (by rw [hc]; omega) htail
  have hx : Spec.Cbc.xor (Spec.Cbc.blocksAt m₀ D (len / 16)).flatten
      (Spec.Ofb.outputs ciph (bytesAt m₀ P 16) (len / 16)).flatten =
        (Spec.Ofb.crypt ciph (bytesAt m₀ P 16) (Spec.Cbc.blocksAt m₀ D (len / 16))).flatten := by
    rw [xor_flatten _ _ (blocksAt_length16 m₀ D _) (outputs_length16 hc _ _)
      (by simp [AesCbc.length_blocksAt, length_outputs]), Spec.Ofb.crypt, AesCbc.length_blocksAt]
  have hl : (Spec.Cbc.blocksAt m₀ D (len / 16)).flatten.length =
      (Spec.Ofb.outputs ciph (bytesAt m₀ P 16) (len / 16)).flatten.length := by
    rw [← bytesAt_blocks, bytesAt_length, outputs_flatten_length hc]
  refine ⟨?_, ?_⟩
  · rw [Spec.Ofb.cryptFinal, bytesAt_length, ecount, bytesAt_blocks_tail m' D len, hblocks, ht,
      bytesAt_blocks_tail m₀ D len]
    split
    · rename_i h0
      have e : ∀ (m : Mem) (p : Addr), bytesAt m p (len % 16) = [] := fun m p => by rw [h0]; rfl
      rw [e, List.append_nil, ← hx]
      simp only [Spec.Cbc.xor, List.zipWith_nil_left, List.append_nil]
    · rw [outputs_succ, List.flatten_append, List.flatten_singleton]
      simp only [Spec.Cbc.xor] at hx ⊢
      rw [List.zipWith_append hl, hx]
  · rw [hiv, ecount]
    dsimp only
    split
    · rfl
    · rw [next_succ]

end

theorem aesWith_length (nr : Nat) (w : List Byte) (b : List Byte) : (Spec.Cbc.aesWith nr w b).length = 16 := by
  simp [Spec.Cbc.aesWith]

/-! ## The contract -/

open VG.Spec.Ofb

/-- The final function's precondition: 10, 12 or 14 rounds. -/
def finalPre (pb : Nat) : Curry (aesFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _len _scratch _ => rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- AES with the key schedule in the first `16 (rounds + 1)` bytes at
`schedule`. -/
abbrev ciphAt (m : Mem) (schedule : Addr) (rounds : Nat) : Spec.Cbc.Cipher :=
  Spec.Cbc.aesWith rounds (bytesAt m schedule (16 * (rounds + 1)))

/-- The final function's postcondition, by AES with the key schedule it is
given, for 10, 12 or 14 rounds (so that it reads only the schedule's 240
bytes). -/
def finalPost (pb : Nat) : aesFinalSig.Post pb :=
  fun schedule rounds iv data len _scratch m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
      CryptFinal (ciphAt m schedule rounds.toNat) 16 m m' iv data len.toNat

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their OFB encryption or decryption by AES with `w`, a partial last
block included, from the block at `iv`, and that block with the last output
block used (`Spec.Ofb.CryptFinal`). -/
def finalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A (pre := finalPre A.ptrBits) (post := finalPost A.ptrBits) (stack := stack)

/-- `Spec.Ofb.aesFinalContract` from `finalRoundsContract`. -/
theorem final_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (finalRoundsContract A stack)) :
    Verified T c (Spec.Ofb.aesFinalContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ _ hp key ⟨hk, hr, hw⟩ => by
    dsimp only [finalPost, ciphAt] at hp
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

/-- Memories that agree within the final function's buffers agree on the
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

/-- `finalPost` reads the memory on entry only within the buffers. -/
theorem finalPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (finalPost pb) vs m₁ m' r →
      Curry.apply (aesFinalSig.words pb) (finalPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, hk, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (finalPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (finalPost pb) _ m₂ m' r
  dsimp only [Curry.apply, finalPost, ArgWord.ofRaw, Spec.Ofb.CryptFinal, ciphAt] at h ⊢
  intro hr
  obtain ⟨h1, h2⟩ := h hr
  rw [hk _ (by rcases hr with h | h | h <;> omega), hv, hd]
  exact ⟨h1, h2⟩

/-- `finalPost` reads the memory on return only within the buffers. -/
theorem finalPost_localOut : ∀ vs m m₁ m₂ r, vs.length = (aesFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinalSig.words pb) (finalPost pb) vs m m₁ r →
      Curry.apply (aesFinalSig.words pb) (finalPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨k, rounds, iv, data, len, scr, rfl, -, hv, hd⟩ := final_bufs (pb := pb) hlen hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (finalPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (finalPost pb) _ m m₂ r
  dsimp only [Curry.apply, finalPost, ArgWord.ofRaw, Spec.Ofb.CryptFinal] at h ⊢
  intro hr
  rw [hv, hd]
  exact h hr

end VG.Proof.AesOfb

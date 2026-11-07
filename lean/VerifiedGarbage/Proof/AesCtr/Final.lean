module

public import VerifiedGarbage.Spec.Ctr.Final
public import VerifiedGarbage.Proof.Framework.PostMono
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: shared by the final functions' proofs of every target.

/-!
# AES-CTR of a message's last piece: the contract on the key schedule it is given

Not trusted, and the same on every target. `finalRoundsContract`: the
contract of `vg_aes_ctr_final` for the key schedule and the number of rounds
it is given, as `Rounds.lean`'s for the whole-block function, from which the
shared contract of `Spec/Ctr/Final.lean` follows (`final_keyed`). Its
postcondition reads the memory, on entry and on return, and its leak, only
within the function's buffers (`finalPost_local`, `finalPost_localOut`,
`finalLeak_local`), as a frame that keeps more working space on the stack
needs. What a final function leaves gives `Spec.Ctr.CryptFinal` by
`Proof.Modes.CtrFinal.cryptFinal_of`, for any cipher.
-/

@[expose] public section

namespace VG.Proof.AesCtr

open VG
open VG.Spec.Aes (bytesAt)

theorem aesWith_length (nr : Nat) (w : List Byte) (b : List Byte) : (Spec.Cbc.aesWith nr w b).length = 16 := by
  simp [Spec.Cbc.aesWith]

/-! ## The contract -/

open VG.Spec.Ctr

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
      CryptFinal (ciphAt m schedule rounds.toNat) m m' iv data len.toNat

/-- What the final function's timing may depend on, besides its public
arguments: the counter block's last four bytes. -/
def finalLeak (pb : Nat) : Curry (aesFinalSig.words pb) (Mem → List Nat) :=
  fun _schedule _rounds ctr _data _len _scratch m => ctrLeak m ctr

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: replaces the `len` bytes at `data`
with their CTR encryption or decryption by AES with `w`, a partial last
block included, from the counter block at `iv`, and that block with `Tₙ₊₁`
(`Spec.Ctr.CryptFinal`). Its timing may depend on the counter block's last
four bytes (`Spec.Ctr.ctrLeak`). -/
def finalRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesFinalSig.contract A (pre := finalPre A.ptrBits) (post := finalPost A.ptrBits)
    (leak := some (finalLeak A.ptrBits)) (stack := stack)

/-- `Spec.Ctr.aesFinalContract` from `finalRoundsContract`. -/
theorem final_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (finalRoundsContract A stack)) :
    Verified T c (Spec.Ctr.aesFinalContract A stack) :=
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
  dsimp only [Curry.apply, finalPost, ArgWord.ofRaw, Spec.Ctr.CryptFinal, ciphAt] at h ⊢
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
  dsimp only [Curry.apply, finalPost, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
  intro hr
  rw [hv, hd]
  exact h hr

/-- The leak, `Spec.Ctr.ctrLeak`, reads the memory only within the
buffers. -/
theorem finalLeak_local : Sig.LeakLocal pb aesFinalSig (some (finalLeak pb)) := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨k, rounds, iv, data, len, scr, rfl, -, hv, -⟩ := final_bufs (pb := pb) hlen hb
  change ctrLeak m₁ iv = ctrLeak m₂ iv
  simp only [ctrLeak, hv]

end VG.Proof.AesCtr

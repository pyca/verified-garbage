import VerifiedGarbage.Spec.Cfb8
import VerifiedGarbage.Spec.Aes

/-!
# CFB8's result, for any block cipher and target

A CFB8 data loop (`Impl/Modes/<Target>/Cfb8.lean`) replaces each byte `j`
with `P#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))` (`cfb8Out`), where the input block `Iⱼ`
(`cfb8In`) is the IV for `j = 0` and is then the one before it without its
first byte, followed by the ciphertext byte, the output when encrypting and
the input when decrypting. When it has, the bytes are `Spec.Cfb8.encrypt`'s
or `Spec.Cfb8.decrypt`'s, and the input block after the last is the one to
continue from (`cfb8Enc_of`, `cfb8Dec_of`). Nothing here depends on a
cipher or a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

/-- The input block of byte `j` of the data at `D` in `m₀`, from the IV `iv`:
the one before it without its first byte, followed by the ciphertext byte
before it (`cfb8C`). -/
def cfb8In (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) : Nat → List Byte
  | 0 => iv
  | j + 1 => (cfb8In enc ciph m₀ D iv j).tail ++
      [if enc then m₀ (D + BitVec.ofNat 64 j) ^^^ (ciph (cfb8In enc ciph m₀ D iv j)).headD 0
       else m₀ (D + BitVec.ofNat 64 j)]

/-- The ciphertext byte `j`: the output when encrypting, the input when
decrypting. -/
def cfb8C (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : Byte :=
  if enc then m₀ (D + BitVec.ofNat 64 j) ^^^ (ciph (cfb8In enc ciph m₀ D iv j)).headD 0
  else m₀ (D + BitVec.ofNat 64 j)

theorem cfb8In_succ_eq (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    cfb8In enc ciph m₀ D iv (j + 1) = (cfb8In enc ciph m₀ D iv j).tail ++ [cfb8C enc ciph m₀ D iv j] := rfl

/-- The output byte `j`. -/
def cfb8Out (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : Byte :=
  m₀ (D + BitVec.ofNat 64 j) ^^^ (ciph (cfb8In enc ciph m₀ D iv j)).headD 0

theorem cfb8In_succ (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    ∀ j, cfb8In enc ciph m₀ D iv (j + 1) =
      cfb8In enc ciph m₀ (D + 1) (iv.tail ++ [cfb8C enc ciph m₀ D iv 0]) j ∧
    cfb8C enc ciph m₀ D iv (j + 1) = cfb8C enc ciph m₀ (D + 1) (iv.tail ++ [cfb8C enc ciph m₀ D iv 0]) j
  | 0 => by
    have e : D + BitVec.ofNat 64 (0 + 1) = D + 1 + BitVec.ofNat 64 0 := by simp
    have hi : cfb8In enc ciph m₀ D iv (0 + 1) =
        cfb8In enc ciph m₀ (D + 1) (iv.tail ++ [cfb8C enc ciph m₀ D iv 0]) 0 := by
      rw [cfb8In_succ_eq]; rfl
    exact ⟨hi, by simp only [cfb8C, hi, e]⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := cfb8In_succ enc ciph m₀ D iv j
    have e : D + BitVec.ofNat 64 (j + 1 + 1) = D + 1 + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    have hi : cfb8In enc ciph m₀ D iv (j + 1 + 1) =
        cfb8In enc ciph m₀ (D + 1) (iv.tail ++ [cfb8C enc ciph m₀ D iv 0]) (j + 1) := by
      rw [cfb8In_succ_eq, h1, h2, ← cfb8In_succ_eq]
    exact ⟨hi, by simp only [cfb8C, hi, e]⟩

theorem cfb8Out_succ (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    cfb8Out enc ciph m₀ D iv (j + 1) =
      cfb8Out enc ciph m₀ (D + 1) (iv.tail ++ [cfb8C enc ciph m₀ D iv 0]) j := by
  have e : D + BitVec.ofNat 64 (j + 1) = D + 1 + BitVec.ofNat 64 j := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  simp only [cfb8Out, (cfb8In_succ enc ciph m₀ D iv j).1, e]

theorem bytesAt_succ (m : Mem) (D : Addr) (n : Nat) :
    bytesAt m D (n + 1) = m D :: bytesAt m (D + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congr (congrArg List.cons (by simp)) (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply]
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- `Spec.Cfb8.next` after one more byte. -/
theorem next_cons {iv : List Byte} (h : iv ≠ []) (c : Byte) (cs : List Byte) :
    Spec.Cfb8.next iv (c :: cs) = Spec.Cfb8.next (iv.tail ++ [c]) cs := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [Spec.Cfb8.next, List.drop_succ_cons, List.append_assoc]

theorem tail_append_ne {iv : List Byte} (c : Byte) : iv.tail ++ [c] ≠ [] := by simp

/-- The data and the input block after `n` bytes of CFB8 encryption. -/
theorem cfb8Enc_of (ciph : Spec.Cbc.Cipher) (m₀ : Mem) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte), iv ≠ [] →
      (List.range n).map (cfb8Out true ciph m₀ D iv) = Spec.Cfb8.encrypt ciph iv (bytesAt m₀ D n) ∧
      cfb8In true ciph m₀ D iv n = Spec.Cfb8.next iv (Spec.Cfb8.encrypt ciph iv (bytesAt m₀ D n))
  | 0, _, _, _ => ⟨rfl, by simp [cfb8In, Spec.Cfb8.next, Spec.Cfb8.encrypt, bytesAt]⟩
  | n + 1, D, iv, hiv => by
    obtain ⟨ih1, ih2⟩ := cfb8Enc_of ciph m₀ n (D + 1) (iv.tail ++ [cfb8C true ciph m₀ D iv 0]) (tail_append_ne _)
    have hc : cfb8C true ciph m₀ D iv 0 = m₀ D ^^^ (ciph iv).headD 0 := by simp [cfb8C, cfb8In]
    rw [bytesAt_succ, Spec.Cfb8.encrypt, ← hc]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map, ← ih1]
      refine congr (congrArg List.cons (by rw [hc]; simp [cfb8Out, cfb8In])) (List.map_congr_left fun j _ => ?_)
      exact cfb8Out_succ true ciph m₀ D iv j
    · rw [next_cons hiv, ← ih2, (cfb8In_succ true ciph m₀ D iv n).1]

/-- The data and the input block after `n` bytes of CFB8 decryption. -/
theorem cfb8Dec_of (ciph : Spec.Cbc.Cipher) (m₀ : Mem) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte), iv ≠ [] →
      (List.range n).map (cfb8Out false ciph m₀ D iv) = Spec.Cfb8.decrypt ciph iv (bytesAt m₀ D n) ∧
      cfb8In false ciph m₀ D iv n = Spec.Cfb8.next iv (bytesAt m₀ D n)
  | 0, _, _, _ => ⟨rfl, by simp [cfb8In, Spec.Cfb8.next, bytesAt]⟩
  | n + 1, D, iv, hiv => by
    obtain ⟨ih1, ih2⟩ := cfb8Dec_of ciph m₀ n (D + 1) (iv.tail ++ [cfb8C false ciph m₀ D iv 0]) (tail_append_ne _)
    have hc : cfb8C false ciph m₀ D iv 0 = m₀ D := by simp [cfb8C]
    rw [bytesAt_succ, Spec.Cfb8.decrypt, ← hc]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map, ← ih1]
      refine congr (congrArg List.cons (by rw [hc]; simp [cfb8Out, cfb8In])) (List.map_congr_left fun j _ => ?_)
      exact cfb8Out_succ false ciph m₀ D iv j
    · rw [next_cons hiv, ← ih2, (cfb8In_succ false ciph m₀ D iv n).1]

theorem cfb8In_length (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) {iv : List Byte} {L : Nat}
    (hiv : iv.length = L) (hL : 0 < L) : ∀ j, (cfb8In enc ciph m₀ D iv j).length = L
  | 0 => by rw [cfb8In]; exact hiv
  | j + 1 => by
    rw [cfb8In_succ_eq, List.length_append, List.length_tail, cfb8In_length enc ciph m₀ D hiv hL j, List.length_singleton]
    omega

/-- Byte `u` of the input block of byte `j + 1`. -/
theorem cfb8In_succ_getD (enc : Bool) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) {iv : List Byte} {L : Nat}
    (hiv : iv.length = L) (hL : 0 < L) (j : Nat) {u : Nat} (hu : u < L) :
    (cfb8In enc ciph m₀ D iv (j + 1)).getD u 0 =
      if u + 1 < L then (cfb8In enc ciph m₀ D iv j).getD (u + 1) 0 else cfb8C enc ciph m₀ D iv j := by
  have hl := cfb8In_length enc ciph m₀ D hiv hL j
  rw [cfb8In_succ_eq]
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_tail]; omega),
      List.getElem?_tail, ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [List.length_tail]; omega),
      List.length_tail, hl, show u - (L - 1) = 0 by omega]
    rfl

end VG.Proof.Modes

import VerifiedGarbage.Spec.Cast5

/-!
# CAST5: the round function by its type, and the rounds in order

`f` of round `i` is `comb t` of the four S-box values at the bytes of
`I = (mix t Kmᵢ D) <<< Krᵢ`, for the type `t = i % 3` (`f_eq`). Encryption
and decryption run the rounds one after the other (`encFold`, `decFold`).
-/

namespace VG.Proof.Cast5

open VG.Spec.Cast5

/-- The first step of a round function of type `t`: `Km + D` (1), `Km ^ D` (2),
`Km - D` (3, or 0). -/
def mix (t : Nat) (km d : Word) : Word :=
  match t with | 1 => km + d | 2 => km ^^^ d | _ => km - d

/-- `f` of type `t` from `S1[Ia]`, `S2[Ib]`, `S3[Ic]`, `S4[Id]`. -/
def comb (t : Nat) (a b c d : Word) : Word :=
  match t with
  | 1 => ((a ^^^ b) - c) + d
  | 2 => ((a - b) + c) ^^^ d
  | _ => ((a + b) ^^^ c) - d

/-- `I` of round `i`. -/
def roundI (i : Nat) (d km kr : Word) : Word := (mix (i % 3) km d).rotateLeft (kr.toNat % 32)

theorem f_eq (i : Nat) (d km kr : Word) :
    f i d km kr = comb (i % 3) (S1 (byte (roundI i d km kr) 0)) (S2 (byte (roundI i d km kr) 1))
      (S3 (byte (roundI i d km kr) 2)) (S4 (byte (roundI i d km kr) 3)) := by
  unfold f roundI
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h <;> simp only [h] <;> rfl

/-- `mix` and `comb` of type 3 are those of type 0. -/
theorem mix_three (km d : Word) : mix 3 km d = mix 0 km d := rfl
theorem comb_three (a b c d : Word) : comb 3 a b c d = comb 0 a b c d := rfl

/-! ## The rounds in order -/

/-- Rounds `1 … m` of encryption. -/
def encFold (k : Schedule) (m : Nat) (lr : Word × Word) : Word × Word :=
  (List.range m).foldl (fun lr j => round k (j + 1) lr) lr

/-- The first `m` rounds of decryption with `n` rounds: `n … n - m + 1`. -/
def decFold (k : Schedule) (n m : Nat) (lr : Word × Word) : Word × Word :=
  (List.range m).foldl (fun lr j => round k (n - j) lr) lr

theorem encFold_succ (k : Schedule) (m : Nat) (lr : Word × Word) :
    encFold k (m + 1) lr = round k (m + 1) (encFold k m lr) := by
  simp only [encFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem decFold_succ (k : Schedule) (n m : Nat) (lr : Word × Word) :
    decFold k n (m + 1) lr = round k (n - m) (decFold k n m lr) := by
  simp only [decFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem encryptBlock_eq (k : Schedule) (n : Nat) (b : Block) :
    encryptBlock k n b = encodeBlock ((encFold k n (decodeBlock b)).2, (encFold k n (decodeBlock b)).1) :=
  rfl

theorem decryptBlock_eq (k : Schedule) (n : Nat) (b : Block) :
    decryptBlock k n b =
      encodeBlock ((decFold k n n (decodeBlock b)).2, (decFold k n n (decodeBlock b)).1) :=
  rfl

end VG.Proof.Cast5

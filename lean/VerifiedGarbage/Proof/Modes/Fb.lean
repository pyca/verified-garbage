import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Impl.Modes.FbMode
import VerifiedGarbage.Spec.Ofb
import VerifiedGarbage.Spec.Cfb

/-!
# OFB's and CFB's results, for any block cipher and target

A feedback mode's data loop (`Impl/Modes/<Target>/Fb.lean`) replaces each
block `j` with `Pⱼ ⊕ CIPH_K(Iⱼ)` (`fbOut`), where the input block `Iⱼ`
(`fbIn`) is the IV for `j = 0` and is then made from the previous block's
output block, input and output (`fbStep`): the output block for OFB, the
ciphertext for CFB. When it has, the blocks are `Spec.Ofb.crypt`'s,
`Spec.Cfb.encrypt`'s or `Spec.Cfb.decrypt`'s, and the input block after the
last is the block to continue from (`ofb_of`, `cfbEnc_of`, `cfbDec_of`).
Nothing here depends on a cipher or a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Impl.Modes (FbMode)
open VG.Spec.Aes (bytesAt)

/-- The next input block, from the output block `o` of a block whose input
is `x`: OFB's is `o`, CFB's the ciphertext, `x ⊕ o` when encrypting and `x`
when decrypting. -/
def fbStep : FbMode → List Byte → List Byte → List Byte
  | .ofb, o, _ => o
  | .cfbEnc, o, x => Spec.Cbc.xor x o
  | .cfbDec, _, x => x

/-- The input block of block `j` (of `L` bytes) of the data at `D` in `m₀`,
from the IV `iv`. -/
def fbIn (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) : Nat → List Byte
  | 0 => iv
  | j + 1 => fbStep mo (ciph (fbIn mo L ciph m₀ D iv j)) (bytesAt m₀ (D + BitVec.ofNat 64 (L * j)) L)

/-- The output of block `j`: the data's block XORed with `CIPH_K` of its
input block. -/
def fbOut (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    List Byte :=
  Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * j)) L) (ciph (fbIn mo L ciph m₀ D iv j))

theorem fbIn_succ (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    ∀ j, fbIn mo L ciph m₀ D iv (j + 1) =
      fbIn mo L ciph m₀ (D + BitVec.ofNat 64 L) (fbStep mo (ciph iv) (bytesAt m₀ D L)) j
  | 0 => by simp [fbIn]
  | j + 1 => by
    rw [fbIn, fbIn_succ mo L ciph m₀ D iv j, fbIn, VG.Offset.add_add, Nat.mul_succ, Nat.add_comm L]

theorem fbOut_succ (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte)
    (j : Nat) : fbOut mo L ciph m₀ D iv (j + 1) =
      fbOut mo L ciph m₀ (D + BitVec.ofNat 64 L) (fbStep mo (ciph iv) (bytesAt m₀ D L)) j := by
  rw [fbOut, fbOut, fbIn_succ, VG.Offset.add_add, Nat.mul_succ, Nat.add_comm L]

/-- The blocks of a mode `F` that makes each block `x` into `x ⊕ CIPH_K(iv)`
and goes on from `fbStep`, block by block. -/
theorem fbOut_eq (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem)
    (F : List Byte → List (List Byte) → List (List Byte)) (hF : ∀ iv x xs,
      F iv (x :: xs) = Spec.Cbc.xor x (ciph iv) :: F (fbStep mo (ciph iv) x) xs) (hF0 : ∀ iv, F iv [] = []) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte),
      (List.range n).map (fbOut mo L ciph m₀ D iv) = F iv (blocksOf L m₀ D n)
  | 0, _, iv => (hF0 iv).symm
  | n + 1, D, iv => by
    rw [blocksOf_succ, hF, ← fbOut_eq mo L ciph m₀ F hF hF0 n, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congr (congrArg List.cons (by simp [fbOut, fbIn])) (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    exact fbOut_succ mo L ciph m₀ D iv j

/-- The input block after `n` blocks, from the next input block after each. -/
theorem fbIn_eq (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (G : List Byte → List (List Byte) → List Byte)
    (hG : ∀ iv x xs, G iv (x :: xs) = G (fbStep mo (ciph iv) x) xs) (hG0 : ∀ iv, G iv [] = iv) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte), fbIn mo L ciph m₀ D iv n = G iv (blocksOf L m₀ D n)
  | 0, _, iv => (hG0 iv).symm
  | n + 1, D, iv => by rw [blocksOf_succ, hG, fbIn_succ, fbIn_eq mo L ciph m₀ G hG hG0 n]

/-- OFB's output blocks after `n` blocks from `iv`, as `Spec.Ofb.outputs`. -/
theorem outputs_succ (ciph : Spec.Cbc.Cipher) (iv : List Byte) (n : Nat) :
    Spec.Ofb.outputs ciph iv (n + 1) = ciph iv :: Spec.Ofb.outputs ciph (ciph iv) n := rfl

/-- The data and the input block after `n` blocks of OFB. -/
theorem ofb_of (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (n : Nat) :
    (List.range n).map (fbOut .ofb L ciph m₀ D iv) = Spec.Ofb.crypt ciph iv (blocksOf L m₀ D n) ∧
      fbIn .ofb L ciph m₀ D iv n = Spec.Ofb.next ciph iv n := by
  refine ⟨fbOut_eq .ofb L ciph m₀ (Spec.Ofb.crypt ciph) (fun iv x xs => ?_) (fun _ => rfl) n D iv, ?_⟩
  · simp only [Spec.Ofb.crypt, List.length_cons, outputs_succ, List.zipWith_cons_cons, fbStep]
  · have hl : (blocksOf L m₀ D n).length = n := by simp [blocksOf]
    rw [fbIn_eq .ofb L ciph m₀ (fun iv xs => Spec.Ofb.next ciph iv xs.length) (fun iv x xs => ?_) (fun _ => rfl) n D iv,
      hl]
    simp only [Spec.Ofb.next, List.length_cons, outputs_succ, List.getLastD_cons, fbStep]

/-- The data and the input block after `n` blocks of CFB encryption: the
last ciphertext block. -/
theorem cfbEnc_of (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (n : Nat) :
    (List.range n).map (fbOut .cfbEnc L ciph m₀ D iv) = Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D n) ∧
      fbIn .cfbEnc L ciph m₀ D iv n = Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D n)) :=
  ⟨fbOut_eq .cfbEnc L ciph m₀ (Spec.Cfb.encrypt ciph) (fun _ _ _ => rfl) (fun _ => rfl) n D iv,
    fbIn_eq .cfbEnc L ciph m₀ (fun iv xs => Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv xs))
      (fun _ _ _ => by simp only [Spec.Cfb.encrypt, Spec.Cbc.next, List.getLastD_cons, fbStep]) (fun _ => rfl) n D iv⟩

/-- The data and the input block after `n` blocks of CFB decryption: the
last ciphertext block, the last block of the data on entry. -/
theorem cfbDec_of (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (n : Nat) :
    (List.range n).map (fbOut .cfbDec L ciph m₀ D iv) = Spec.Cfb.decrypt ciph iv (blocksOf L m₀ D n) ∧
      fbIn .cfbDec L ciph m₀ D iv n = Spec.Cbc.next iv (blocksOf L m₀ D n) :=
  ⟨fbOut_eq .cfbDec L ciph m₀ (Spec.Cfb.decrypt ciph) (fun _ _ _ => rfl) (fun _ => rfl) n D iv,
    fbIn_eq .cfbDec L ciph m₀ Spec.Cbc.next
      (fun _ _ _ => by simp only [Spec.Cbc.next, List.getLastD_cons, fbStep]) (fun _ => rfl) n D iv⟩

theorem fbIn_length {mo : FbMode} {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem)
    (D : Addr) {iv : List Byte} (hiv : iv.length = L) : ∀ j, (fbIn mo L ciph m₀ D iv j).length = L
  | 0 => hiv
  | j + 1 => by
    cases mo <;> simp [fbIn, fbStep, Spec.Cbc.xor, hc, bytesAt]

theorem fbOut_length {mo : FbMode} {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem)
    (D : Addr) (iv : List Byte) (j : Nat) : (fbOut mo L ciph m₀ D iv j).length = L := by
  simp [fbOut, Spec.Cbc.xor, hc, bytesAt]

/-! ## Byte by byte -/

/-- Byte `u` of the next input block, from byte `o` of the output block and
`x` of the block (`fbStep`). -/
def fbByte : FbMode → Byte → Byte → Byte
  | .ofb, o, _ => o
  | .cfbEnc, o, x => x ^^^ o
  | .cfbDec, _, x => x

theorem xor_getD {a b : List Byte} {u : Nat} (ha : u < a.length) (hb : u < b.length) :
    (Spec.Cbc.xor a b).getD u 0 = a.getD u 0 ^^^ b.getD u 0 := by
  have h : u < (Spec.Cbc.xor a b).length := by simp only [Spec.Cbc.xor, List.length_zipWith]; omega
  rw [← List.getElem_eq_getD (h := h) 0, ← List.getElem_eq_getD (h := ha) 0, ← List.getElem_eq_getD (h := hb) 0]
  simp only [Spec.Cbc.xor, List.getElem_zipWith]

theorem fbStep_getD (mo : FbMode) {o x : List Byte} {u : Nat} (ho : u < o.length) (hx : u < x.length) :
    (fbStep mo o x).getD u 0 = fbByte mo (o.getD u 0) (x.getD u 0) := by
  cases mo
  · rfl
  · exact xor_getD hx ho
  · rfl

/-- Byte `u` of the input block of block `j + 1`. -/
theorem fbIn_succ_getD (mo : FbMode) {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem)
    (D : Addr) (iv : List Byte) (j : Nat) {u : Nat} (hu : u < L) :
    (fbIn mo L ciph m₀ D iv (j + 1)).getD u 0 =
      fbByte mo ((ciph (fbIn mo L ciph m₀ D iv j)).getD u 0) (m₀ (D + BitVec.ofNat 64 (L * j + u))) := by
  rw [fbIn, fbStep_getD mo (by rw [hc]; exact hu) (by simp [bytesAt, hu])]
  simp [bytesAt, hu, VG.Offset.add_add]

/-- Byte `u` of the output of block `j`. -/
theorem fbOut_getD (mo : FbMode) {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem)
    (D : Addr) (iv : List Byte) (j : Nat) {u : Nat} (hu : u < L) :
    (fbOut mo L ciph m₀ D iv j).getD u 0 =
      m₀ (D + BitVec.ofNat 64 (L * j + u)) ^^^ (ciph (fbIn mo L ciph m₀ D iv j)).getD u 0 := by
  rw [fbOut, xor_getD (by simp [bytesAt, hu]) (by rw [hc]; exact hu)]
  simp [bytesAt, hu, VG.Offset.add_add]

/-- The byte the data's XORed back into the output gives, for CFB decryption. -/
theorem xor_xor_cancel (o x : Byte) : o ^^^ (x ^^^ o) = x := by
  rw [BitVec.xor_comm x o, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Modes

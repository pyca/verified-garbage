module

public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Spec.Cfb.Final
public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Proof.Modes.Fb
import VerifiedGarbage.Proof.Modes.Cbc
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.Modes.CbcEnc
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB's and CFB's results on a message's last piece, for any block cipher and target

A feedback mode's loop over the `len` bytes of a message's last piece, in
segments of a block of `L` bytes the last of which may be partial
(`Impl/Modes/<Target>/FbFinal.lean`), makes byte `i` that of `fbOut` of its
block, and leaves the block to continue from, `fbNextF`: the input block
after the whole blocks, or the partial segment's output block. When it has,
the data and the block are `Spec.Cfb.encryptFinal`'s and
`encryptFinalNext`'s (`cfbEncFinal_of_bytes`), `decryptFinal`'s and
`decryptFinalNext`'s (`cfbDecFinal_of_bytes`), or, for OFB,
`Spec.Ofb.cryptFinal`'s and the last output block used, `Spec.Ofb.next`
after `⌈len / L⌉` blocks (`ofbFinal_of_bytes`). Nothing here depends on a
cipher or a target.
-/

@[expose] public section

/-! ## CFB of a message's last piece, for any block cipher and target

A final function calls a whole-block CFB function on the `n = len / L`
whole blocks of its data, which leaves the last ciphertext block `c` in the
IV, then, if `r = len % L` bytes are left, the whole-block encryption on a
zero block, which leaves `CIPH_K(c)` both there and in the IV, and XORs its
first `r` bytes into them. When it has, its data and block are
`Spec.Cfb.encryptFinal`'s and `encryptFinalNext`'s (`cfbEncFinal_of`,
`cfbEncFinalNext_of`), or `decryptFinal`'s and `decryptFinalNext`'s
(`cfbDecFinal_of`, `cfbDecFinalNext_of`). Nothing here depends on a cipher
or a target.
-/

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

theorem bytesAt_length (m : Mem) (D : Addr) (len : Nat) : (bytesAt m D len).length = len := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (D : Addr) (a b : Nat) :
    bytesAt m D (a + b) = bytesAt m D a ++ bytesAt m (D + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_add,
    BitVec.add_assoc]

theorem bytesAt_drop (m : Mem) (D : Addr) (len a : Nat) :
    (bytesAt m D len).drop a = bytesAt m (D + BitVec.ofNat 64 a) (len - a) := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_take (m : Mem) (D : Addr) {len k : Nat} (h : k ≤ len) :
    (bytesAt m D len).take k = bytesAt m D k := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i _ _
  simp only [bytesAt, List.getElem_take, List.getElem_map, List.getElem_range]

theorem blocksOf_succ' (L : Nat) (m : Mem) (D : Addr) (n : Nat) :
    blocksOf L m D (n + 1) = blocksOf L m D n ++ [bytesAt m (D + BitVec.ofNat 64 (L * n)) L] := by
  simp [blocksOf, List.range_succ]

/-- `L n` bytes, as `n` blocks. -/
theorem bytesAt_mul (L : Nat) (m : Mem) (D : Addr) : ∀ n, bytesAt m D (L * n) = (blocksOf L m D n).flatten
  | 0 => by simp [bytesAt, blocksOf]
  | n + 1 => by
    rw [Nat.mul_succ, bytesAt_add, bytesAt_mul L m D n, blocksOf_succ', List.flatten_append, List.flatten_singleton]

/-- The whole segments of the `len` bytes at `D`: its `len / L` blocks. -/
theorem segments_bytesAt {L : Nat} (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.segments L (bytesAt m D len) = blocksOf L m D (len / L) := by
  simp only [Spec.Cfb.segments, bytesAt_length, blocksOf]
  apply List.map_congr_left
  intro i hi
  have hi : i < len / L := List.mem_range.mp hi
  have hle : L * i + L ≤ len := by
    have := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    exact Nat.le_trans this (Nat.mul_div_le len L)
  rw [bytesAt_drop, bytesAt_take _ _ (by omega)]

/-- The partial last segment of the `len` bytes at `D`: its last `len % L`
bytes. -/
theorem tail_bytesAt (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.tail L (bytesAt m D len) = bytesAt m (D + BitVec.ofNat 64 (L * (len / L))) (len % L) := by
  rw [Spec.Cfb.tail, bytesAt_length, bytesAt_drop, Nat.mod_eq_sub_mul_div]

theorem tail_eq_nil_iff (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.tail L (bytesAt m D len) = [] ↔ len % L = 0 := by
  rw [tail_bytesAt, ← List.length_eq_zero_iff, bytesAt_length]

/-- The `len` bytes at `D`: its whole blocks, then the rest. -/
theorem bytesAt_blocks_tail (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    bytesAt m D len = (blocksOf L m D (len / L)).flatten ++
      bytesAt m (D + BitVec.ofNat 64 (L * (len / L))) (len % L) := by
  have h := bytesAt_add m D (L * (len / L)) (len % L)
  rw [Nat.div_add_mod] at h
  rw [h, bytesAt_mul]

/-- CFB encryption of the `len` bytes at `D` by a final function (see
above): its `n = len / L` whole blocks replaced by `Spec.Cfb.encrypt`'s
from `iv`, leaving `c`, the last ciphertext block (`Cbc.next`), and its last
`len % L` bytes XORed with `CIPH_K(c)`. -/
theorem cfbEncFinal_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ m' : Mem) (D : Addr) (iv : List Byte) (len : Nat)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))
    (htail : bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))))) :
    bytesAt m' D len = Spec.Cfb.encryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [bytesAt_blocks_tail L m' D len, hblocks, htail, Spec.Cfb.encryptFinal, segments_bytesAt, tail_bytesAt]

/-- The block a final function leaves after CFB encryption: the last
ciphertext block `c` if `len` is a multiple of `L`, and `CIPH_K(c)`
otherwise. -/
theorem cfbEncFinalNext_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (let c := Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))
      if len % L = 0 then c else ciph c) = Spec.Cfb.encryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  simp only [Spec.Cfb.encryptFinalNext, segments_bytesAt, tail_eq_nil_iff]

/-- CFB decryption of the `len` bytes at `D` by a final function (see
above): its whole blocks replaced by `Spec.Cfb.decrypt`'s from `iv`, and its
last `len % L` bytes XORed with `CIPH_K(c)`, `c` the last whole ciphertext
block (`Cbc.next`). -/
theorem cfbDecFinal_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ m' : Mem) (D : Addr) (iv : List Byte) (len : Nat)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.decrypt ciph iv (blocksOf L m₀ D (len / L)))
    (htail : bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (Spec.Cbc.next iv (blocksOf L m₀ D (len / L))))) :
    bytesAt m' D len = Spec.Cfb.decryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [bytesAt_blocks_tail L m' D len, hblocks, htail, Spec.Cfb.decryptFinal, segments_bytesAt, tail_bytesAt]

/-- The block a final function leaves after CFB decryption. -/
theorem cfbDecFinalNext_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (let c := Spec.Cbc.next iv (blocksOf L m₀ D (len / L))
      if len % L = 0 then c else ciph c) = Spec.Cfb.decryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  simp only [Spec.Cfb.decryptFinalNext, segments_bytesAt, tail_eq_nil_iff]

end VG.Proof.Modes


namespace VG.Proof.Modes

open VG
open VG.Impl.Modes (FbMode)
open VG.Spec.Aes (bytesAt)

/-- The block left after the `len` bytes: the input block after the whole
blocks if there is no partial segment, and otherwise the partial segment's
output block. -/
def fbNextF (mo : FbMode) (L : Nat) (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    List Byte :=
  if len % L = 0 then fbIn mo L ciph m₀ D iv (len / L) else ciph (fbIn mo L ciph m₀ D iv (len / L))

theorem fbNextF_length {mo : FbMode} {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem)
    (D : Addr) {iv : List Byte} (hiv : iv.length = L) (len : Nat) : (fbNextF mo L ciph m₀ D iv len).length = L := by
  unfold fbNextF
  split
  · exact fbIn_length hc m₀ D hiv _
  · exact hc _

section

variable {mo : FbMode} {L : Nat} {ciph : Spec.Cbc.Cipher} {m₀ m' : Mem} {D : Addr} {iv : List Byte} {len : Nat}

/-- The whole blocks, from the bytes. -/
theorem fbFinal_blocks (hc : ∀ b, (ciph b).length = L)
    (h : ∀ i < len, m' (D + BitVec.ofNat 64 i) = (fbOut mo L ciph m₀ D iv (i / L)).getD (i % L) 0) :
    blocksOf L m' D (len / L) = (List.range (len / L)).map (fbOut mo L ciph m₀ D iv) :=
  blocksOf_of_dinv (m₀ := m₀) (fbOut_length hc m₀ D iv) fun i hi => by
    rw [ite_eq_left hi]
    exact h i (Nat.lt_of_lt_of_le hi (Nat.mul_div_le len L))

/-- The partial segment, from the bytes: XORed with `CIPH_K` of its input
block. -/
theorem fbFinal_tail (hL : 0 < L) (hc : ∀ b, (ciph b).length = L)
    (h : ∀ i < len, m' (D + BitVec.ofNat 64 i) = (fbOut mo L ciph m₀ D iv (i / L)).getD (i % L) 0) :
    bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (fbIn mo L ciph m₀ D iv (len / L))) := by
  have hr : len % L < L := Nat.mod_lt _ hL
  have hlen : L * (len / L) + len % L = len := Nat.div_add_mod _ _
  apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, hc]; omega)
  intro q h1 h2
  have hq : q < len % L := by simpa [bytesAt] using h1
  rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, xor_getD (by simpa [bytesAt] using hq) (by rw [hc]; omega)]
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hq, Option.map_some,
    Option.getD_some, VG.Offset.add_add]
  rw [h _ (by omega), idx_div (by omega), idx_mod (by omega), fbOut_getD mo hc m₀ D iv _ (by omega),
    List.getD_eq_getElem?_getD]

end

/-- CFB encryption of the `len` bytes at `D`, from the bytes and the block a
final function leaves. -/
theorem cfbEncFinal_of_bytes {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    {m₀ m' : Mem} {D : Addr} {iv : List Byte} {len : Nat}
    (h : ∀ i < len, m' (D + BitVec.ofNat 64 i) = (fbOut .cfbEnc L ciph m₀ D iv (i / L)).getD (i % L) 0) :
    bytesAt m' D len = Spec.Cfb.encryptFinal ciph L iv (bytesAt m₀ D len) ∧
      fbNextF .cfbEnc L ciph m₀ D iv len = Spec.Cfb.encryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  obtain ⟨hb, hn⟩ := cfbEnc_of L ciph m₀ D iv (len / L)
  refine ⟨cfbEncFinal_of ciph m₀ m' D iv len (by rw [fbFinal_blocks hc h, hb]) ?_, ?_⟩
  · rw [fbFinal_tail hL hc h, hn]
  · rw [fbNextF, hn]; exact cfbEncFinalNext_of ciph m₀ D iv len

/-- CFB decryption of the `len` bytes at `D`, from the bytes and the block a
final function leaves. -/
theorem cfbDecFinal_of_bytes {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    {m₀ m' : Mem} {D : Addr} {iv : List Byte} {len : Nat}
    (h : ∀ i < len, m' (D + BitVec.ofNat 64 i) = (fbOut .cfbDec L ciph m₀ D iv (i / L)).getD (i % L) 0) :
    bytesAt m' D len = Spec.Cfb.decryptFinal ciph L iv (bytesAt m₀ D len) ∧
      fbNextF .cfbDec L ciph m₀ D iv len = Spec.Cfb.decryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  obtain ⟨hb, hn⟩ := cfbDec_of L ciph m₀ D iv (len / L)
  refine ⟨cfbDecFinal_of ciph m₀ m' D iv len (by rw [fbFinal_blocks hc h, hb]) ?_, ?_⟩
  · rw [fbFinal_tail hL hc h, hn]
  · rw [fbNextF, hn]; exact cfbDecFinalNext_of ciph m₀ D iv len

/-! ## OFB of a message's last piece -/

/-- The number of blocks of `len` bytes, the last possibly partial:
`len / L`, and one more if `len % L ≠ 0`. -/
theorem blockCount_eq {L : Nat} (hL : 0 < L) (len : Nat) :
    Spec.Ofb.blockCount L len = if len % L = 0 then len / L else len / L + 1 := by
  have hd := Nat.div_add_mod len L
  have hr := Nat.mod_lt len hL
  unfold Spec.Ofb.blockCount
  generalize len / L = n at hd
  generalize len % L = r at hd hr
  subst hd
  split
  · subst r
    rw [Nat.add_zero, Nat.add_sub_assoc (by omega), Nat.mul_add_div hL, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  · rw [Nat.add_assoc, Nat.add_sub_assoc (by omega), Nat.mul_add_div hL,
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]

theorem length_flatten_outputs {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) :
    ∀ (n : Nat) (iv : List Byte), (Spec.Ofb.outputs ciph iv n).flatten.length = L * n
  | 0, _ => rfl
  | n + 1, iv => by
    rw [outputs_succ, List.flatten_cons, List.length_append, hc, length_flatten_outputs hc n, Nat.mul_succ,
      Nat.add_comm]

/-- XORing `n` blocks with OFB's `n` output blocks, all at once. -/
theorem xor_flatten_outputs {L : Nat} {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L) (m₀ : Mem) :
    ∀ (n : Nat) (D : Addr) (iv : List Byte),
      Spec.Cbc.xor (blocksOf L m₀ D n).flatten (Spec.Ofb.outputs ciph iv n).flatten =
        (List.zipWith Spec.Cbc.xor (blocksOf L m₀ D n) (Spec.Ofb.outputs ciph iv n)).flatten
  | 0, _, _ => rfl
  | n + 1, D, iv => by
    rw [blocksOf_succ, outputs_succ, List.flatten_cons, List.flatten_cons, List.zipWith_cons_cons,
      List.flatten_cons, ← xor_flatten_outputs hc m₀ n]
    exact List.zipWith_append (by rw [hc, bytesAt_length])

/-- OFB of the `len` bytes at `D`, as a final function leaves them: its
`n = len / L` whole blocks as `Spec.Ofb.crypt`'s from `iv`, then its last
`len % L` bytes XORed with `CIPH_K(Oₙ)`, `Oₙ` the last whole output block
(`Spec.Ofb.next` after `n`): `Spec.Ofb.cryptFinal`. -/
theorem ofbFinal_out {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (Spec.Ofb.crypt ciph iv (blocksOf L m₀ D (len / L))).flatten ++
        Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
          (ciph (Spec.Ofb.next ciph iv (len / L))) =
      Spec.Ofb.cryptFinal ciph L iv (bytesAt m₀ D len) := by
  have hx := xor_flatten_outputs hc m₀ (len / L) D iv
  have hnB : (blocksOf L m₀ D (len / L)).length = len / L := by simp [blocksOf]
  rw [Spec.Ofb.cryptFinal, bytesAt_length, blockCount_eq hL, bytesAt_blocks_tail L m₀ D len, Spec.Ofb.crypt, hnB]
  split
  · rename_i h0
    rw [h0, ← hx]
    simp [bytesAt, Spec.Cbc.xor]
  · rw [AesOfb.outputs_succ, List.flatten_append, List.flatten_singleton, ← hx]
    exact (List.zipWith_append (by rw [← bytesAt_mul, bytesAt_length, length_flatten_outputs hc])).symm

/-- OFB of the `len` bytes at `D` by a final function: its `n = len / L`
whole blocks replaced by `Spec.Ofb.crypt`'s from `iv`, and its last
`len % L` bytes XORed with `CIPH_K(Oₙ)`, `Oₙ` the last whole output block
(`Spec.Ofb.next` after `n`): `Spec.Ofb.cryptFinal`. -/
theorem ofbFinal_of {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    (m₀ m' : Mem) (D : Addr) (iv : List Byte) (len : Nat)
    (hblocks : blocksOf L m' D (len / L) = Spec.Ofb.crypt ciph iv (blocksOf L m₀ D (len / L)))
    (htail : bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (Spec.Ofb.next ciph iv (len / L)))) :
    bytesAt m' D len = Spec.Ofb.cryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [bytesAt_blocks_tail L m' D len, hblocks, htail]
  exact ofbFinal_out hL hc m₀ D iv len

/-- OFB of the `len` bytes at `D`, from the bytes and the block a final
function leaves: `Spec.Ofb.cryptFinal`, and the last output block used,
`Spec.Ofb.next` after `⌈len / L⌉` blocks. -/
theorem ofbFinal_of_bytes {L : Nat} (hL : 0 < L) {ciph : Spec.Cbc.Cipher} (hc : ∀ b, (ciph b).length = L)
    {m₀ m' : Mem} {D : Addr} {iv : List Byte} {len : Nat}
    (h : ∀ i < len, m' (D + BitVec.ofNat 64 i) = (fbOut .ofb L ciph m₀ D iv (i / L)).getD (i % L) 0) :
    bytesAt m' D len = Spec.Ofb.cryptFinal ciph L iv (bytesAt m₀ D len) ∧
      fbNextF .ofb L ciph m₀ D iv len = Spec.Ofb.next ciph iv (Spec.Ofb.blockCount L len) := by
  obtain ⟨hb, hn⟩ := ofb_of L ciph m₀ D iv (len / L)
  have hT := fbFinal_tail hL hc h
  rw [hn] at hT
  refine ⟨ofbFinal_of hL hc m₀ m' D iv len (by rw [fbFinal_blocks hc h, hb]) hT, ?_⟩
  · rw [fbNextF, hn, blockCount_eq hL]
    split
    · rfl
    · exact (AesOfb.next_succ ciph iv _).symm

end VG.Proof.Modes

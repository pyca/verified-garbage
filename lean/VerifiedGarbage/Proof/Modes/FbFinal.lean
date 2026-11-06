module

public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.Modes.CfbFinal
import VerifiedGarbage.Proof.Modes.Cbc
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# OFB's and CFB's results on a message's last piece, for any block cipher and target

A feedback mode's loop over the `len` bytes of a message's last piece, in
segments of a block of `L` bytes the last of which may be partial
(`Impl/Modes/<Target>/FbFinal.lean`), makes byte `i` that of `fbOut` of its
block, and leaves the block to continue from, `fbNextF`: the input block
after the whole blocks, or the partial segment's output block. When it has,
the data and the block are `Spec.Cfb.encryptFinal`'s and
`encryptFinalNext`'s (`cfbEncFinal_of_bytes`), or `decryptFinal`'s and
`decryptFinalNext`'s (`cfbDecFinal_of_bytes`). Nothing here depends on a
cipher or a target.
-/

@[expose] public section

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

end VG.Proof.Modes

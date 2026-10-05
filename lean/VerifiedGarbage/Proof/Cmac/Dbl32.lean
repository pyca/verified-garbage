import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Gcm.Bits

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Spec`. -/
section

/-!
# CMAC: lemmas about the specification

* `macFull_split`: the MAC of a message of whole blocks followed by its last
  bytes `Mₙ*` (at most a block, and some unless the message is empty) is the
  cipher of the chaining value of the whole blocks XORed with `Mₙ` (§6.2
  steps 3–6), which is how `update` and `finalize` compute it.
* `ctr32_one`: counter mode on one zero block is the cipher of the counter
  block, which is how the implementations call `vg_aes_ctr32`: as bytes,
  `Spec.Gcm.toBytes (aesWith nr w (Spec.Gcm.ofBytes x)) = Cmac.aesWith nr w x`.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-! ## Lists of bytes -/

theorem length_xor (x y : List Byte) : (Spec.Cmac.xor x y).length = min x.length y.length := by
  simp [Spec.Cmac.xor]

theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]

theorem getD_xor {x y : List Byte} (h : x.length = y.length) {k : Nat} (hk : k < x.length) :
    (Spec.Cmac.xor x y).getD k 0 = x.getD k 0 ^^^ y.getD k 0 := by
  simp only [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k < y.length by omega)]
  rfl

/-- Lists of 16 bytes are equal if their bytes are. -/
theorem ext16 {x y : List Byte} (hx : x.length = 16) (hy : y.length = 16)
    (h : ∀ k < 16, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem (by rw [hx, hy])
  intro k h₁ h₂
  have := h k (by omega)
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

/-! ## Splitting the MAC -/

theorem chain_append (ciph : Cipher) (c : List Byte) (xs ys : List (List Byte)) :
    chain ciph c (xs ++ ys) = chain ciph (chain ciph c xs) ys := by
  simp [chain, List.foldl_append]

theorem chain_single (ciph : Cipher) (c m : List Byte) : chain ciph c [m] = ciph (xor c m) := rfl

theorem blocks_eq {msg : List Byte} (hm : msg.length % 16 = 0) (last : List Byte) (q : Nat)
    (hq : msg.length = 16 * q) :
    (List.range q).map (fun i => ((msg ++ last).drop (16 * i)).take 16) = blocks 16 msg := by
  simp only [blocks, hq, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- §6.2 steps 3–6, for a message of whole blocks `msg` followed by `last`. -/
theorem macFull_split (ciph : Cipher) {msg last : List Byte} (hm : msg.length % 16 = 0)
    (hl : last.length ≤ 16) (hne : msg = [] ∨ 0 < last.length) :
    macFull ciph 16 (msg ++ last) =
      ciph (xor (chain ciph (zeros 16) (blocks 16 msg))
        (lastBlock 16 (subkeys ciph 16).1 (subkeys ciph 16).2 last)) := by
  obtain ⟨q, hq⟩ : ∃ q, msg.length = 16 * q := ⟨msg.length / 16, by omega⟩
  have hn : (if (msg ++ last).length = 0 then 1 else ((msg ++ last).length + 16 - 1) / 16) = q + 1 := by
    rw [List.length_append]
    split
    · omega
    · have hl0 : 0 < last.length := by
        rcases hne with h | h
        · subst h; simp only [List.length_nil] at *; omega
        · exact h
      omega
  simp only [macFull, hn, Nat.add_sub_cancel]
  rw [VG.Proof.Cmac.blocks_eq hm last q hq, VG.Proof.Cmac.chain_append, VG.Proof.Cmac.chain_single,
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

/-! ## One block of counter mode -/

theorem toBytes_length (x : Spec.Gcm.Block) : (Spec.Gcm.toBytes x).length = 16 := by simp [Spec.Gcm.toBytes]

theorem toBytes_ofBytes {bs : List Byte} (h : bs.length = 16) : Spec.Gcm.toBytes (Spec.Gcm.ofBytes bs) = bs :=
  VG.Proof.Cmac.ext16 (VG.Proof.Cmac.toBytes_length _) h fun _ hk => Proof.Aes.toBytes_ofBytes h hk

theorem ctr32_one (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [0] = [ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem aesWith_bytes (nr : Nat) (w : List Byte) {x : List Byte} (h : x.length = 16) :
    Spec.Gcm.toBytes (Spec.Gcm.aesWith nr w (Spec.Gcm.ofBytes x)) = aesWith nr w x := by
  rw [Spec.Gcm.aesWith, VG.Proof.Cmac.toBytes_ofBytes (by simp), aesWith]
  refine congrArg (fun v => (Spec.Aes.cipher nr w v).toList) ?_
  exact Vector.ext fun i hi => by simpa only [Vector.getElem_ofFn] using Proof.Aes.toBytes_ofBytes h hi

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Aes.bytesAt m p n).length = n := by
  simp [Spec.Aes.bytesAt]

theorem bytesAt_blockAt (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Gcm.toBytes (Spec.Gcm.blockAt m p) :=
  (VG.Proof.Cmac.toBytes_ofBytes (VG.Proof.Cmac.bytesAt_length m p 16)).symm

/-! ## Lengths -/

theorem aesWith_length (nr : Nat) (w x : List Byte) : (aesWith nr w x).length = 16 := by simp [aesWith]

theorem dbl_length {x : List Byte} (h : x.length = 16) : (dbl 16 x).length = 16 := by
  unfold dbl; split <;> simp [shiftLeft1, VG.Proof.Cmac.length_xor, rb, zeros, h]

theorem subkeys_aes_length (nr : Nat) (w : List Byte) : (subkeys (aesWith nr w) 16).1.length = 16 :=
  VG.Proof.Cmac.dbl_length (VG.Proof.Cmac.aesWith_length _ _ _)

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Mem`. -/
section

/-!
# CMAC: blocks in memory as 64-bit words

A 16-byte block is loaded and stored as two little-endian 64-bit words:
`le8 w` is the bytes of the word `w`, so the bytes at `p` are
`le8 (readW p) ++ le8 (readW (p + BitVec.ofNat 64 8))`, and storing `w₀` at `p` and `w₁` at
`p + 8` leaves `le8 w₀ ++ le8 w₁` there.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-- The bytes of a 64-bit word, least significant first. -/
def le8 (w : BitVec 64) : List Byte := (List.range 8).map fun i => w.extractLsb' (8 * i) 8

theorem length_le8 (w : BitVec 64) : (VG.Proof.Cmac.le8 w).length = 8 := by simp [VG.Proof.Cmac.le8]

theorem getD_le8 (w : BitVec 64) {k : Nat} (hk : k < 8) : (VG.Proof.Cmac.le8 w).getD k 0 = w.extractLsb' (8 * k) 8 := by
  simp [VG.Proof.Cmac.le8, List.getD_eq_getElem?_getD, hk]

theorem getD_bytesAt (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem le8_readW (m : Mem) (a : Addr) : VG.Proof.Cmac.le8 (m.readW a 64) = Spec.Aes.bytesAt m a 8 := by
  apply List.ext_getElem (by simp [VG.Proof.Cmac.le8, Spec.Aes.bytesAt])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [VG.Proof.Cmac.le8] using h₁
  simp only [VG.Proof.Cmac.le8, Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a (n := 8) hk]
  simp only [Mem.readW]
  rfl

theorem le8_xor (a b : BitVec 64) : VG.Proof.Cmac.le8 (a ^^^ b) = Spec.Cmac.xor (VG.Proof.Cmac.le8 a) (VG.Proof.Cmac.le8 b) := by
  apply List.ext_getElem (by simp [VG.Proof.Cmac.le8, Spec.Cmac.xor])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [VG.Proof.Cmac.le8] using h₁
  simp only [VG.Proof.Cmac.le8, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem le8_zero : VG.Proof.Cmac.le8 0 = zeros 8 := by decide

theorem bytesAt_split (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Aes.bytesAt m p 8 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 8) 8 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (16 : Nat) = 8 + 8 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes of a block after storing its two words. -/
theorem bytesAt_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p 16 = VG.Proof.Cmac.le8 w₀ ++ VG.Proof.Cmac.le8 w₁ := by
  have hs : Mem.Sep p (64 / 8) (p + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep p (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  have h₀ : Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p 8 = VG.Proof.Cmac.le8 w₀ := by
    rw [← VG.Proof.Cmac.le8_readW, Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64]
  have h₁ : Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) (p + BitVec.ofNat 64 8) 8 = VG.Proof.Cmac.le8 w₁ := by
    rw [← VG.Proof.Cmac.le8_readW, Mem.readW_writeW_self64]
  rw [VG.Proof.Cmac.bytesAt_split, h₀, h₁]

theorem xor_append {a b c d : List Byte} (h : a.length = c.length) :
    Spec.Cmac.xor (a ++ b) (c ++ d) = Spec.Cmac.xor a c ++ Spec.Cmac.xor b d := by
  simp [Spec.Cmac.xor, List.zipWith_append h]

/-- The XOR of two blocks, a word at a time. -/
theorem xor_words (m : Mem) (p q : Addr) :
    VG.Proof.Cmac.le8 (m.readW p 64 ^^^ m.readW q 64) ++ VG.Proof.Cmac.le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64) =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [VG.Proof.Cmac.le8_xor, VG.Proof.Cmac.le8_xor, VG.Proof.Cmac.le8_readW, VG.Proof.Cmac.le8_readW, VG.Proof.Cmac.le8_readW, VG.Proof.Cmac.le8_readW, VG.Proof.Cmac.bytesAt_split m p,
    VG.Proof.Cmac.bytesAt_split m q, VG.Proof.Cmac.xor_append (by simp [Spec.Aes.bytesAt])]

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Frame`. -/
section

/-!
# CMAC: blocks in memory under frames

What the implementations' stores of 64-bit words leave in memory, on any
target: the bytes outside a frame are unchanged (`bytesAt_frame`), and the
memory after forming a counter block `C = P ⊕ Q` and zeroing `P`
(`chainMem`), as each block of `update` does.
-/

namespace VG.Proof.Cmac

open VG

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem bytesAt_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Aes.bytesAt m' p 16 = Spec.Aes.bytesAt m p 16 :=
  VG.Proof.Cmac.bytesAt_frame hf hd (by decide)

theorem frame_store2 {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

/-- The memory after forming a counter block: the block at `c` is the block
at `p` XORed with the block at `q`, and the block at `p` is zeroed. -/
def chainMem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)
  (m₂.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem chainMem_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (VG.Proof.Cmac.chainMem m C P Q) := by
  have f₁ : Frame [⟨C, 16⟩, ⟨P, 16⟩] m _ :=
    (VG.Proof.Cmac.frame_store2 (m := m) C (m.readW P 64 ^^^ m.readW Q 64)
      ((m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (P + BitVec.ofNat 64 8) 64 ^^^
        (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (Q + BitVec.ofNat 64 8) 64)).mono
      (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  exact f₁.trans ((VG.Proof.Cmac.frame_store2 P 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.chainMem m C P Q) P 16 = Spec.Cmac.zeros 16 := by
  rw [VG.Proof.Cmac.chainMem, VG.Proof.Cmac.bytesAt_store2, VG.Proof.Cmac.le8_zero]; rfl

theorem chainMem_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.chainMem m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [VG.Proof.Cmac.chainMem, VG.Proof.Cmac.bytesAt_frame16 (VG.Proof.Cmac.frame_store2 P 0 0) (by simpa using hcp), VG.Proof.Cmac.bytesAt_store2]
  have g : Frame [⟨C, 16⟩] m (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base C (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  rw [VG.Proof.Cmac.readW_frame16 g (d := 8) (by decide) (by simpa using hcp.symm),
    VG.Proof.Cmac.readW_frame16 g (d := 8) (by decide) (by simpa using hcq.symm)]
  exact VG.Proof.Cmac.xor_words m P Q

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Block`. -/
section

/-!
# CMAC: forming the last block in memory

What `finalize`'s stores leave, on any target: the XOR of two blocks stored a
word at a time (`xor2Mem`), a zeroed block (`zero2`), and a partial last
block copied onto zeros and padded with `0x80` (`padded_bytes`).
-/

namespace VG.Proof.Cmac

open VG

/-! ## XORing two blocks, a word at a time -/

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`,
a word at a time. -/
def xor2Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)

theorem xor2Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (VG.Proof.Cmac.xor2Mem m c p q) := VG.Proof.Cmac.frame_store2 _ _ _

theorem xor2Mem_bytes (m : Mem) {c p q : Addr}
    (hp : (⟨c, 8⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 8⟩)
    (hq : (⟨c, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.xor2Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  have g : Frame [⟨c, 8⟩] m (m.writeW c (m.readW p 64 ^^^ m.readW q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [VG.Proof.Cmac.xor2Mem, VG.Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.symm) (by decide),
    g.readW (r := ⟨q + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.symm) (by decide)]
  exact VG.Proof.Cmac.xor_words m p q

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Zeroing, copying and padding -/

theorem zeros_8_8 : Spec.Cmac.zeros 8 ++ Spec.Cmac.zeros 8 = Spec.Cmac.zeros 16 := by decide

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (0 : BitVec 64)).writeW (c + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem zero2_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (VG.Proof.Cmac.zero2 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [VG.Proof.Cmac.zero2, VG.Proof.Cmac.bytesAt_store2, VG.Proof.Cmac.le8_zero, VG.Proof.Cmac.zeros_8_8]

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

theorem bytesAt_32 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 32 = Spec.Aes.bytesAt m p 16 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 16) 16 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (32 : Nat) = 16 + 16 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The two subkeys, from the 32 bytes after the key schedule. -/
theorem k1k2 {m : Mem} {W : Addr} {k1 k2 : List Byte} (h1 : k1.length = 16)
    (h : Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 32 = k1 ++ k2) :
    Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16 = k1 ∧ Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16 = k2 := by
  rw [VG.Proof.Cmac.bytesAt_32, Offset.add_add] at h
  exact List.append_inj h (by rw [VG.Proof.Cmac.bytesAt_length, h1])

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 16)
    (hz : Spec.Aes.bytesAt m C 16 = Spec.Cmac.zeros 16) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 16 =
      xs ++ [0x80] ++ Spec.Cmac.zeros (16 - xs.length - 1) := by
  refine VG.Proof.Cmac.ext16 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Cmac.zeros]; omega) fun k hk => ?_
  rw [VG.Proof.Cmac.getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [VG.Proof.Cmac.getD_bytesAt _ _ hk] at this
    rw [this]; simp only [Spec.Cmac.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega, ite_true, Option.getD_some]

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Mem32`. -/
section

/-!
# CMAC: blocks in memory as 32-bit words

On the 32-bit targets a 16-byte block is loaded and stored as four
little-endian 32-bit words: `le4 w` is the bytes of the word `w`, and storing
`w₀ … w₃` at `p`, `p + 4`, `p + 8` and `p + 12` (`store4`) leaves
`le4 w₀ ++ … ++ le4 w₃` there. `xor4Mem` stores the XOR of two blocks a
word at a time (the block written may be one of those read), `zero4` zeroes
a block, and `chainMem4` forms a counter block `C = P ⊕ Q` and zeroes `P`.
-/

namespace VG.Proof.Cmac

open VG

/-- The bytes of a 32-bit word, least significant first. -/
def le4 (w : BitVec 32) : List Byte := (List.range 4).map fun i => w.extractLsb' (8 * i) 8

theorem length_le4 (w : BitVec 32) : (VG.Proof.Cmac.le4 w).length = 4 := by simp [VG.Proof.Cmac.le4]

theorem getD_le4 (w : BitVec 32) {k : Nat} (hk : k < 4) : (VG.Proof.Cmac.le4 w).getD k 0 = w.extractLsb' (8 * k) 8 := by
  simp [VG.Proof.Cmac.le4, List.getD_eq_getElem?_getD, hk]

theorem le4_readW (m : Mem) (a : Addr) : VG.Proof.Cmac.le4 (m.readW a 32) = Spec.Aes.bytesAt m a 4 := by
  apply List.ext_getElem (by simp [VG.Proof.Cmac.le4, Spec.Aes.bytesAt])
  intro k h₁ h₂
  have hk : k < 4 := by simpa [VG.Proof.Cmac.le4] using h₁
  simp only [VG.Proof.Cmac.le4, Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a (n := 4) hk]
  simp only [Mem.readW]
  rfl

theorem le4_xor (a b : BitVec 32) : VG.Proof.Cmac.le4 (a ^^^ b) = Spec.Cmac.xor (VG.Proof.Cmac.le4 a) (VG.Proof.Cmac.le4 b) := by
  apply List.ext_getElem (by simp [VG.Proof.Cmac.le4, Spec.Cmac.xor])
  intro k h₁ h₂
  have hk : k < 4 := by simpa [VG.Proof.Cmac.le4] using h₁
  simp only [VG.Proof.Cmac.le4, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem le4_zero : VG.Proof.Cmac.le4 0 = Spec.Cmac.zeros 4 := by decide

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Aes.bytesAt m p (a + b) = Spec.Aes.bytesAt m p a ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Aes.bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- A block as its four words' bytes. -/
theorem bytesAt_split4 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Aes.bytesAt m p 4 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 4) 4 ++
      Spec.Aes.bytesAt m (p + BitVec.ofNat 64 8) 4 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 12) 4 := by
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, VG.Proof.Cmac.bytesAt_add, VG.Proof.Cmac.bytesAt_add, VG.Proof.Cmac.bytesAt_add]
  simp only [Offset.add_add, List.append_assoc]

/-- The four words `w₀ … w₃` stored at `p`. -/
def store4 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) : Mem :=
  (((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8) w₂).writeW
    (p + BitVec.ofNat 64 12) w₃

theorem frame_store4 {m : Mem} (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    Frame [⟨p, 16⟩] m (VG.Proof.Cmac.store4 m p w₀ w₁ w₂ w₃) := by
  have c (d : Nat) (h : d + 4 ≤ 16) : (⟨p, 16⟩ : Region).Contains (p + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base p h (by omega)
  have c0 : (⟨p, 16⟩ : Region).Contains p 4 := by simpa using c 0 (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _
    (c 4 (by decide))).writeW (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 12 (by decide))

theorem readW_store4_of_sep {m : Mem} {p a : Addr} (w₀ w₁ w₂ w₃ : BitVec 32) (h : (⟨p, 16⟩ : Region).Disjoint ⟨a, 4⟩) :
    (VG.Proof.Cmac.store4 m p w₀ w₁ w₂ w₃).readW a 32 = m.readW a 32 :=
  (VG.Proof.Cmac.frame_store4 (m := m) p w₀ w₁ w₂ w₃).readW (r := ⟨a, 4⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm) (by decide)

/-- The bytes of a block after storing its four words. -/
theorem bytesAt_store4 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.store4 m p w₀ w₁ w₂ w₃) p 16 = VG.Proof.Cmac.le4 w₀ ++ VG.Proof.Cmac.le4 w₁ ++ VG.Proof.Cmac.le4 w₂ ++ VG.Proof.Cmac.le4 w₃ := by
  have sep (d e : Nat) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (he : e + 4 ≤ 16) (hd : d + 4 ≤ 16) :
      Mem.Sep (p + BitVec.ofNat 64 d) (32 / 8) (p + BitVec.ofNat 64 e) (32 / 8) :=
    Offset.sep p h (by omega) (by omega)
  rw [VG.Proof.Cmac.bytesAt_split4, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.store4]
  rw [Mem.readW_writeW_self32, Mem.readW_writeW_sep (sep 8 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32, Mem.readW_writeW_sep (sep 4 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 4 8 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  rw [Mem.readW_writeW_sep (by simpa using sep 0 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (by simpa using sep 0 8 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (by simpa using sep 0 4 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem xor_append4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length) :
    Spec.Cmac.xor (a ++ b ++ c ++ d) (a' ++ b' ++ c' ++ d') =
      Spec.Cmac.xor a a' ++ Spec.Cmac.xor b b' ++ Spec.Cmac.xor c c' ++ Spec.Cmac.xor d d' := by
  simp only [List.append_assoc]
  rw [VG.Proof.Cmac.xor_append ha, VG.Proof.Cmac.xor_append hb, VG.Proof.Cmac.xor_append hc]

/-- The XOR of two blocks, a word at a time. -/
theorem xor_words4 (m : Mem) (p q : Addr) :
    VG.Proof.Cmac.le4 (m.readW p 32 ^^^ m.readW q 32) ++
      VG.Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 4) 32 ^^^ m.readW (q + BitVec.ofNat 64 4) 32) ++
      VG.Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 8) 32 ^^^ m.readW (q + BitVec.ofNat 64 8) 32) ++
      VG.Proof.Cmac.le4 (m.readW (p + BitVec.ofNat 64 12) 32 ^^^ m.readW (q + BitVec.ofNat 64 12) 32) =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [VG.Proof.Cmac.le4_xor, VG.Proof.Cmac.le4_xor, VG.Proof.Cmac.le4_xor, VG.Proof.Cmac.le4_xor, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW,
    VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.le4_readW, VG.Proof.Cmac.bytesAt_split4 m p, VG.Proof.Cmac.bytesAt_split4 m q,
    VG.Proof.Cmac.xor_append4 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Aes.bytesAt])]

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Block32`. -/
section

/-!
# CMAC: blocks formed a 32-bit word at a time

What the 32-bit targets' stores leave: the XOR of two blocks stored a word at
a time (`xor4Mem`; the block written may be one of those read, as long as no
word written is read afterwards, `Sep4`), a zeroed block (`zero4`), and a
counter block `C = P ⊕ Q` with `P` zeroed (`chainMem4`).
-/

namespace VG.Proof.Cmac

open VG

/-- No word written at `c` is read at `p` after it: the word `i` written is
disjoint from every word `j > i` of `p`. -/
def Sep4 (c p : Addr) : Prop :=
  ∀ i < 4, ∀ j < 4, i < j → (⟨c + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 (4 * j), 4⟩

theorem Sep4.self (c : Addr) : VG.Proof.Cmac.Sep4 c c := fun i hi j hj hij =>
  Offset.disjoint c (by omega) (by omega) (by omega)

theorem Sep4.of_disjoint {c p : Addr} (h : (⟨c, 16⟩ : Region).Disjoint ⟨p, 16⟩) : VG.Proof.Cmac.Sep4 c p :=
  fun i hi j hj _ => (h.sub_left (Offset.sub_base c (by omega))).sub_right (Offset.sub_base p (by omega))

theorem readW_writeW_disj {m : Mem} {a b : Addr} (v : BitVec 32) (h : (⟨a, 4⟩ : Region).Disjoint ⟨b, 4⟩) :
    (m.writeW a v).readW b 32 = m.readW b 32 :=
  Mem.readW_writeW_sep (h.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`, a
word at a time. -/
def xor4Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 32 ^^^ m.readW q 32)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 4)
    (m₁.readW (p + BitVec.ofNat 64 4) 32 ^^^ m₁.readW (q + BitVec.ofNat 64 4) 32)
  let m₃ := m₂.writeW (c + BitVec.ofNat 64 8)
    (m₂.readW (p + BitVec.ofNat 64 8) 32 ^^^ m₂.readW (q + BitVec.ofNat 64 8) 32)
  m₃.writeW (c + BitVec.ofNat 64 12) (m₃.readW (p + BitVec.ofNat 64 12) 32 ^^^ m₃.readW (q + BitVec.ofNat 64 12) 32)

theorem xor4Mem_eq (m : Mem) {c p q : Addr} (hp : VG.Proof.Cmac.Sep4 c p) (hq : VG.Proof.Cmac.Sep4 c q) :
    VG.Proof.Cmac.xor4Mem m c p q = VG.Proof.Cmac.store4 m c (m.readW p 32 ^^^ m.readW q 32)
      (m.readW (p + BitVec.ofNat 64 4) 32 ^^^ m.readW (q + BitVec.ofNat 64 4) 32)
      (m.readW (p + BitVec.ofNat 64 8) 32 ^^^ m.readW (q + BitVec.ofNat 64 8) 32)
      (m.readW (p + BitVec.ofNat 64 12) 32 ^^^ m.readW (q + BitVec.ofNat 64 12) 32) := by
  have e (x : Addr) (h : VG.Proof.Cmac.Sep4 c x) (i j : Nat) (hi : i < 4) (hj : j < 4) (hij : i < j) :
      (⟨c + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint ⟨x + BitVec.ofNat 64 (4 * j), 4⟩ := h i hi j hj hij
  have p01 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by simpa using e p hp 0 1 (by decide) (by decide) (by decide)
  have q01 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 4, 4⟩ := by simpa using e q hq 0 1 (by decide) (by decide) (by decide)
  have p02 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by simpa using e p hp 0 2 (by decide) (by decide) (by decide)
  have q02 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 4⟩ := by simpa using e q hq 0 2 (by decide) (by decide) (by decide)
  have p03 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by simpa using e p hp 0 3 (by decide) (by decide) (by decide)
  have q03 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := by simpa using e q hq 0 3 (by decide) (by decide) (by decide)
  have p12 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := e p hp 1 2 (by decide) (by decide) (by decide)
  have q12 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 4⟩ := e q hq 1 2 (by decide) (by decide) (by decide)
  have p13 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := e p hp 1 3 (by decide) (by decide) (by decide)
  have q13 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := e q hq 1 3 (by decide) (by decide) (by decide)
  have p23 : (⟨c + BitVec.ofNat 64 8, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := e p hp 2 3 (by decide) (by decide) (by decide)
  have q23 : (⟨c + BitVec.ofNat 64 8, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := e q hq 2 3 (by decide) (by decide) (by decide)
  simp only [VG.Proof.Cmac.xor4Mem, VG.Proof.Cmac.store4, VG.Proof.Cmac.readW_writeW_disj _ p01, VG.Proof.Cmac.readW_writeW_disj _ q01, VG.Proof.Cmac.readW_writeW_disj _ p02,
    VG.Proof.Cmac.readW_writeW_disj _ q02, VG.Proof.Cmac.readW_writeW_disj _ p03, VG.Proof.Cmac.readW_writeW_disj _ q03, VG.Proof.Cmac.readW_writeW_disj _ p12,
    VG.Proof.Cmac.readW_writeW_disj _ q12, VG.Proof.Cmac.readW_writeW_disj _ p13, VG.Proof.Cmac.readW_writeW_disj _ q13, VG.Proof.Cmac.readW_writeW_disj _ p23,
    VG.Proof.Cmac.readW_writeW_disj _ q23]

theorem xor4Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (VG.Proof.Cmac.xor4Mem m c p q) := by
  have k (d : Nat) (h : d + 4 ≤ 16) : (⟨c, 16⟩ : Region).Contains (c + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base c h (by omega)
  have k0 : (⟨c, 16⟩ : Region).Contains c 4 := by simpa using k 0 (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ k0).writeW (List.mem_singleton_self _) _
    (k 4 (by decide))).writeW (List.mem_singleton_self _) _ (k 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (k 12 (by decide))

theorem xor4Mem_bytes (m : Mem) {c p q : Addr} (hp : VG.Proof.Cmac.Sep4 c p) (hq : VG.Proof.Cmac.Sep4 c q) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.xor4Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [VG.Proof.Cmac.xor4Mem_eq m hp hq, VG.Proof.Cmac.bytesAt_store4, VG.Proof.Cmac.xor_words4]

/-- The memory after zeroing the block at `c`, a word at a time. -/
def zero4 (m : Mem) (c : Addr) : Mem := VG.Proof.Cmac.store4 m c 0 0 0 0

theorem zero4_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (VG.Proof.Cmac.zero4 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [VG.Proof.Cmac.zero4, VG.Proof.Cmac.bytesAt_store4, VG.Proof.Cmac.le4_zero]; decide

/-- The memory after forming a counter block: the block at `c` is the block
at `p` XORed with the block at `q`, and the block at `p` is zeroed. -/
def chainMem4 (m : Mem) (c p q : Addr) : Mem := VG.Proof.Cmac.zero4 (VG.Proof.Cmac.xor4Mem m c p q) p

theorem chainMem4_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (VG.Proof.Cmac.chainMem4 m C P Q) :=
  ((VG.Proof.Cmac.xor4Mem_frame m C P Q).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])).trans
    ((VG.Proof.Cmac.frame_store4 P 0 0 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem4_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.chainMem4 m C P Q) P 16 = Spec.Cmac.zeros 16 := VG.Proof.Cmac.zero4_bytes _ _

theorem chainMem4_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (VG.Proof.Cmac.chainMem4 m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [VG.Proof.Cmac.chainMem4, VG.Proof.Cmac.zero4, VG.Proof.Cmac.bytesAt_frame16 (VG.Proof.Cmac.frame_store4 P 0 0 0 0) (by simpa using hcp),
    VG.Proof.Cmac.xor4Mem_bytes m (Sep4.of_disjoint hcp) (Sep4.of_disjoint hcq)]

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Dbl`. -/
section

/-!
# CMAC: doubling a 16-byte block as a 128-bit integer

`dbl_eq`: the doubling of §6.1 on 16 bytes (`Spec.Cmac.dbl 16`) is, on the
block as a big-endian 128-bit integer `x` (`Spec.Gcm.ofBytes`), the shift
`x << 1` XORed with `0x87` if the bit shifted out was 1.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-- Bit `j` of byte `i` of a block, as an integer. -/
theorem ofBytes_bit {L : List Byte} (hL : L.length = 16) {i j : Nat} (hi : i < 16) (hj : j < 8) :
    (Spec.Gcm.ofBytes L).getLsbD (8 * (15 - i) + j) = (L.getD i 0).getLsbD j := by
  rw [← Proof.Aes.toBytes_ofBytes hL hi, Proof.Aes.toBytes_getD _ hi, BitVec.getLsbD_extractLsb']
  simp [hj]

/-- The 128-bit doubling. -/
def dbl128 (x : BitVec 128) : BitVec 128 := (x <<< 1) ^^^ (if x.msb then 0x87 else 0)

theorem getD_shiftLeft1 {L : List Byte} (hL : L.length = 16) {k : Nat} (hk : k < 16) :
    (shiftLeft1 L).getD k 0 = (L.getD k 0 <<< 1) ||| (((L.drop 1 ++ [0]).getD k 0 : Byte) >>> 7) := by
  simp [shiftLeft1, List.getD_eq_getElem?_getD, hL, hk]

theorem next_getD {L : List Byte} (hL : L.length = 16) {k : Nat} (hk : k < 15) :
    (L.drop 1 ++ [0]).getD k 0 = L.getD (k + 1) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hL, hk,
    List.getElem?_eq_getElem (show k + 1 < L.length by omega)]

theorem next_getD15 {L : List Byte} (hL : L.length = 16) : (L.drop 1 ++ [0]).getD 15 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, hL]

theorem getD_rb : ∀ k < 16, (rb 16).getD k 0 = if k = 15 then 0x87 else 0 := by decide

theorem testBit_135 : ∀ p < 128, 8 ≤ p → Nat.testBit 135 p = false := by decide

theorem high_0x87 {p : Nat} (hp : 8 ≤ p) : (0x87 : BitVec 128).getLsbD p = false := by
  rw [show (0x87 : BitVec 128) = BitVec.ofNat 128 135 from rfl, BitVec.getLsbD_ofNat]
  by_cases h : p < 128
  · rw [VG.Proof.Cmac.testBit_135 p h hp, Bool.and_false]
  · simp [h]

theorem bit_0x87 : ∀ j < 8, (0x87 : BitVec 128).getLsbD j = (0x87 : Byte).getLsbD j := by decide

theorem dbl_eq {L : List Byte} (hL : L.length = 16) :
    dbl 16 L = Spec.Gcm.toBytes (VG.Proof.Cmac.dbl128 (Spec.Gcm.ofBytes L)) := by
  have hmsb : (Spec.Gcm.ofBytes L).msb = msb1 L := by
    rw [BitVec.msb_eq_getLsbD_last, show 128 - 1 = 8 * (15 - 0) + 7 from rfl,
      VG.Proof.Cmac.ofBytes_bit hL (by decide) (by decide), msb1, BitVec.msb_eq_getLsbD_last]
    cases L with
    | nil => simp at hL
    | cons a _ => rfl
  have hsl : (shiftLeft1 L).length = 16 := by simp [shiftLeft1, hL]
  refine VG.Proof.Cmac.ext16 (by unfold dbl; split <;> simp [VG.Proof.Cmac.length_xor, hsl, rb, zeros]) (VG.Proof.Cmac.toBytes_length _)
    fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', VG.Proof.Cmac.dbl128]
  simp only [hj, decide_true, Bool.true_and, BitVec.getLsbD_xor, hmsb, BitVec.getLsbD_shiftLeft]
  have hdbl : (dbl 16 L).getD k 0 = (shiftLeft1 L).getD k 0 ^^^ (if msb1 L then (rb 16).getD k 0 else 0) := by
    unfold dbl
    split
    · rw [VG.Proof.Cmac.getD_xor (by simp [hsl, rb, zeros]) (by rw [hsl]; exact hk)]
    · simp
  rw [hdbl, VG.Proof.Cmac.getD_shiftLeft1 hL hk, VG.Proof.Cmac.getD_rb k hk]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hj, decide_true, Bool.true_and]
  have hm : ∀ p, 8 ≤ p → (if msb1 L = true then (135 : BitVec 128) else 0).getLsbD p = false := by
    intro p hp; split
    · exact VG.Proof.Cmac.high_0x87 hp
    · simp
  rcases Nat.lt_or_ge k 15 with hk15 | hk15
  · have hm0 : (if msb1 L = true then (if k = 15 then (135 : Byte) else 0) else 0).getLsbD j = false := by
      simp [show k ≠ 15 by omega]
    rw [hm0, hm _ (by omega), Bool.xor_false, Bool.xor_false, VG.Proof.Cmac.next_getD hL hk15]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [show 8 * (15 - k) + 0 - 1 = 8 * (15 - (k + 1)) + 7 by omega, VG.Proof.Cmac.ofBytes_bit hL (by omega) (by decide)]
      simp [show ¬ 8 * (15 - k) < 1 by omega, show 8 * (15 - k) < 128 by omega]
    · rw [show 8 * (15 - k) + j - 1 = 8 * (15 - k) + (j - 1) by omega, VG.Proof.Cmac.ofBytes_bit hL hk (by omega),
        BitVec.getLsbD_of_ge _ (7 + j) (by omega)]
      simp [show ¬ j < 1 by omega, show ¬ 8 * (15 - k) + j < 1 by omega, show 8 * (15 - k) + j < 128 by omega]
  · have hk' : k = 15 := by omega
    subst hk'
    rw [VG.Proof.Cmac.next_getD15 hL]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · cases hb : msb1 L
      · simp
      · simp
    · rw [show 8 * (15 - 15) + j - 1 = 8 * (15 - 15) + (j - 1) by omega,
        VG.Proof.Cmac.ofBytes_bit hL (i := 15) (by decide) (by omega)]
      cases hb : msb1 L
      · simp [show ¬ j < 1 by omega, show j < 128 by omega]
      · simp [show ¬ j < 1 by omega, show j < 128 by omega]
        rw [← BitVec.getLsbD_eq_getElem]; exact (VG.Proof.Cmac.bit_0x87 j hj).symm

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Dbl32`. -/
section

/-!
# CMAC: doubling a block in four 32-bit words

The 32-bit targets load a block as four byte-reversed words (`byteRev32`), the
block as a big-endian 128-bit integer `b₀ ++ b₁ ++ b₂ ++ b₃` (`ofBytes_rev4`),
double it a word at a time (`dbl_words4`), and store the words byte-reversed
again (`le4_rev4`).
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

theorem ofBytes_toBytes (x : Spec.Gcm.Block) : Spec.Gcm.ofBytes (Spec.Gcm.toBytes x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < 16 ∧ j < 8 ∧ p = 8 * (15 - i) + j :=
    ⟨15 - p / 8, p % 8, by omega, by omega, by omega⟩
  rw [VG.Proof.Cmac.ofBytes_bit (VG.Proof.Cmac.toBytes_length x) hi hj, Proof.Aes.toBytes_getD _ hi, BitVec.getLsbD_extractLsb']
  simp [hj]

theorem getLsbD_byteRev32 (a : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 a).getLsbD i = a.getLsbD (8 * (3 - i / 8) + i % 8) := by
  simp only [byteRev32]
  rw [VG.getLsbD_cat4]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h
  · simp only [h, ite_true, BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, h.2, ite_true, ite_false, BitVec.getLsbD_extractLsb',
      show i - 8 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i < 16 by omega, h.2, ite_true, ite_false,
      BitVec.getLsbD_extractLsb', show i - 16 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, ite_false,
      BitVec.getLsbD_extractLsb', show i - 24 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega

theorem getD_le4_append4 (a b c d : BitVec 32) {k : Nat} (hk : k < 16) :
    (VG.Proof.Cmac.le4 a ++ VG.Proof.Cmac.le4 b ++ VG.Proof.Cmac.le4 c ++ VG.Proof.Cmac.le4 d).getD k 0 =
      (if k < 4 then a else if k < 8 then b else if k < 12 then c else d).extractLsb' (8 * (k % 4)) 8 := by
  simp only [List.append_assoc, List.getD_eq_getElem?_getD]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
  · rw [List.getElem?_append_left (by rw [VG.Proof.Cmac.length_le4]; omega), ← List.getD_eq_getElem?_getD, VG.Proof.Cmac.getD_le4 _ h]
    simp [h, Nat.mod_eq_of_lt h]
  · rw [List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4,
      List.getElem?_append_left (by rw [VG.Proof.Cmac.length_le4]; omega), ← List.getD_eq_getElem?_getD,
      VG.Proof.Cmac.getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, h.2, show k % 4 = k - 4 by omega]
  · rw [List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4,
      List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4,
      List.getElem?_append_left (by rw [VG.Proof.Cmac.length_le4]; omega), ← List.getD_eq_getElem?_getD,
      VG.Proof.Cmac.getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, show k % 4 = k - 4 - 4 by omega]
  · rw [List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4,
      List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4,
      List.getElem?_append_right (by rw [VG.Proof.Cmac.length_le4]; omega), VG.Proof.Cmac.length_le4, ← List.getD_eq_getElem?_getD,
      VG.Proof.Cmac.getD_le4 _ (by omega)]
    simp [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, show k % 4 = k - 4 - 4 - 4 by omega]

/-- Storing the byte-reversed words of `a ++ b ++ c ++ d` stores its bytes,
big-endian. -/
theorem le4_rev4 (a b c d : BitVec 32) :
    VG.Proof.Cmac.le4 (byteRev32 a) ++ VG.Proof.Cmac.le4 (byteRev32 b) ++ VG.Proof.Cmac.le4 (byteRev32 c) ++ VG.Proof.Cmac.le4 (byteRev32 d) =
      Spec.Gcm.toBytes (a ++ b ++ c ++ d) := by
  refine VG.Proof.Cmac.ext16 (by simp [VG.Proof.Cmac.length_le4]) (VG.Proof.Cmac.toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk, VG.Proof.Cmac.getD_le4_append4 _ _ _ _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
  · simp only [h, ite_true, VG.Proof.Cmac.getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, h.2, ite_true, ite_false,
      VG.Proof.Cmac.getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, ite_true, ite_false,
      VG.Proof.Cmac.getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ite_false,
      VG.Proof.Cmac.getLsbD_byteRev32 _ (show 8 * (k % 4) + j < 32 by omega)]
    simp only [BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)

theorem mask_eq32 (hi : BitVec 32) :
    ((0 : BitVec 32) - (hi >>> 31)) &&& 0x87 = if hi.msb then 0x87 else 0 := by
  have h : hi >>> 31 = if hi.msb then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
    have := hi.isLt
    by_cases hm : 2 ^ (32 - 1) ≤ hi.toNat
    · rw [decide_eq_true hm]; simp; omega
    · rw [decide_eq_false hm]; simp; omega
  rw [h]
  split <;> decide

theorem bit135_32 : ∀ p < 32, (135 : BitVec 32).getLsbD p = (135 : BitVec 128).getLsbD p := by decide

/-- The words the 32-bit targets store, from the big-endian words `b₀ … b₃`
of a block: the block doubled. -/
def dblW0 (b₀ b₁ : BitVec 32) : BitVec 32 := (b₀ <<< 1) ||| (b₁ >>> 31)
def dblW3 (b₀ b₃ : BitVec 32) : BitVec 32 := (b₃ <<< 1) ^^^ (((0 : BitVec 32) - (b₀ >>> 31)) &&& 0x87)

theorem getLsbD_cat4w (b₀ b₁ b₂ b₃ : BitVec 32) {i : Nat} (hi : i < 128) :
    (b₀ ++ b₁ ++ b₂ ++ b₃).getLsbD i = if i < 32 then b₃.getLsbD i else if i < 64 then b₂.getLsbD (i - 32)
      else if i < 96 then b₁.getLsbD (i - 64) else b₀.getLsbD (i - 96) := by
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | (congr 1; omega) | rfl

theorem getLsbD_shl1 (x : BitVec 32) {i : Nat} (hi : i < 32) :
    (x <<< 1).getLsbD i = (decide (1 ≤ i) && x.getLsbD (i - 1)) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 1 <;> simp [h] <;> omega

theorem getLsbD_shr31 (x : BitVec 32) (i : Nat) : (x >>> 31).getLsbD i = (decide (i = 0) && x.getLsbD 31) := by
  rw [BitVec.getLsbD_ushiftRight]
  by_cases h : i = 0
  · subst h; simp
  · simp only [h, decide_false, Bool.false_and]; exact BitVec.getLsbD_of_ge x _ (by omega)

theorem getLsbD_shl1_128 (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (x <<< 1).getLsbD i = (decide (1 ≤ i) && x.getLsbD (i - 1)) := by
  rw [BitVec.getLsbD_shiftLeft]; simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 1 <;> simp [h] <;> omega

theorem dbl_words4 (b₀ b₁ b₂ b₃ : BitVec 32) :
    VG.Proof.Cmac.dblW0 b₀ b₁ ++ VG.Proof.Cmac.dblW0 b₁ b₂ ++ VG.Proof.Cmac.dblW0 b₂ b₃ ++ VG.Proof.Cmac.dblW3 b₀ b₃ = VG.Proof.Cmac.dbl128 (b₀ ++ b₁ ++ b₂ ++ b₃) := by
  rw [VG.Proof.Cmac.dblW0, VG.Proof.Cmac.dblW0, VG.Proof.Cmac.dblW0, VG.Proof.Cmac.dblW3, VG.Proof.Cmac.mask_eq32, VG.Proof.Cmac.dbl128, BitVec.msb_append, BitVec.msb_append, BitVec.msb_append]
  have h0 : ((32 : Nat) = 0) = False := by simp
  have h64 : ((64 : Nat) = 0) = False := by simp
  have h96 : ((96 : Nat) = 0) = False := by simp
  simp only [h0, h64, h96, ite_false]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ hp]
  rw [BitVec.getLsbD_xor (x := (b₀ ++ b₁ ++ b₂ ++ b₃) <<< 1), VG.Proof.Cmac.getLsbD_shl1_128 _ hp]
  have m87 : (if b₀.msb = true then (135 : BitVec 128) else 0).getLsbD p =
      (decide (p < 32) && (if b₀.msb = true then (135 : BitVec 32) else 0).getLsbD p) := by
    split
    · by_cases h : p < 32
      · simp only [h, decide_true, Bool.true_and]; exact (VG.Proof.Cmac.bit135_32 p h).symm
      · simp only [h, decide_false, Bool.false_and]; exact Proof.Cmac.high_0x87 (by omega)
    · simp
  rw [m87]
  rcases (by omega : p = 0 ∨ (1 ≤ p ∧ p < 32) ∨ p = 32 ∨ (33 ≤ p ∧ p < 64) ∨ p = 64 ∨ (65 ≤ p ∧ p < 96) ∨
    p = 96 ∨ (97 ≤ p ∧ p < 128)) with h | h | h | h | h | h | h | h
  · subst h
    simp
  · simp only [show p < 32 from h.2, ite_true, BitVec.getLsbD_xor, VG.Proof.Cmac.getLsbD_shl1 _ h.2, show 1 ≤ p from h.1,
      decide_true, Bool.true_and, VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show p - 1 < 32 by omega]
  · subst h
    simp only [show ¬ 32 < 32 by decide, show 32 < 64 by decide, ite_false, ite_true, Nat.sub_self,
      BitVec.getLsbD_or, VG.Proof.Cmac.getLsbD_shl1 _ (by decide : 0 < 32), VG.Proof.Cmac.getLsbD_shr31,
      VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (by decide : 32 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show p < 64 from h.2, ite_true, ite_false, BitVec.getLsbD_or,
      VG.Proof.Cmac.getLsbD_shl1 _ (show p - 32 < 32 by omega), VG.Proof.Cmac.getLsbD_shr31, show ¬ p - 32 = 0 by omega,
      show 1 ≤ p - 32 by omega, show 1 ≤ p by omega, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.or_false, Bool.xor_false, VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega),
      show ¬ p - 1 < 32 by omega, show p - 1 < 64 by omega]
    congr 1
  · subst h
    simp only [show ¬ 64 < 32 by decide, show ¬ 64 < 64 by decide, show 64 < 96 by decide, ite_false,
      ite_true, Nat.sub_self, BitVec.getLsbD_or, VG.Proof.Cmac.getLsbD_shl1 _ (by decide : 0 < 32), VG.Proof.Cmac.getLsbD_shr31,
      VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (by decide : 64 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show ¬ p < 64 by omega, show p < 96 from h.2, ite_true, ite_false,
      BitVec.getLsbD_or, VG.Proof.Cmac.getLsbD_shl1 _ (show p - 64 < 32 by omega), VG.Proof.Cmac.getLsbD_shr31,
      show ¬ p - 64 = 0 by omega, show 1 ≤ p - 64 by omega, show 1 ≤ p by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.xor_false,
      VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show ¬ p - 1 < 32 by omega,
      show ¬ p - 1 < 64 by omega, show p - 1 < 96 by omega]
    congr 1
  · subst h
    simp only [show ¬ 96 < 32 by decide, show ¬ 96 < 64 by decide, show ¬ 96 < 96 by decide, ite_false,
      Nat.sub_self, BitVec.getLsbD_or, VG.Proof.Cmac.getLsbD_shl1 _ (by decide : 0 < 32), VG.Proof.Cmac.getLsbD_shr31,
      VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (by decide : 96 - 1 < 128)]
    simp
  · simp only [show ¬ p < 32 by omega, show ¬ p < 64 by omega, show ¬ p < 96 by omega, ite_false,
      BitVec.getLsbD_or, VG.Proof.Cmac.getLsbD_shl1 _ (show p - 96 < 32 by omega), VG.Proof.Cmac.getLsbD_shr31,
      show ¬ p - 96 = 0 by omega, show 1 ≤ p - 96 by omega, show 1 ≤ p by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.xor_false,
      VG.Proof.Cmac.getLsbD_cat4w _ _ _ _ (show p - 1 < 128 by omega), show ¬ p - 1 < 32 by omega,
      show ¬ p - 1 < 64 by omega, show ¬ p - 1 < 96 by omega]
    congr 1

theorem byteRev32_byteRev32 (a : BitVec 32) : byteRev32 (byteRev32 a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [VG.Proof.Cmac.getLsbD_byteRev32 _ hi, VG.Proof.Cmac.getLsbD_byteRev32 _ (by omega)]
  congr 1; omega

/-- The block at `p` as a big-endian integer, from its four byte-reversed words. -/
theorem ofBytes_rev4 (m : Mem) (p : Addr) :
    Spec.Gcm.ofBytes (Spec.Aes.bytesAt m p 16) =
      byteRev32 (m.readW p 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32) ++
        byteRev32 (m.readW (p + BitVec.ofNat 64 8) 32) ++ byteRev32 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  have h := VG.Proof.Cmac.le4_rev4 (byteRev32 (m.readW p 32)) (byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32))
    (byteRev32 (m.readW (p + BitVec.ofNat 64 8) 32)) (byteRev32 (m.readW (p + BitVec.ofNat 64 12) 32))
  rw [VG.Proof.Cmac.byteRev32_byteRev32, VG.Proof.Cmac.byteRev32_byteRev32, VG.Proof.Cmac.byteRev32_byteRev32, VG.Proof.Cmac.byteRev32_byteRev32] at h
  rw [VG.Proof.Cmac.bytesAt_split4, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, ← VG.Proof.Cmac.le4_readW, h, VG.Proof.Cmac.ofBytes_toBytes]

end VG.Proof.Cmac

end

/- Proofs formerly in `VerifiedGarbage.Proof.Cmac.Stream`. -/
section

/-!
# Streaming AES-CMAC: lemmas about the state

What every target's `vg_cmac_aes_absorb` and `vg_cmac_aes_finish` need of the
streaming state (`Spec.Cmac.Repr`), whatever the ISA:

* `held n`, the number of bytes a state for a message of `n` bytes holds
  back: none for the empty message, else 1 to 16.
* `repr_fill`: absorbing `d` that fits in the block being held back
  (`d.length ≤ 16 - held n`) only appends `d` to the bytes held back.
* `repr_chain`: absorbing more chains the block held back, completed with
  the first `16 - held n` bytes of `d`, and then the whole blocks of the
  rest of `d` but its last 1 to 16 bytes, which it holds back.
* `repr_finish`: the chaining value and the bytes held back are what
  `vg_cmac_aes_finalize` takes, and its result is the MAC.
-/

namespace VG.Proof.Cmac.Stream

open VG Spec.Cmac

/-! ## Lengths -/

/-- The number of bytes held back for a message of `n` bytes. -/
def held (n : Nat) : Nat := n - chainedLen 16 n

theorem held_zero : VG.Proof.Cmac.Stream.held 0 = 0 := rfl

theorem held_pos {n : Nat} (h : 0 < n) : VG.Proof.Cmac.Stream.held n = (n - 1) % 16 + 1 := by
  unfold VG.Proof.Cmac.Stream.held chainedLen; omega

theorem held_le (n : Nat) : VG.Proof.Cmac.Stream.held n ≤ 16 := by unfold VG.Proof.Cmac.Stream.held chainedLen; omega

theorem chainedLen_add_held (n : Nat) : chainedLen 16 n + VG.Proof.Cmac.Stream.held n = n := by
  unfold VG.Proof.Cmac.Stream.held chainedLen; omega

theorem chainedLen_mod (n : Nat) : chainedLen 16 n % 16 = 0 := by unfold chainedLen; omega

theorem chainedLen_fill {n l : Nat} (h : l ≤ 16 - VG.Proof.Cmac.Stream.held n) : chainedLen 16 (n + l) = chainedLen 16 n := by
  unfold VG.Proof.Cmac.Stream.held chainedLen at *; omega

theorem held_fill {n l : Nat} (h : l ≤ 16 - VG.Proof.Cmac.Stream.held n) : VG.Proof.Cmac.Stream.held (n + l) = VG.Proof.Cmac.Stream.held n + l := by
  unfold VG.Proof.Cmac.Stream.held chainedLen at *; omega

/-- The number of whole blocks of `d` chained after the block held back is
completed with the first `16 - held n` bytes of `d`. -/
def nblocks (n l : Nat) : Nat := (l - (16 - VG.Proof.Cmac.Stream.held n) - 1) / 16

theorem chainedLen_chain {n l : Nat} (h : 16 - VG.Proof.Cmac.Stream.held n < l) :
    chainedLen 16 (n + l) = chainedLen 16 n + 16 + 16 * VG.Proof.Cmac.Stream.nblocks n l := by
  unfold VG.Proof.Cmac.Stream.nblocks VG.Proof.Cmac.Stream.held chainedLen at *; omega

theorem held_chain {n l : Nat} (h : 16 - VG.Proof.Cmac.Stream.held n < l) :
    VG.Proof.Cmac.Stream.held (n + l) = l - (16 - VG.Proof.Cmac.Stream.held n) - 16 * VG.Proof.Cmac.Stream.nblocks n l := by
  unfold VG.Proof.Cmac.Stream.nblocks VG.Proof.Cmac.Stream.held chainedLen at *; omega

theorem held_chain_pos {n l : Nat} (h : 16 - VG.Proof.Cmac.Stream.held n < l) :
    0 < l - (16 - VG.Proof.Cmac.Stream.held n) - 16 * VG.Proof.Cmac.Stream.nblocks n l ∧ l - (16 - VG.Proof.Cmac.Stream.held n) - 16 * VG.Proof.Cmac.Stream.nblocks n l ≤ 16 := by
  unfold VG.Proof.Cmac.Stream.nblocks; omega

/-! ## Blocks -/

theorem blocks_append {xs ys : List Byte} (hx : xs.length % 16 = 0) :
    blocks 16 (xs ++ ys) = blocks 16 xs ++ blocks 16 ys := by
  obtain ⟨q, hq⟩ : ∃ q, xs.length = 16 * q := ⟨xs.length / 16, by omega⟩
  simp only [blocks, List.length_append, hq,
    show (16 * q + ys.length) / 16 = q + ys.length / 16 by omega,
    Nat.mul_div_cancel_left _ (by decide : 0 < 16), List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.mul_add, List.drop_append, hq]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem blocks_single {x : List Byte} (hx : x.length = 16) : blocks 16 x = [x] := by
  simp [blocks, hx, List.take_of_length_le]

theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksAt m p 16 n = blocks 16 (Spec.Aes.bytesAt m p (16 * n)) := by
  simp only [blocksAt, blocks, VG.Proof.Cmac.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

/-- The bytes at `p + a` are those at `p` from the `a`-th on. -/
theorem bytesAt_offset (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b = ((Spec.Aes.bytesAt m p n).drop a).take b := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Aes.bytesAt m p (a + b) =
      Spec.Aes.bytesAt m p a ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Aes.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-! ## The state -/

/-- The key schedule and the subkeys at `p` are those of `key`, as `Repr`
requires. -/
def KeyAt (mem : Mem) (p : Addr) (key : List Byte) : Prop :=
  let ks := subkeys (aes key) 16
  (key.length = 16 ∨ key.length = 24 ∨ key.length = 32) ∧
    Spec.Aes.bytesAt mem p (16 * (Spec.Aes.rounds (key.length / 4) + 1)) = Spec.Aes.expandKey key ∧
    Spec.Aes.bytesAt mem (p + 240) 32 = ks.1 ++ ks.2

theorem rounds_le {key : List Byte} (h : key.length = 16 ∨ key.length = 24 ∨ key.length = 32) :
    16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
  simp only [Spec.Aes.rounds]; omega

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `KeyAt` depends only on the first 272 bytes. -/
theorem KeyAt.congr {m m' : Mem} {p : Addr} {key : List Byte} (hk : VG.Proof.Cmac.Stream.KeyAt m p key)
    (h : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : VG.Proof.Cmac.Stream.KeyAt m' p key := by
  obtain ⟨hl, hs, hsk⟩ := hk
  have hR := VG.Proof.Cmac.Stream.rounds_le hl
  refine ⟨hl, ?_, ?_⟩
  · rw [VG.Proof.Cmac.Stream.bytesAt_congr fun i hi => h i (by omega), hs]
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl,
      VG.Proof.Cmac.Stream.bytesAt_congr (m := m) fun i hi => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact hsk

theorem repr_iff (mem : Mem) (p : Addr) (key msg : List Byte) :
    Spec.Cmac.Repr mem p key msg ↔ VG.Proof.Cmac.Stream.KeyAt mem p key ∧
      Spec.Aes.bytesAt mem (p + 272) 16 =
        chain (aes key) (zeros 16) (blocks 16 (msg.take (chainedLen 16 msg.length))) ∧
      Spec.Aes.bytesAt mem (p + 288) (VG.Proof.Cmac.Stream.held msg.length) = msg.drop (chainedLen 16 msg.length) := by
  simp only [Spec.Cmac.Repr, VG.Proof.Cmac.Stream.KeyAt, VG.Proof.Cmac.Stream.held, and_assoc]

theorem length_take_chained (msg : List Byte) :
    (msg.take (chainedLen 16 msg.length)).length = chainedLen 16 msg.length := by
  have := VG.Proof.Cmac.Stream.chainedLen_add_held msg.length
  simp only [List.length_take]; omega

/-- Absorbing `d` that fits in the block held back. -/
theorem repr_fill {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : Spec.Cmac.Repr m p key msg)
    (hk : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : d.length ≤ 16 - VG.Proof.Cmac.Stream.held msg.length)
    (hc : Spec.Aes.bytesAt m' (p + 272) 16 = Spec.Aes.bytesAt m (p + 272) 16)
    (hh : Spec.Aes.bytesAt m' (p + 288) (VG.Proof.Cmac.Stream.held msg.length + d.length) =
      Spec.Aes.bytesAt m (p + 288) (VG.Proof.Cmac.Stream.held msg.length) ++ d) :
    Spec.Cmac.Repr m' p key (msg ++ d) := by
  rw [VG.Proof.Cmac.Stream.repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := VG.Proof.Cmac.Stream.chainedLen_add_held msg.length
  rw [List.length_append, VG.Proof.Cmac.Stream.chainedLen_fill hl, VG.Proof.Cmac.Stream.held_fill hl]
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · rw [hc, hc', List.take_append_of_le_length (by omega)]
  · rw [hh, hh', List.drop_append_of_le_length (by omega)]

/-- Absorbing `d` that does not fit in the block held back. -/
theorem repr_chain {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : Spec.Cmac.Repr m p key msg)
    (hk : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : 16 - VG.Proof.Cmac.Stream.held msg.length < d.length)
    (hc : Spec.Aes.bytesAt m' (p + 272) 16 =
      Spec.Cmac.chain (aes key) (Spec.Aes.bytesAt m (p + 272) 16)
        ([Spec.Aes.bytesAt m (p + 288) (VG.Proof.Cmac.Stream.held msg.length) ++ d.take (16 - VG.Proof.Cmac.Stream.held msg.length)] ++
          blocks 16 ((d.drop (16 - VG.Proof.Cmac.Stream.held msg.length)).take (16 * VG.Proof.Cmac.Stream.nblocks msg.length d.length))))
    (hh : Spec.Aes.bytesAt m' (p + 288) (d.length - (16 - VG.Proof.Cmac.Stream.held msg.length) - 16 * VG.Proof.Cmac.Stream.nblocks msg.length d.length) =
      (d.drop (16 - VG.Proof.Cmac.Stream.held msg.length)).drop (16 * VG.Proof.Cmac.Stream.nblocks msg.length d.length)) :
    Spec.Cmac.Repr m' p key (msg ++ d) := by
  rw [VG.Proof.Cmac.Stream.repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := VG.Proof.Cmac.Stream.chainedLen_add_held msg.length
  have hm := VG.Proof.Cmac.Stream.chainedLen_mod msg.length
  have hp := VG.Proof.Cmac.Stream.held_chain_pos hl
  have hle := VG.Proof.Cmac.Stream.held_le msg.length
  rw [List.length_append, VG.Proof.Cmac.Stream.chainedLen_chain hl, VG.Proof.Cmac.Stream.held_chain hl]
  generalize hcd : chainedLen 16 msg.length = c at *
  generalize hhd : VG.Proof.Cmac.Stream.held msg.length = h at *
  generalize hnb : VG.Proof.Cmac.Stream.nblocks msg.length d.length = nb at *
  have hdc : (msg.drop c).length = h := by simp; omega
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · have e : (msg ++ d).take (c + 16 + 16 * nb) =
        msg.take c ++ ((msg.drop c ++ d.take (16 - h)) ++ (d.drop (16 - h)).take (16 * nb)) := by
      rw [List.take_append, List.take_of_length_le (by omega),
        show c + 16 + 16 * nb - msg.length = (16 - h) + 16 * nb by omega, List.take_add]
      simp only [List.append_assoc]
      rw [← List.append_assoc (List.take c msg), List.take_append_drop]
    have hx : (msg.drop c ++ d.take (16 - h)).length = 16 := by simp; omega
    rw [hc, hc', hh', e, VG.Proof.Cmac.Stream.blocks_append (by rw [List.length_take]; omega),
      VG.Proof.Cmac.Stream.blocks_append (by rw [hx]), VG.Proof.Cmac.Stream.blocks_single hx, VG.Proof.Cmac.chain_append, VG.Proof.Cmac.chain_append, VG.Proof.Cmac.chain_append]
  · have e : (msg ++ d).drop (c + 16 + 16 * nb) = (d.drop (16 - h)).drop (16 * nb) := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
      congr 1; omega
    rw [hh, e]

/-- The MAC is `macFull`'s, which has 16 bytes. -/
theorem aesCmac_eq (key msg : List Byte) : aesCmac key 16 msg = macFull (aes key) 16 msg := by
  simp only [aesCmac, mac]
  apply List.take_of_length_le
  simp only [macFull, VG.Proof.Cmac.chain_append, VG.Proof.Cmac.chain_single, aes, VG.Proof.Cmac.aesWith_length, Nat.le_refl]

/-- What `vg_cmac_aes_finalize` takes of a state that represents `msg`. -/
theorem repr_finish {m : Mem} {p : Addr} {key msg : List Byte} (hr : Spec.Cmac.Repr m p key msg) :
    let c := chainedLen 16 msg.length
    (msg.take c).length % 16 = 0 ∧ (msg.take c = [] ∨ 0 < VG.Proof.Cmac.Stream.held msg.length) ∧
      Spec.Aes.bytesAt m (p + 272) 16 = Spec.Cmac.chain (aes key) (zeros 16) (blocks 16 (msg.take c)) ∧
      msg.take c ++ Spec.Aes.bytesAt m (p + 288) (VG.Proof.Cmac.Stream.held msg.length) = msg := by
  rw [VG.Proof.Cmac.Stream.repr_iff] at hr
  obtain ⟨_, hc, hh⟩ := hr
  have hn := VG.Proof.Cmac.Stream.chainedLen_add_held msg.length
  refine ⟨by rw [VG.Proof.Cmac.Stream.length_take_chained]; exact VG.Proof.Cmac.Stream.chainedLen_mod _, ?_, hc, by rw [hh, List.take_append_drop]⟩
  by_cases h0 : msg.length = 0
  · exact .inl (by simp [List.eq_nil_of_length_eq_zero h0])
  · exact .inr (by rw [VG.Proof.Cmac.Stream.held_pos (by omega)]; omega)

end VG.Proof.Cmac.Stream

end

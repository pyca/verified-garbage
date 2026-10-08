import VerifiedGarbage.Proof.AesCbc.Spec

/-!
# CBC: blocks moved as 64-bit words

The memories the functions leave when they XOR a block into another
(`xorMem`) or copy one (`copyMem`), as two 64-bit words, and what they leave
there, on every target.
-/

namespace VG.Proof.AesCbc

open VG
open VG.Spec.Aes (bytesAt)

/-- The block at `P` XORed with the block at `Q`, as `xorInto` writes it. -/
def xorMem (m : Mem) (P Q : Addr) : Mem :=
  let m₁ := m.writeW P (m.readW P 64 ^^^ m.readW Q 64)
  m₁.writeW (P + BitVec.ofNat 64 8) (m₁.readW (P + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (Q + BitVec.ofNat 64 8) 64)

/-- The block at `Q` copied to `P`, as `copy` writes it. -/
def copyMem (m : Mem) (P Q : Addr) : Mem :=
  let m₁ := m.writeW P (m.readW Q 64)
  m₁.writeW (P + BitVec.ofNat 64 8) (m₁.readW (Q + BitVec.ofNat 64 8) 64)

theorem frame_store2 {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem frame_store1 {m : Mem} (p : Addr) (w : BitVec 64) : Frame [⟨p, 16⟩] m (m.writeW p w) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))

theorem xorMem_frame (m : Mem) (P Q : Addr) : Frame [⟨P, 16⟩] m (xorMem m P Q) := frame_store2 _ _ _

theorem copyMem_frame (m : Mem) (P Q : Addr) : Frame [⟨P, 16⟩] m (copyMem m P Q) := frame_store2 _ _ _

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

theorem readW8_store1 {m : Mem} {P : Addr} (w : BitVec 64) :
    (m.writeW P w).readW (P + BitVec.ofNat 64 8) 64 = m.readW (P + BitVec.ofNat 64 8) 64 := by
  have hs : Mem.Sep (P + BitVec.ofNat 64 8) (64 / 8) P (64 / 8) := by
    have := Offset.sep P (d := 8) (n := 8) (e := 0) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  exact Mem.readW_writeW_sep hs (by decide)

theorem xorMem_bytes (m : Mem) {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (xorMem m P Q) P 16 = Spec.Cbc.xor (bytesAt m P 16) (bytesAt m Q 16) := by
  rw [xorMem, Proof.Cmac.bytesAt_store2, readW8_store1,
    readW_frame16 (frame_store1 (m := m) P _) (d := 8) (by decide) (by simpa using hpq.symm)]
  exact Proof.Cmac.xor_words m P Q

theorem copyMem_bytes (m : Mem) {P Q : Addr} (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (copyMem m P Q) P 16 = bytesAt m Q 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store2,
    readW_frame16 (frame_store1 (m := m) P _) (d := 8) (by decide) (by simpa using hpq.symm),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

end VG.Proof.AesCbc

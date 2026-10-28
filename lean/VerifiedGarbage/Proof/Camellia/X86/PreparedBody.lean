module

public import VerifiedGarbage.Proof.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Camellia.X86.Prepared
import VerifiedGarbage.Proof.Camellia.Planes32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's batches under prepared subkeys on x86 (32-bit): the code

What `vg_camellia_crypt_prepared` reads (`layout`,
`Spec.Camellia.Prepared.Holds`) is the table that ECB's rounds read
(`EntryOk`), word for word (`TableWordsAt`, `holds_of_words`,
`readyAt_of_words` and back): each of the table's words is the plane of its
subkey (`keyPlane32`, the only words related to it by `W32.HalfRel`,
`halfRel_eq`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Camellia (keyPlane32)
open VG.Proof.Camellia (sigma_rel)

/-! ## The encoding -/

/-- The only planes of the subkey `x` are `keyPlane32 x`. -/
theorem halfRel_eq {Q : Nat → BitVec 32} {x : BitVec 64} (h : W32.HalfRel Q fun _ => x) {k : Nat}
    (hk : k < 16) : Q k = keyPlane32 x (k / 8) (k % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have e1 := h (p % 8) (by omega) (4 * (k / 8) + p / 8) (by omega) (k % 8) (by omega)
  have e2 := sigma_rel x (p % 8) (by omega) (4 * (k / 8) + p / 8) (by omega) (k % 8) (by omega)
  simp only at e2
  rw [show 8 * ((4 * (k / 8) + p / 8) / 4) + k % 8 = k by omega,
    show 8 * ((4 * (k / 8) + p / 8) % 4) + p % 8 = p by omega] at e1 e2
  rw [e1, e2]

theorem keyEntry_eq (w : List (BitVec 64)) (g : Nat) (d : Dir) (e : Nat) :
    keyEntry w g d e = w.getD (permOf d g e) 0 := by
  cases d <;> rfl

theorem ofSpecDir_specDir (d : Dir) : ofSpecDir (specDir d) = d := by cases d <;> rfl

theorem specDir_ofSpecDir (d : Spec.Camellia.Direction) : specDir (ofSpecDir d) = d := by cases d <;> rfl

/-- The table of subkeys of `R` rounds in the order of `d`: the words of
the working space at `B` from `keySlot` on. -/
def TableWordsAt (R : Nat) (m : Mem) (B : BitVec 32) (w : List (BitVec 64)) (d : Dir) : Prop :=
  ∀ k, keySlot ≤ k → k < keySlot + 16 * (8 * (R / 6) + 2) → m.readW (wordAddr B k) 32 = preparedWord R w d k

theorem layout_table (R : Nat) : layout.table R = [(416, 64 * (8 * (R / 6) + 2))] := rfl

/-- Byte `o` of the working space, from its word. -/
theorem byte_word {m : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {o : Nat}
    (ho : o < 4 * slots) :
    m (B.setWidth 64 + BitVec.ofNat 64 o) = (m.readW (wordAddr B (o / 4)) 32).extractLsb' (8 * (o % 4)) 8 := by
  rw [slot_addr (by omega), show B.setWidth 64 + BitVec.ofNat 64 o =
    B.setWidth 64 + BitVec.ofNat 64 (4 * (o / 4)) + BitVec.ofNat 64 (o % 4) by
      rw [VG.Offset.add_add]; congr 2; omega]
  exact Mem.readW_byte m _ (by omega)

theorem holds_of_words {R : Nat} {m : Mem} {B : BitVec 32} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) (hR : R = 18 ∨ R = 24) (h : TableWordsAt R m B w (ofSpecDir d)) :
    Spec.Camellia.Prepared.Holds layout m (B.setWidth 64) R w d := by
  intro r hr i hi
  rw [layout_table] at hr
  simp only [List.mem_singleton] at hr; subst hr
  have hg : R / 6 ≤ 4 := by omega
  dsimp only at hi ⊢
  rw [byte_word (m := m) hfit (by rw [slots_eq]; omega), h _ (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)]
  rfl

theorem words_of_holds {R : Nat} {m : Mem} {B : BitVec 32} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) (hR : R = 18 ∨ R = 24)
    (h : Spec.Camellia.Prepared.Holds layout m (B.setWidth 64) R w d) : TableWordsAt R m B w (ofSpecDir d) := by
  intro k hk1 hk2
  have hg : R / 6 ≤ 4 := by omega
  rw [keySlot_eq] at hk1 hk2
  simp only [Mem.readW, BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes (n := 4) (v := preparedWord R w (ofSpecDir d) k) fun j hj => ?_
  have := h _ (List.mem_singleton_self _) (4 * k + j - 416) (by omega)
  simp only [keySlot_eq] at this
  rw [show 4 * 104 + (4 * k + j - 416) = 4 * k + j by omega] at this
  rw [show wordAddr B k = B.setWidth 64 + BitVec.ofNat 64 (4 * k) from slot_addr (by rw [slots_eq] at hfit; omega),
    VG.Offset.add_add, this]
  show (preparedWord R w (ofSpecDir d) ((4 * k + j) / 4)).extractLsb' (8 * ((4 * k + j) % 4)) 8 = _
  rw [show (4 * k + j) / 4 = k by omega, show (4 * k + j) % 4 = j by omega]

theorem preparedWord_entry (R : Nat) (w : List (BitVec 64)) (d : Dir) {e j : Nat} (hj : j < 16) :
    preparedWord R w d (keySlot + 16 * e + j) = keyPlane32 (keyEntry w (R / 6) d e) (j / 8) (j % 8) := by
  simp only [preparedWord]
  rw [show (keySlot + 16 * e + j - keySlot) / 16 = e by omega,
    show (keySlot + 16 * e + j - keySlot) % 16 = j by omega, show (keySlot + 16 * e + j - keySlot) % 8 = j % 8 by omega]

/-- The table holds the entries `EntryOk` reads. -/
theorem entries_of_words {R : Nat} {m : Mem} {B : BitVec 32} {w : List (BitVec 64)} {d : Dir}
    (h : TableWordsAt R m B w d) {e : Nat} (he : e < 8 * (R / 6) + 2) :
    EntryOk m B e (keyEntry w (R / 6) d e) :=
  (sigma_rel (keyEntry w (R / 6) d e)).congr fun j hj => by
    rw [entryW, h _ (by omega) (by omega), preparedWord_entry R w d hj]

theorem words_of_entries {R : Nat} {m : Mem} {B : BitVec 32} {w : List (BitVec 64)} {d : Dir}
    (h : ∀ e < 8 * (R / 6) + 2, EntryOk m B e (keyEntry w (R / 6) d e)) : TableWordsAt R m B w d := by
  intro k hk1 hk2
  have e := halfRel_eq (h ((k - keySlot) / 16) (by omega)) (k := (k - keySlot) % 16) (by omega)
  rw [entryW, show keySlot + 16 * ((k - keySlot) / 16) + (k - keySlot) % 16 = k by omega] at e
  rw [e, preparedWord]
  rw [show (k - keySlot) % 16 % 8 = (k - keySlot) % 8 by omega]

end VG.Proof.Camellia.X86

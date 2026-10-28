module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Camellia.Bytes
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The serial core's working space as `Spec.Camellia.Prepared`'s layout

The table of `layout` holds the words `w` (`Holds`) exactly when the serial
core's table is ready for them (`Ready`): the S-box's bytes, then the
words, the most significant byte first (`holds_of_ready`,
`ready_of_holds`). `keeps_of_frame`: a working space changed only within
one range keeps every byte outside it.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Spec.Camellia.Prepared (Holds Keeps)

theorem wordBytes_getD (w : BitVec 64) {j : Nat} (hj : j < 8) :
    (Spec.Camellia.wordBytes w).getD j 0 = Proof.Camellia.byteOf w j := by
  simp [Spec.Camellia.wordBytes, Proof.Camellia.byteOf, hj]

theorem layout_table (R : Nat) : layout.table R = [(0, 256), (256, 8 * Spec.Camellia.scheduleLength R)] := rfl

theorem encode_sbox {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction} {i : Nat} (hi : i < 256) :
    layout.encode R w d i = Spec.Camellia.sbox1Table.getD i 0 := by
  simp only [layout, hi, ↓reduceIte]

theorem encode_word {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction} (i : Nat) :
    layout.encode R w d (256 + i) = Proof.Camellia.byteOf (w.getD (i / 8) 0) (i % 8) := by
  simp only [layout, show ¬ 256 + i < 256 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  exact wordBytes_getD _ (Nat.mod_lt _ (by decide))

/-- A ready table holds its words, for either direction (the encoding does
not depend on it). -/
theorem holds_of_ready {m : Mem} {B : Addr} {k : Nat × List (BitVec 64)} (h : Ready m B k)
    (d : Spec.Camellia.Direction) : Holds layout m B k.1 k.2 d := by
  intro r hr i hi
  rw [layout_table] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [Nat.zero_add] at hi ⊢
    rw [encode_sbox hi]
    exact h.sbox i hi
  · dsimp only at hi ⊢
    rw [encode_word, ← h.keys (i / 8) (by omega), Proof.Camellia.byteOf_wordAt _ _ (Nat.mod_lt _ (by decide)),
      VG.Offset.add_add, show 256 + 8 * (i / 8) + i % 8 = 256 + i by omega]

/-- A table holding the words of 18 or 24 rounds is ready for them. -/
theorem ready_of_holds {m : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d) : Ready m B (R, w) := by
  refine ⟨hR, fun j hj => ?_, fun i hi => ?_⟩
  · have := h (0, 256) (by rw [layout_table]; simp) j hj
    simp only [Nat.zero_add] at this
    rw [this, encode_sbox hj]
  · dsimp only at hi
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hb := h (256, 8 * Spec.Camellia.scheduleLength R) (by rw [layout_table]; simp)
      (8 * i + (7 - k / 8)) (by omega)
    dsimp only at hb
    rw [Proof.Camellia.getLsbD_wordAt _ _ hk, VG.Offset.add_add,
      show 256 + 8 * i + (7 - k / 8) = 256 + (8 * i + (7 - k / 8)) by omega, hb, encode_word,
      show (8 * i + (7 - k / 8)) / 8 = i by omega, show (8 * i + (7 - k / 8)) % 8 = 7 - k / 8 by omega,
      Proof.Camellia.getLsbD_byteOf _ (by omega) (Nat.mod_lt _ (by decide)),
      show 56 - 8 * (7 - k / 8) + k % 8 = k by omega]

/-- A working space changed only within the `n` bytes at offset `e` keeps
every byte outside them. -/
theorem keeps_of_frame {m m' : Mem} {B : Addr} {len e n : Nat}
    (hf : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m') (hn : 0 < n) (fit : B.toNat + len * 8 ≤ 2 ^ 64)
    (he : e + n ≤ 8 * len) : Keeps B len [(e, n)] m m' := fun i hi hout =>
  hf _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have ho := hout (e, n) (List.mem_singleton_self _)
    exact Proof.Camellia.not_contains_off B ho (by omega) hn (by omega)

/-- What changed within the working space and only within one range of it
changed only within that range. -/
theorem frame_of_keeps {m m' : Mem} {B : Addr} {len e n : Nat}
    (hf : Frame [⟨B, 8 * len⟩] m m') (hk : Keeps B len [(e, n)] m m') (he : e + n ≤ 8 * len)
    (fit : 8 * len < 2 ^ 64) : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m' := by
  intro x hx
  by_cases hc : (⟨B, 8 * len⟩ : Region).Contains x 1
  · simp only [Region.Contains] at hc
    have hx' : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [hx']
    refine hk _ (by omega) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    by_contra hne
    refine hx _ (List.mem_singleton_self _) ?_
    rw [hx', show (x - B).toNat = e + ((x - B).toNat - e) by omega, ← VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega) (by omega)
  · exact hf x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc

end VG.Proof.Camellia.AArch64.Serial

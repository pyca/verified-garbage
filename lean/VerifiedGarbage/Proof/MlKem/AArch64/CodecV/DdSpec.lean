module

public import VerifiedGarbage.Proof.MlKem.AArch64.Width

/-!
# ML-KEM on AArch64: what `vg_mlkem_decode_decompress` reads and writes

Group `g` of the input is the number whose bytes are its bytes (`num g nb`), and coefficient `e`
of the group is its base-`2ᵈ` digit `e` (`byteDecode_group`), decompressed (`G_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (w : Width) (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x3
abbrev bR : Region := ⟨bP s₀, 32 * w.d⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (32 * w.d)
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B w s₀).getD j 0).toNat
/-- The first `j` bytes of group `g`, as a little-endian number. -/
def num (g j : Nat) : Nat := digits 8 ((List.range j).map fun j' => byte w s₀ (w.nb * g + j'))
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress w.d (B w s₀))[i]!).val
/-- The output's coefficients before. -/
def old (i : Nat) : BitVec 32 := coeffAt s₀.mem (fP s₀) i

end

structure Pre (w : Width) (s₀ : State) : Prop where
  rd : s₀.rd = [bR w s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR w s₀).Disjoint (polyRegion (fP s₀))

theorem num_succ (w : Width) (s₀ : State) (g j : Nat) :
    num w s₀ g (j + 1) = num w s₀ g j + 2 ^ (8 * j) * byte w s₀ (w.nb * g + j) :=
  digits_range_succ _ _ _

theorem num_lt (w : Width) (s₀ : State) (g j : Nat) : num w s₀ g j < 2 ^ (8 * j) :=
  digits_range_lt (fun _ => byte_lt _) _

theorem cg_lt {w : Width} (hw : WOk w) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    w.c * g + e < 256 := by
  have := hw.cG
  have : w.c * (g + 1) ≤ w.c * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

theorem nbg_le {w : Width} (hw : WOk w) {g : Nat} (hg : g < 256 / w.c) :
    w.nb * g + w.nb ≤ 32 * w.d := by
  have := hw.bytes
  have : w.nb * (g + 1) ≤ w.nb * (256 / w.c) := Nat.mul_le_mul_left _ hg
  rw [Nat.mul_succ] at this
  omega

/-- Coefficient `e` of group `g` of the output. -/
theorem G_eq {w : Width} (hw : WOk w) (s₀ : State) {g e : Nat} (hg : g < 256 / w.c) (he : e < w.c) :
    G w s₀ (w.c * g + e) =
      BitVec.ofNat 32 ((q * (num w s₀ g w.nb / 2 ^ (w.d * e) % 2 ^ w.d) + 2 ^ (w.d - 1)) / 2 ^ w.d) := by
  have hi := cg_lt hw hg he
  have hd12 : w.d < 12 := by have := hw.d_le; omega
  rw [G, decodeDecompress_get _ _ (show _ < n from hi),
    byteDecode_group hw.dc _ he (show _ < n from hi), bytes_map_take_drop _ (by
      rw [bytesAt_length]; exact nbg_le hw hg), ite_eq_left hd12, Nat.mod_mod,
    (decompress_val hw.mem (Nat.mod_lt _ (Nat.two_pow_pos _))).1]
  rfl

theorem Pre.byte_eq {w : Width} {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {j : Nat} (hj : j < 32 * w.d) (hw : w.d ≤ 10) :
    (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte w s₀ j := by
  rw [byte_frame (len := 32 * w.d) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by omega) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) (32 * w.d)).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

end VG.Proof.MlKem.AArch64.DD

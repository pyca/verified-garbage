module

public import VerifiedGarbage.Impl.Pbkdf2.Stream.PPC64LE
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import all Init.Data.Nat.Bitwise.Basic

/-!
# PBKDF2 over any streaming hash function on PPC64LE: `T ← T ⊕ U`

`n` 32-bit words of `U` at `o(r21)` exclusive-ored into `T` at `0(r23)`
(`Iter.xorT`) write `T ⊕ U` over `T` (`xor32_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE

open VG.PPC64LE
open VG.WriteBytes (writeBytes writeBytes_nil)
open VG.Proof.Sha256.Stream (write_eq_writeBytes writeBytes_append)
open Spec.Sha256 (bytesAt)
open Spec.Pbkdf2 (xorBytes)
open VG.Impl.Pbkdf2.Stream.PPC64LE (xor32)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_lwz wp_stw toNat_ofNat_lt)

/-- The exclusive-or of two words read, written, is their bytes'. -/
theorem writeW_xor (m m₁ m₂ : Mem) (d a b : Addr) (n : Nat) :
    m.writeW d (m₁.readW a (8 * n) ^^^ m₂.readW b (8 * n)) =
      writeBytes m d (xorBytes (bytesAt m₁ a n) (bytesAt m₂ b n)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, VG.Proof.Hmac.Common.extractLsb'_read _ _ h₁,
    VG.Proof.Hmac.Common.extractLsb'_read _ _ h₁]

theorem xorBytes_append (a b c d : List Byte) (h : a.length = c.length) :
    xorBytes (a ++ b) (c ++ d) = xorBytes a c ++ xorBytes b d := by
  simp only [xorBytes, List.zipWith_append h]

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) :
    (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

/-- The bytes at `B + j`, for `j` past what a `writeBytes` at `B` wrote. -/
theorem bytesAt_past (m : Mem) (B : Addr) (xs : List Byte) {j w : Nat} (hj : xs.length ≤ j)
    (hw : j + w < 2 ^ 64) :
    bytesAt (writeBytes m B xs) (B + BitVec.ofNat 64 j) w = bytesAt m (B + BitVec.ofNat 64 j) w := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine VG.Proof.Hmac.Common.writeBytes_other m B xs ?_
  rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The bytes at `A + j`, for `A`'s range separate from what a `writeBytes`
at `B` wrote. -/
theorem bytesAt_sep (m : Mem) {A B : Addr} (xs : List Byte) {j w : Nat}
    (hsep : Mem.Sep A (j + w) B xs.length) (hw : j + w < 2 ^ 64) :
    bytesAt (writeBytes m B xs) (A + BitVec.ofNat 64 j) w = bytesAt m (A + BitVec.ofNat 64 j) w := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes]
  split
  · rename_i h
    exact absurd h (hsep _ (by
      rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega))
  · rfl

/-- One more word exclusive-ored from `A` into `B`. -/
theorem xor_mem (m : Mem) (A B : Addr) (n w : Nat)
    (hsep : Mem.Sep A (w * n + w) B (w * n + w)) (hlt : w * n + w < 2 ^ 64) :
    let mm := writeBytes m B (xorBytes (bytesAt m B (w * n)) (bytesAt m A (w * n)))
    mm.writeW (B + BitVec.ofNat 64 (w * n))
      (mm.readW (B + BitVec.ofNat 64 (w * n)) (8 * w) ^^^ mm.readW (A + BitVec.ofNat 64 (w * n)) (8 * w)) =
      writeBytes m B (xorBytes (bytesAt m B (w * n + w)) (bytesAt m A (w * n + w))) := by
  intro mm
  have hl : (xorBytes (bytesAt m B (w * n)) (bytesAt m A (w * n))).length = w * n := by
    rw [xorBytes_length _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length, VG.Proof.Hmac.Common.bytesAt_length]),
      VG.Proof.Hmac.Common.bytesAt_length]
  rw [writeW_xor, bytesAt_past _ _ _ (by omega) (by omega), bytesAt_sep _ _ ?_ (by omega),
    VG.Proof.Hmac.Common.bytesAt_add m B, VG.Proof.Hmac.Common.bytesAt_add m A,
    xorBytes_append _ _ _ _ (by rw [VG.Proof.Hmac.Common.bytesAt_length, VG.Proof.Hmac.Common.bytesAt_length])]
  · rw [← writeBytes_append _ _ _ _ (by
      rw [hl, xorBytes_length _ _ (by
        rw [VG.Proof.Hmac.Common.bytesAt_length, VG.Proof.Hmac.Common.bytesAt_length]),
        VG.Proof.Hmac.Common.bytesAt_length]; omega), hl]
  · rw [hl]
    intro x hx hy
    exact hsep x (by omega) (by omega)

theorem wp_xorL {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  VG.Proof.MdStream.PPC64LE.WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `T ← T ⊕ U`, for `n` words of `U` at `o(src)` and `T` at `0(dst)`. -/
theorem xor32_ok {src dst : Reg} (hs : src ≠ .r8 ∧ src ≠ .r9) (hd : dst ≠ .r8 ∧ dst ≠ .r9)
    (hs0 : src ≠ .r0) (hd0 : dst ≠ .r0) (o : Nat) (n : Nat) (hb : o + 4 * n ≤ 2 ^ 15 ∧ 4 * n ≤ 2 ^ 15) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o) (4 * n) (s.gpr dst) (4 * n) →
    (∀ s', (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst)
        (xorBytes (bytesAt s.mem (s.gpr dst) (4 * n))
          (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o) (4 * n))) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xor32 src dst o) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by
      rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, VG.Proof.Hmac.Common.bytesAt_zero]
      exact (writeBytes_nil _ _).symm)
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xor32, List.cons_append, List.nil_append]
    refine wp_lwz (a := s.gpr dst + BitVec.ofNat 64 (4 * n)) (by omega) (by rw [g₁ _ hd.1 hd.2])
      (by rw [rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hout n (by omega); exact ⟨r, List.mem_append_right _ hr, hc⟩) (fun s₂ u₂ => ?_) hd0
    refine wp_lwz (a := s.gpr src + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2, VG.Proof.Hmac.Stream.PPC64LE.add_off])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hin n (by omega)) (fun s₃ u₃ => ?_) hs0
    refine wp_xorL fun s₄ u₄ => ?_
    refine wp_stw (a := s.gpr dst + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, g₁ _ hd.1 hd.2])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      (fun s₅ u₅ => k s₅ (fun r h8 h9 => by rw [u₅.gpr, u₄.other r h8, u₃.other r h9, u₂.other r h8, g₁ r h8 h9])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_) hd0
    rw [u₅.mem, u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₄.mem, u₃.mem, u₂.mem, m₁,
      BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, Nat.mul_succ]
    exact xor_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Pbkdf2.Stream.PPC64LE

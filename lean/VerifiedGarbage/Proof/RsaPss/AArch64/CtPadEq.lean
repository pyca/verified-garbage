import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPss.CtPad

/-!
# RSASSA-PSS on AArch64: the padded message in `Y`

After `0x80` (`v80`), the length field at `oLen` (`updL`) and the length
field ORed into the last block (`LenLoop.vLen`), the first `fb + 1` blocks
of `Y` are the padded message `padded` (`ypad`), so the hash value of those
blocks is that of `md.pad msg` (`compressList_ypad`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPss (padded lastBlk pad_getD pad_length)

/-- `Y`, with `0x80`, the length field at `oLen` and in the last block. -/
def vPad (B L : Nat) (V : Nat → Byte) (ℓ n : Nat) (lenB : List Byte) : Nat → Byte :=
  LenLoop.vLen B L (updL (v80 V ℓ n) oLen lenB) ((ℓ + L) / B)

theorem or0 (x : Byte) : x ||| 0 = x := by revert x; decide

theorem ypad {B L : Nat} {V : Nat → Byte} {msg lenB : List Byte} {n : Nat} (hB : 0 < B) (hLB : L < B)
    (hL : L ≤ 16) (hlen : lenB.length = L) (hn : n ≤ 2048) (hfit : msg.length + L < n)
    (hV : ∀ i < n, V (oY + i) = if i < msg.length then msg.getD i 0 else 0) :
    ∀ i < B * ((msg.length + L) / B + 1), i < n →
      vPad B L V msg.length n lenB (oY + i) = padded B L msg lenB i := by
  intro i hi hin
  have hlt := Nat.lt_mul_div_succ (msg.length + L) hB
  generalize hfb : (msg.length + L) / B = fb at hlt hi
  rw [Nat.mul_succ] at hlt hi
  have hsl : B * fb + B - L = B * fb + (B - L) := by omega
  simp only [vPad, LenLoop.vLen, padded, lastBlk, hfb, hsl]
  have hv : ∀ j, oY + j < oY + n → updL (v80 V msg.length n) oLen lenB (oY + j) =
      V (oY + j) ||| (if j = msg.length then 0x80 else 0) := fun j hj => by
    simp only [updL, v80]
    rw [ite_eq_right (by unfold oLen oY; omega), ite_eq_left ⟨by omega, hj⟩, Nat.add_sub_cancel_left]
  by_cases h1 : i < msg.length
  · rw [ite_eq_right (by omega), hv i (by omega), ite_eq_right (by omega), or0, hV i hin,
      ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = msg.length
    · subst h2
      rw [ite_eq_right (by omega), hv _ (by omega), ite_eq_left rfl, hV _ hin, ite_eq_right h1, ite_eq_left rfl]
      decide
    · rw [ite_eq_right h2]
      by_cases h3 : B * fb + (B - L) ≤ i ∧ i < B * fb + B
      · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h3, hv i (by omega), ite_eq_right h2, or0,
          hV i hin, ite_eq_right h1]
        simp only [updL]
        rw [ite_eq_left ⟨by omega, by rw [hlen]; omega⟩, show oLen + (oY + i - (oY + B * fb + (B - L))) - oLen =
          i - (B * fb + (B - L)) by omega]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right h3, hv i (by omega), ite_eq_right h2, or0, hV i hin,
          ite_eq_right h1]

end VG.Proof.RsaPss.AArch64

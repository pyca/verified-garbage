module
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Word copies in the OAEP decoding workspace

The source word is read before the destination is written. Neither alignment
nor disjointness between the two words is required; the frame is preserved.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)

/-- Copy eight bytes from the pre-store workspace. -/
def copy8V (V : Nat → Byte) (dst src : Nat) : Nat → Byte :=
  fun x => if dst ≤ x ∧ x < dst + 8 then V (src + (x - dst)) else V x

/-- A word load/store implements the byte copy even when the words overlap. -/
theorem Rep.copy8 {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep m F S V W) {dst src : Nat}
    (hd : dst + 8 ≤ oRsa) (hs : src + 8 ≤ oRsa) :
    Rep (m.writeW (off S dst) (m.readW (off S src) 64)) F S (copy8V V dst src) W where
  scr x hx := by
    have hw : dst + 8 ≤ 2 ^ 64 := by unfold oRsa at hd; omega
    have hrange : (off S x - off S dst).toNat < 8 ↔ dst ≤ x ∧ x < dst + 8 := by
     rw [Offset.lt_iff _ S hw, Mem.sub_ofNat_toNat S (by unfold oRsa at hx; omega)]
    change (if (off S x - off S dst).toNat < 8 then
     (m.read (off S src) 8).extractLsb' (8 * (off S x - off S dst).toNat) 8 else m (off S x)) = _
    unfold copy8V
    by_cases h : dst ≤ x ∧ x < dst + 8
    · rw [ifp (hrange.mpr h), ifp h, Offset.sub_toNat S h.1 (by unfold oRsa at hx; omega),
       Mem.extractLsb'_read m (off S src) (n := 8) (by omega)]
      change m (off (off S src) (x - dst)) = _
      rw [off_off]
      exact R.scr _ (by omega)
    · rw [ifn (fun e => h (hrange.mp e)), ifn h, R.scr x hx]
  fr k hk := by
    rw [word, Mem.readW_writeW_sep (Region.Disjoint.sep G.dFS (G.cFw hk) (cS S hd)) (by decide)]
    exact R.fr k hk

theorem frame_copy8 {F S : Addr} {ws : List Region} {m : Mem} {dst src : Nat}
    (hd : dst + 8 ≤ oRsa) :
    Frame (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: ws) m
      (m.writeW (off S dst) (m.readW (off S src) 64)) := by
  exact (Frame.refl _ _).write (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    _ (cS S hd)

end VG.Proof.RsaOaep.AArch64

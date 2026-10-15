module

public import VerifiedGarbage.Proof.Dsa.X86.DigestPadByte
public import VerifiedGarbage.Proof.Dsa.X86.FailureStep
public import VerifiedGarbage.Proof.Hmac.Common

/-! # Copying at most 32 digest bytes after a leading zero prefix -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem paddedByte_keep {s t : Mem} {base : Addr} {source : BitVec 32} {size len j : Nat}
    (O : Outside base DigestPad.output 32 s t)
    (apart : Region.Disjoint ⟨source.setWidth 64, len⟩ ⟨base, size⟩)
    (space : DigestPad.output + 32 ≤ size) (hj : j < 32) (hl : len ≤ 32) :
    paddedByte t (source.setWidth 64) len j = paddedByte s (source.setWidth 64) len j := by
  unfold paddedByte
  split
  · rfl
  · rename_i H
    apply O _ (.inr ?_)
    have no := apart (source.setWidth 64 + BitVec.ofNat 64 (j - (32 - len)))
      (Offset.contains_base _ (by omega : j - (32 - len) + 1 ≤ len) (by omega))
    change ¬ (ofs base (source.setWidth 64 + BitVec.ofNat 64 (j - (32 - len))) + 1 ≤ size) at no
    omega

theorem digestPadPrefix_ok {s : State} {base : Addr} {size len : Nat} {source : BitVec 32}
    (hs : Scr s base size) (space : DigestPad.output + 32 ≤ size)
    (hp : s.gpr .esi = source) (hl : len ≤ 32) (fits : source.toNat + len ≤ 2 ^ 32)
    (read : ∀ i < len, InRegions (s.rd ++ s.wr) (source.setWidth 64 + BitVec.ofNat 64 i) 1)
    (apart : Region.Disjoint ⟨source.setWidth 64, len⟩ ⟨base, size⟩)
    (k : Nat) (hk : k ≤ 32) :
    WP isa (.block ((List.range k).flatMap (DigestPad.byte len))) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base DigestPad.output) k =
        (List.range k).map (paddedByte s.mem (source.setWidth 64) len) ∧
      Outside base DigestPad.output 32 s.mem t.mem ∧ Keeps [.eax] s t := by
  induction k with
  | zero => exact WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega)) fun u ⟨Bytes, O, K⟩ => ?_)
    refine WP.mono (digestPadByte_ok (hs.of_keeps K (by decide)) space
      ((K.1 _ (by decide)).trans hp) (by omega) hl fits
      (by intro i hi; rw [K.2.1, K.2.2]; exact read i hi)) fun t ⟨Mem, Keep⟩ => ?_
    refine ⟨?_, ?_, K.trans Keep⟩
    · rw [Mem]
      have Step := VG.Proof.Hmac.Common.bytesAt_snoc u.mem (off base DigestPad.output)
        (j := k) (by omega) (paddedByte u.mem (source.setWidth 64) len k)
      change Spec.Rsa.bytesAt _ _ _ = _ at Step
      rw [Offset.add_add] at Step
      rw [Step]
      change Spec.Rsa.bytesAt u.mem (off base DigestPad.output) k ++
        [paddedByte u.mem (source.setWidth 64) len k] = _
      rw [Bytes, paddedByte_keep O apart space (by omega) hl]
      simp only [List.map_append, List.map_cons, List.map_nil]
    · rw [Mem]
      have W := writeW8_outside u.mem base (d := DigestPad.output + k)
        (paddedByte u.mem (source.setWidth 64) len k) (by have := hs.nowrap; omega)
      exact O.trans (W.mono (by omega) (by omega))

theorem digestPadFill_relCT (len : Nat) :
    RelCT isa (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true))
      (.block (DigestPad.fill len)) (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true)) :=
  blockFlatMap_relCT _ _ (digestPadByte_relCT len)

end VG.Proof.Dsa.X86

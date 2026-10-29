module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Spec.Rsa.Contract
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
/-! The native digest-to-subgroup-candidate operation. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/QShapeEnds.lean`, which only this module imported.
section

/-! Correctness of the two subgroup-candidate endpoint writes. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Ffdh.ParameterCandidate

theorem qShapeEnds_ok {s : State} {op : Addr} {n : Nat}
    (hn : 2 ≤ n) (hbound : n < 2 ^ 64)
    (hop : s.gpr .x13 = op) (hlen : s.gpr .x14 = BitVec.ofNat 64 n)
    (hr0 : InRegions (s.rd ++ s.wr) op 1)
    (hrn : InRegions (s.rd ++ s.wr) (off op (n - 1)) 1)
    (hw0 : InRegions s.wr op 1) (hwn : InRegions s.wr (off op (n - 1)) 1) :
    WP isa (.block Impl.Dsa.AArch64.Generation.qShapeEnds) s fun t =>
      t.mem = (s.mem.writeW op (s.mem op ||| (128#8))).writeW
        (off op (n - 1)) (s.mem (off op (n - 1)) ||| (1#8)) ∧
      Keep [.x0, .x2, .x4] s t := by
  refine WP.keep [.x0, .x2, .x4] ?_ rfl rfl rfl
  have hp : op + BitVec.ofNat 64 n - (1#64) = off op (n - 1) := by
    simp only [off]
    apply BitVec.sub_eq_iff_eq_add.mpr
    rw [BitVec.add_assoc]
    change op + BitVec.ofNat 64 n = op + (BitVec.ofNat 64 (n - 1) + BitVec.ofNat 64 1)
    rw [BitVec.ofNat_add_ofNat]
    rw [show n - 1 + 1 = n by omega]
  have hne : off op (n - 1) ≠ op := by
    simpa [off] using Offset.add_ofNat_ne op (show n - 1 < 2 ^ 64 by omega)
      (show 0 < 2 ^ 64 by decide) (show n - 1 ≠ 0 by omega)
  simp only [off] at hp hne hrn hwn ⊢
  unfold Impl.Dsa.AArch64.Generation.qShapeEnds
  brun [State.read, State.write, hop, hlen, hr0, hrn, hw0, hwn, hp, read_one,
    BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq,
    WriteBytes.writeW8_apply, hne]
  change (s.mem.writeW op (s.mem op ||| (128#8))).writeW _
    ((s.mem.writeW op (s.mem op ||| (128#8))) _ ||| (1#8)) = _
  rw [WriteBytes.writeW8_apply, ite_eq_right hne]

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Ffdh.ParameterCandidate

theorem qShape_ok {s : State} {src op : Addr} {bs : List Byte}
    (hn : 2 ≤ bs.length) (hb : bs.length < 2 ^ 64)
    (hsrc : s.gpr .x12 = src) (hop : s.gpr .x2 = op)
    (hlen : s.gpr .x9 = BitVec.ofNat 64 bs.length)
    (hr : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hw : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off src i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ j < bs.length, off src i ≠ off op j) :
    WP isa Impl.Dsa.AArch64.Generation.qShape s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length = shapedOctets bs 7 ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.x0, .x2, .x4, .x9, .x12, .x13, .x14] s t := by
  unfold Impl.Dsa.AArch64.Generation.qShape
  refine WP.seq (WP.mono (WP.keep [.x13, .x14] (Q := fun u =>
    u.gpr .x13 = op ∧ u.gpr .x14 = BitVec.ofNat 64 bs.length ∧ u.mem = s.mem)
    (by brun [hop, hlen]) rfl rfl rfl) fun u ⟨⟨huop, hulen, hum⟩, ku⟩ => ?_)
  have hru : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off src i) 1 := by
    intro i hi; rw [ku.rd, ku.wr]; exact hr i hi
  have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
    intro i hi; rw [ku.wr]; exact hw i hi
  refine WP.seq (WP.mono (random_copyRest_ok ((ku.gpr _ (by decide)).trans hsrc)
    ((ku.gpr _ (by decide)).trans hop) ((ku.gpr _ (by decide)).trans hlen)
    hb hru hwu hsep) fun v ⟨hcopy, hf, kv⟩ => ?_)
  have hwv : ∀ i < bs.length, InRegions v.wr (off op i) 1 := by
    intro i hi; rw [kv.wr]; exact hwu i hi
  have hrw : ∀ i < bs.length, InRegions (v.rd ++ v.wr) (off op i) 1 := by
    intro i hi
    rcases hwv i hi with ⟨r, hm, hc⟩
    exact ⟨r, List.mem_append_right _ hm, hc⟩
  refine WP.mono (qShapeEnds_ok hn hb ((kv.gpr _ (by decide)).trans huop)
    ((kv.gpr _ (by decide)).trans hulen) (by simpa [off] using hrw 0 (by omega))
    (hrw _ (by omega)) (by simpa [off] using hwv 0 (by omega)) (hwv _ (by omega)))
    fun t ⟨htm, kt⟩ => ?_
  refine ⟨?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [htm]
    apply VG.Proof.Dsa.Generation.qShape_memory hn hb
    intro i hi
    rw [hcopy i hi, hum]
    exact hbytes i hi
  · intro a ha
    rw [htm, WriteBytes.writeW8_apply, ite_eq_right (ha _ (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right (by simpa [off] using ha 0 (by omega)),
      hf a (fun i hi => ha i hi), hum]

end VG.Proof.Dsa.AArch64.Generation

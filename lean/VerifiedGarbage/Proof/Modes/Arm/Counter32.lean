module

import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Modes.Arm.Counter32
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# GCM's `inc₃₂` on ARMv7

`inc32At` run once, with its memory as an explicit write (`inc32Mem`): the
last word, loaded, byte-reversed, plus 1, reversed again and stored.
`inc32Mem_bytes`: the block it leaves is `inc₃₂` of the one it read, as the
number `ctr32Val V 1` of its bytes (`Proof/Modes/Ctr32.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm.Counter32

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

/-- The memory after `inc32At` on the block at `Q`. -/
def inc32Mem (m : Mem) (Q : Addr) : Mem :=
  m.writeW (Q + BitVec.ofNat 64 12) (rev (rev (m.readW (Q + BitVec.ofNat 64 12) 32) + 1))

theorem incr32_ok (s : State) {base : Reg} (h9 : base ≠ .r9) {off : Nat} (hoff : off + 16 ≤ 4096) {Q : Addr}
    (ha : State.addr (s.gpr base + BitVec.ofNat 32 (off + 12)) = Q + BitVec.ofNat 64 12)
    (hr : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (hw : InRegions s.wr (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa (inc32At base off) s = some s' ∧
      (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = inc32Mem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := Proof.MdStream.Arm.op2_imm (by decide)
  have h12 : off + 12 < 4096 := by omega
  refine ⟨_, by
    simp only [↓reduceIte, inc32At, runBlock_cons, runStep_some, runBlock_nil, exec,
      i1, State.load32, State.store32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      h9, h12, ha, hr, hw]
    rfl, ?_⟩
  exact ⟨fun r h₁ => by simp only [gpr_setReg, h₁, ite_false], rfl, rfl, rfl, rfl⟩

theorem rev_eq (a : BitVec 32) : rev a = AesCtr.rv32 a := rfl

theorem inc32Mem_bytes (m : Mem) (Q : Addr) :
    bytesAt (inc32Mem m Q) Q 16 = ofNat (Proof.Modes.ctr32Val (toNat (bytesAt m Q 16)) 1) 16 := by
  have split (m' : Mem) : bytesAt m' Q 16 = bytesAt m' Q 12 ++ bytesAt m' (Q + BitVec.ofNat 64 12) 4 :=
    AesCtr.bytesAt_append m' Q 12 4
  have hl : (bytesAt m Q 16).length = 16 := by simp [bytesAt]
  have hlo : (bytesAt m Q 12).length = 12 := by simp [bytesAt]
  generalize hV : toNat (bytesAt m Q 16) = V
  have hV' := hV
  have hdec : bytesAt m Q 16 = ofNat (V / 256 ^ 4) 12 ++ ofNat V 4 := by
    rw [← AesCtr.ofNat_add, ← hV]; exact (AesCtr.ofNat_toNat hl).symm
  rw [split m] at hdec
  obtain ⟨hhi, hlow⟩ := List.append_inj hdec (by rw [hlo, AesCtr.length_ofNat])
  have frame : bytesAt (inc32Mem m Q) Q 12 = bytesAt m Q 12 := by
    apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, inc32Mem, Mem.writeW]
    exact Mem.write_apply (by
      rw [show Q + BitVec.ofNat 64 i - (Q + BitVec.ofNat 64 12) = BitVec.ofNat 64 (2 ^ 64 - (12 - i)) by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
      simp only [BitVec.toNat_ofNat]; omega)
  rw [split, frame, inc32Mem, rev_eq, rev_eq, AesCtr.bytesAt_writeW_rv32, show (16 : Nat) = 12 + 4 from rfl,
    AesCtr.ofNat_add, hhi]
  have h4 := congrArg toNat hlow
  rw [AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat, AesCtr.toNat_ofNat] at h4
  have hw := (AesCtr.rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  congr 1
  · exact AesCtr.ofNat_congr (by unfold Proof.Modes.ctr32Val; omega)
  · refine AesCtr.ofNat_congr ?_
    rw [BitVec.toNat_add, e1]
    unfold Proof.Modes.ctr32Val
    simp only [Nat.reducePow] at *
    omega

theorem inc32Mem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (inc32Mem m Q) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))

end VG.Proof.Modes.Arm.Counter32

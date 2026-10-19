module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The primality workspace needs no initialized caller memory. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

def workspaceRanges : List (Nat × Nat) := [(48, 16), (64, 64), (224, 8)]

theorem workspace_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : slot w 16 ≤ Z)
    (hw : 2 ≤ w) (hw48 : w ≤ 48) :
    WP isa (Impl.Dsa.AArch64.Generation.workspace w) s fun t =>
      Ws t B Z w ∧ word t.mem B (8 * sMinv) = 0 ∧
      Frm B workspaceRanges s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  have hz := hs.nowrap
  have h256 : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  have h16 : (BitVec.ofNat 16 w).setWidth 64 = BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hstride : (BitVec.ofNat 16 (8 * (w + 2))).setWidth 64 = BitVec.ofNat 64 (8 * (w + 2)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  unfold Impl.Dsa.AArch64.Generation.workspace
  refine WP.seq (WP.mono (WP.keep [.x3, .x12] (Q := fun u =>
    u.gpr .x12 = BitVec.ofNat 64 w ∧
    u.mem = (s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w)).writeW (off B (8 * sMinv)) (0#64))
    (by
      unfold Impl.Dsa.AArch64.Generation.workspaceHead
      brun [h0, h16, hdr_enc (show sW < 32 by decide), hdr_enc (show sMinv < 32 by decide),
        hs.st (d := 8 * sW) (by simp only [sW]; omega), hs.st (d := 8 * sMinv) (by simp only [sMinv]; omega)]
      rfl)
    rfl rfl rfl) fun u ⟨⟨hu12, hum⟩, ku⟩ => ?_)
  have hu0 := (ku.gpr .x0 (by decide)).trans h0
  have huS := hs.congr ku.wr
  have huW : word u.mem B (8 * sW) = BitVec.ofNat 64 w := by
    rw [hum, (writeW_outside _ B (0#64) (d := 8 * sMinv) (by simp only [sMinv]; omega)).word
      (by decide) (by simp only [sW]; omega), word_writeW_self]
  have huI : word u.mem B (8 * sMinv) = 0 := by rw [hum, word_writeW_self]; rfl
  have fu : Frm B workspaceRanges s.mem u.mem := by
    rw [hum]
    apply Frm.trans (m₂ := s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w))
    · exact Frm.of_outside ((writeW_outside _ B _ (d := 8 * sW) (by simp only [sW]; omega)).mono
        (o' := 48) (n' := 16) (by decide) (by decide)) (by simp [workspaceRanges])
    · exact Frm.of_outside ((writeW_outside _ B _ (d := 8 * sMinv) (by simp only [sMinv]; omega)).mono
        (o' := 48) (n' := 16) (by decide) (by decide)) (by simp [workspaceRanges])
  refine WP.seq (WP.mono (setBases_ok huS hu0 hu12 (by simp only [sArr]; omega))
    fun v ⟨hvArr, ov, kv⟩ => ?_)
  have hv0 := (kv.gpr .x0 (by decide)).trans hu0
  have hvS := huS.congr kv.wr
  have hvW := (ov.word (d := 8 * sW) (by decide) (by simp only [sW]; omega)).trans huW
  have hvI := (ov.word (d := 8 * sMinv) (by decide) (by simp only [sMinv]; omega)).trans huI
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = v.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (w + 2))))
    (by
      unfold Impl.Dsa.AArch64.Generation.workspaceStride
      brun [hv0, hstride, hdr_enc (show sStride < 32 by decide),
        hvS.st (d := 8 * sStride) (by simp only [sStride, sFn]; omega)]) rfl rfl rfl)
    fun t ⟨htm, kt⟩ => ?_
  have ot : Outside B (8 * sStride) 8 v.mem t.mem := by
    rw [htm]; exact writeW_outside _ B _ (by simp only [sStride, sFn]; omega)
  have fixed (i : Nat) (hi : i < 16) : word t.mem B (8 * i) = word v.mem B (8 * i) :=
    ot.word (by simp only [sStride, sFn]; omega) (by omega)
  refine ⟨⟨hvS.congr kt.wr, (kt.gpr .x0 (by decide)).trans hv0,
    (fixed sW (by decide)).trans hvW, ?_, fun j hj =>
      (fixed (sArr j) (by unfold sArr; omega)).trans (hvArr j hj), hZ, hw, by omega⟩,
    (fixed sMinv (by decide)).trans hvI, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [htm, word_writeW_self]
  · exact (fu.trans (Frm.of_outside ov (by simp [workspaceRanges, sArr]))).trans
      (Frm.of_outside ot (by simp [workspaceRanges, sStride, sFn]))

end VG.Proof.Dsa.AArch64.Generation

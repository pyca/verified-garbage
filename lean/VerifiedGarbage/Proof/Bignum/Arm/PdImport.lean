module

public import VerifiedGarbage.Impl.Bignum.Arm.PdImport
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-! # Import both public precomputation arrays in the shared 64-bit word format -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

structure PdImportInput (base pp : BitVec 32) (len w : Nat) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  sourceFit : pp.toNat + 16 * w ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr pp) (16 * w)
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr pp, 16 * w⟩
  source : s.gpr .r4 = pp

theorem pdImport_ok (s : State) {base pp : BitVec 32} {len w : Nat}
    (h : PdImportInput base pp len w s) :
    WP isa pdImport s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = (s.mem.read (State.addr pp) (8 * w)).toNat ∧
      numAt t.mem (State.addr base) w 4 = (s.mem.read (off (State.addr pp) (8 * w)) (8 * w)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  have nowrap := h.ready.workspace.nowrap
  let pp2 := pp + BitVec.ofNat 32 (8 * w)
  have address : State.addr pp2 = off (State.addr pp) (8 * w) := addr_add (by have := h.sourceFit; omega)
  have secondFit : pp2.toNat + 8 * w ≤ 2 ^ 32 := by
    have sourceFit := h.sourceFit
    simp only [pp2, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * w < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : pp.toNat + 8 * w < 2 ^ 32)]
    omega
  have firstRead : InRegions (s.rd ++ s.wr) (State.addr pp) (8 * w) := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) h.read (by omega) (by omega)
  have secondRead : InRegions (s.rd ++ s.wr) (State.addr pp2) (8 * w) := by
    rw [address]; exact CallLay.inRegions_sub h.read (by omega) (by omega)
  have firstSep := h.separate.sub_right (Region.sub_prefix (show 8 * w ≤ 16 * w by omega))
  have secondSep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr pp2, 8 * w⟩ := by
    apply h.separate.sub_right
    rw [address]; exact Offset.sub_base _ (by omega)
  rw [pdImport, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
  have readyU := h.ready.of_mem moved.mem (moved.rest (by simp : Reg.r2 ∈ [.r2]))
    ((moved.other .r0 (by decide)).trans h.ready.ptr)
  rw [WP.seq_iff]
  refine WP.mono (importArrayLayout_ok u readyU (by decide : 0 < 8)
    (by have := h.sourceFit; omega) (by rw [moved.rd, moved.wr]; exact firstRead) firstSep moved.gpr
    ((moved.other .r4 (by decide)).trans h.source)) ?_
  rintro v ⟨readyV, first, _, frameV, restV, sourceV⟩
  rw [moved.mem] at first frameV
  have rv : Rest roundClobbers s v := (moved.rest (by decide)).trans restV
  have header := nativeHeader_of_layout v.mem base nowrap (Nat.le_refl _) readyV.layout
  rw [readyV.width] at header
  rw [WP.seq_iff]
  refine WP.mono (precomputeOutAdvance_ok v readyV.workspace (by omega) readyV.ptr header.count) ?_
  rintro z ⟨sourceZ, indexZ, memZ, restZ⟩
  have readyZ := readyV.of_mem memZ restZ ((restZ.gpr .r0 (by decide)).trans readyV.ptr)
  refine WP.mono (importArrayLayout_ok z readyZ (by decide : 4 < 8) secondFit
    (by rw [restZ.rd, restZ.wr, rv.rd, rv.wr]; exact secondRead) secondSep indexZ
    (by rw [sourceZ, sourceV])) ?_
  rintro t ⟨readyT, second, keepsT, frameT, restT, _⟩
  rw [memZ, address] at second
  rw [memZ] at frameT
  have publicEq := WorkspaceEq.of_frame (by have := h.sourceFit; omega : 16 * w < 2 ^ 64)
    frameV (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate.symm)
  have unchanged := publicEq.read (8 * w) (8 * w) (by omega)
  rw [unchanged] at second
  have firstT := keeps_array_num keepsT fits
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide : 0 ≠ 4)
  rw [memZ] at firstT
  exact ⟨readyT, firstT.trans first, second, frameV.trans frameT,
    rv.trans ((restZ.mono (by decide)).trans restT)⟩

end VG.Proof.Bignum.Arm

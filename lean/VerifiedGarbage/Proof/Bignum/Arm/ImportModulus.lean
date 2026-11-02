module

public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.ModulusReady
import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Import the modulus while preserving its workspace layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem importModulus_ok (s : State) {base src : BitVec 32} {len w k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (hk : 0 < k) (fit : k ≤ 8 * w) (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (ptr : s.gpr .r0 = base) (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa importModulus s fun t => Layout t.mem (State.addr base) len ∧
      wOf t.mem (State.addr base) = w ∧ t.gpr .r0 = base ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [importModulus, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
  refine WP.mono (loadBEFn_ok u (ws.congr moved.wr) (by rw [moved.mem]; exact layout)
    (by rw [moved.mem]; exact width) (o := 0) (by decide) hk fit srcFit
    (by rw [moved.rd, moved.wr]; exact read) sep
    ((moved.other .r0 (by decide)).trans ptr) moved.gpr
    ((moved.other .r4 (by decide)).trans source) ((moved.other .r6 (by decide)).trans count)
    (by rw [moved.rd, moved.wr, moved.sp]; exact stackRead)
    (by rw [moved.sp]; exact stackSep) (by rw [moved.mem, moved.sp]; exact saved)) ?_
  rintro t ⟨value, outside, frame, keep, out⟩
  rw [moved.mem] at value outside frame
  have kl := array_outside_layout outside layout
  exact ⟨kl.2, kl.1.trans width, out, value, frame, (moved.rest (by simp [roundClobbers])).trans keep⟩

end VG.Proof.Bignum.Arm

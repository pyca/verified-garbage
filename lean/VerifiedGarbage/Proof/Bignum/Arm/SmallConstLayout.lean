module
public import Batteries.Logic
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize constants before the secret modulus has been sanitized -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem smallConstLayout_ok (s : State) {base : BitVec 32} {len w o : Nat} (value : BitVec 32)
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base)
    (ho : o < 8) (encO : encodable (BitVec.ofNat 32 o) = true) (encV : encodable value = true)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (smallConst (BitVec.ofNat 32 o) value) s fun t =>
      Layout t.mem (State.addr base) len ∧ wOf t.mem (State.addr base) = w ∧
      numAt t.mem (State.addr base) w o = value.toNat ∧
      Outside (State.addr base) (arrAt w o) (8 * w) s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  rw [smallConst, WP.seq_iff]
  refine WP.mono (smallConstArgs_ok s _ value encO encV) ?_
  rintro u ⟨index, val, mem, rest⟩
  have body := setSmallFn_ok u (ws.congr rest.wr) (by rw [mem]; exact layout) ho
    ((rest.gpr .r0 (by decide)).trans ptr) index
    (by rw [rest.rd, rest.wr, rest.sp]; exact stackRead) (by rw [rest.sp]; exact stackSep)
    (by rw [mem, rest.sp]; exact saved)
  have widthU : wOf u.mem (State.addr base) = w := by rw [mem]; exact width
  simp only [widthU] at body
  refine WP.mono body ?_
  rintro t ⟨number, _, outside, frame, keep, out⟩
  rw [val] at number
  rw [mem] at outside frame
  have keeps := outside_array_keeps outside (len := len) (by have := ws.nowrap; omega)
  have kl := keeps_layout layout (by rw [width]; exact keeps)
  exact ⟨kl.2, kl.1.trans width, number, outside, frame,
    (rest.mono (by decide)).trans keep, out⟩

end VG.Proof.Bignum.Arm

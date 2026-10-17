module

public import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Zero a complete extended arithmetic operand while preserving all other bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem clearOperandBuffer_ok (s : State) {base : BitVec 32} {size slot w o : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096)
    (outFit : o + 4 * (2 * w + 2) ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) slot) 32 = base + BitVec.ofNat 32 o)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (clearOperandBuffer slot) s fun t => val32 t.mem (State.addr base) o (2 * w + 2) = 0 ∧
      Outside (State.addr base) o (4 * (2 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [clearOperandBuffer, WP.seq_iff]
  refine WP.mono (clearOperandBufferArgs_ok s ws fit slotFit hs ptr count link) ?_
  rintro u ⟨ptrU, countU, zeroU, memU, restU⟩
  have ctx : ZeroCtx u base size o (2 * w + 2) :=
    ⟨ws.nowrap, outFit, by rw [restU.wr]; exact ⟨_, ws.writable, Region.contains_self _ _⟩⟩
  rw [WP.seq_iff]
  refine WP.mono (zero_ok u ctx (by omega) ptrU countU zeroU) ?_
  intro v inv
  have outside := inv.outside
  rw [memU] at outside
  have frame := outside_workspace outside outFit
  have restUV : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans
    (inv.rest.mono (by simp [roundClobbers]))
  refine WP.mono (restoreBase_ok v (by rw [restUV.rd, restUV.wr, restUV.sp]; exact stackRead)
    (saved_base_kept frame stackSep saved restUV.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨by rw [memT]; exact inv.value, by rw [memT]; exact outside,
    by rw [memT]; exact frame, ptrT, restUV.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm

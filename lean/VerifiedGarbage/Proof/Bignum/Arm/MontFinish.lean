module

public import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Canonical Montgomery output using the workspace temporary -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem montFinish_ok (s : State) {base : BitVec 32} {size out acc mod tmp n : Nat}
    (ctx : CsubCtx s base size out acc mod tmp n) (hn : 0 < n) (ht : tmp + 32 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (mn : s.mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n)
    (mo : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out)
    (ma : s.mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc)
    (mm : s.mem.readW (off (State.addr base) (tmp + 8)) 32 = base + BitVec.ofNat 32 mod)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n) :
    WP isa montFinish s fun t =>
      val32 t.mem (State.addr base) out n =
        val32 s.mem (State.addr base) acc (n + 2) % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [montFinish, WP.seq_iff]
  refine WP.mono (finishArgs_ok s ⟨ctx.sub.nowrap, ctx.sub.writable⟩ ht ptr mn mo ma mm) ?_
  rintro u ⟨p0, p9, p10, p12, count, lr, carry, mem, keep⟩
  have cu : CsubCtx u base size out acc mod tmp n := {
    ctx with sub := { ctx.sub with writable := by rw [keep.wr]; exact ctx.sub.writable } }
  refine WP.mono (csub_ok u cu hn p0 p10 p12 p9 lr count carry (by rw [mem]; exact hT)) ?_
  rintro t ⟨value, outside, rest⟩
  rw [mem] at value outside
  exact ⟨value, outside, (keep.mono (by simp [roundClobbers])).trans
    (rest.mono (by simp [subLoopClobbers, roundClobbers]))⟩

end VG.Proof.Bignum.Arm

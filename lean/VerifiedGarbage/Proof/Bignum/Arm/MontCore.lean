module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCore
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Canonical Montgomery multiplication and its workspace frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem CsubCtx.congr {s t : State} {base : BitVec 32} {size out acc mod tmp n : Nat}
    (ctx : CsubCtx s base size out acc mod tmp n) (wr : t.wr = s.wr) :
    CsubCtx t base size out acc mod tmp n :=
  { ctx with sub := { ctx.sub with writable := by rw [wr]; exact ctx.sub.writable } }

theorem montCore_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (finish : CsubCtx s base size out acc mod tmp n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n 0 inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out)
    (hzero : val32 s.mem (State.addr base) acc (n + 2) = 0)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montCore s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) b n % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have hn := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fitsM := ctx.mFits
  have accM := ctx.accM
  have tmpM := ctx.tmpM
  have tmpFits := ctx.tmpFits
  have layout := ctx.layout
  rw [montCore, WP.seq_iff]
  refine WP.mono (montRounds_ok s ctx hdr ptr hzero hB hInv) ?_
  intro u loop
  have oldM := loop.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldOut := outs_word32 loop.outside (d := tmp + 24) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have outU : u.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out := by
    apply BitVec.eq_of_toNat_eq
    exact oldOut.trans (congrArg BitVec.toNat outPtr)
  refine WP.mono (montFinish_ok u (finish.congr loop.rest.wr) (by omega) tmpFits loop.ptr
    loop.hdr.count outU loop.hdr.accPtr loop.hdr.mPtr (by rw [oldM]; exact loop.bound)) ?_
  rintro t ⟨value, outside, keep⟩
  rw [oldM] at value
  refine ⟨?_, ?_, ?_, loop.rest.trans keep⟩
  · rw [value]; exact Nat.mod_lt _ (by omega)
  · rw [value, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    exact loop.value
  · exact (loop.outside.mono (by simp)).trans (outside.mono (by simp))

end VG.Proof.Bignum.Arm

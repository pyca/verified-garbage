module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Framework.Block

/-! One word of `b` or `m` times a row's scalar into the word in flight. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

/-- `macAt p k c x`: `r6 + 2³² c` becomes the word at `p + k` times `x`
plus `r6` and `c`; only `r3`, `r6` and `c` change. -/
theorem macAt_ok (s : State) {base : BitVec 32} {size o k : Nat} {p c x : Reg}
    (ws : Workspace s base size) (pp : s.gpr p = base + BitVec.ofNat 32 o)
    (fit : o + k + 4 ≤ size) (hk : k < 4096)
    (c6 : c ≠ .r6) (c3 : c ≠ .r3) (x3 : x ≠ .r3) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.macAt p k c x) s fun t =>
      (t.gpr .r6).toNat + 2^32 * (t.gpr c).toNat =
        w32 s.mem (State.addr base) (o + k) * (s.gpr x).toNat + (s.gpr .r6).toNat + (s.gpr c).toNat ∧
      t.mem = s.mem ∧ Rest [.r3, .r6, c] s t := by
  rw [VG.Impl.Bignum.Arm.Fios2.macAt, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (o + k)) hk (ws.ea pp (by omega)) (ws.read fit)
    fun u hu => WP.block_nil ?_
  refine WP.mono (Fios.umaal_ok u .r6 c .r3 x (Ne.symm c6)) ?_
  rintro t ⟨value, frame⟩
  rw [hu.gpr, hu.other x x3, hu.other .r6 (by decide), hu.other c c3] at value
  refine ⟨by simpa only [w32] using value, frame.mem.trans hu.mem, ?_⟩
  exact (hu.rest (by simp)).trans
    ⟨fun r hr => frame.regs r (by simp_all), frame.rd, frame.wr, frame.sp⟩

end VG.Proof.Bignum.Arm.Fios2

module
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The invariant of the runtime-length Montgomery loop -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure MontInv (s0 : State) (base : BitVec 32) (tmp a b mod acc n i : Nat) (inv : BitVec 32)
    (s : State) : Prop where
  index : i ≤ n
  hdr : RoundMeta s.mem base tmp a b mod acc n i inv
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp
  value : 2 ^ (32 * i) * val32 s.mem (State.addr base) acc (n + 2) % val32 s0.mem (State.addr base) mod n =
    val32 s0.mem (State.addr base) a i * val32 s0.mem (State.addr base) b n % val32 s0.mem (State.addr base) mod n
  bound : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s0.mem (State.addr base) mod n
  outside : Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8)] s0.mem s.mem
  rest : Rest roundClobbers s0 s

theorem montLoopBody_ok {s0 s : State} {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s0 base size tmp a b mod acc n) (h : MontInv s0 base tmp a b mod acc n i inv s)
    (hi : i < n)
    (hB : val32 s0.mem (State.addr base) b n < val32 s0.mem (State.addr base) mod n)
    (hInv : (val32 s0.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montRound s fun t => MontInv s0 base tmp a b mod acc n (i + 1) inv t ∧
      t.z = decide (i + 1 = n) := by
  have nowrap := ctx.workspace.nowrap
  have fa := ctx.aFits
  have fb := ctx.bFits
  have fm := ctx.mFits
  have aa := ctx.accA
  have ab := ctx.accB
  have am := ctx.accM
  have ta := ctx.tmpA
  have tb := ctx.tmpB
  have tm := ctx.tmpM
  have oldB := h.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldM := h.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldA := outs_word32 h.outside (d := a + 4 * i) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine WP.mono (montRound_ok s (ctx.congr h.rest.wr) h.hdr hi h.ptr
    (by rw [oldM]; exact h.bound) (by rw [oldB, oldM]; exact hB) (by rw [oldM]; exact hInv)) ?_
  intro t post
  obtain ⟨q, _, value⟩ := post.value
  rw [oldA, oldB, oldM] at value
  refine ⟨⟨by omega, post.hdr, post.ptr, ?_, ?_, h.outside.trans post.outside,
    h.rest.trans post.rest⟩, post.zero⟩
  · rw [pow32_succ, Nat.mul_comm (2 ^ 32) (2 ^ (32 * i)), val32_succ s0.mem (State.addr base) a i]
    exact round_step value h.value
  · simpa only [oldM] using post.bound

end VG.Proof.Bignum.Arm

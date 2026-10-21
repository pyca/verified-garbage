module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.MontState
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! A scanning-round law suffices for the existing complete Montgomery invariant. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- Replacement rounds may exploit the even native word count while preserving the round contract. -/
def RoundLaw (round : Prog isa) : Prop :=
  ∀ (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32},
    RoundCtx s base size tmp a b mod acc n → n % 2 = 0 →
    RoundMeta s.mem base tmp a b mod acc n i inv → i < n →
    s.gpr .r0 = base + BitVec.ofNat 32 tmp →
    val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n →
    val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n →
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0 →
    WP isa round s fun t => RoundPost s t base tmp a b mod acc n i inv

theorem loopBody_ok (round : Prog isa) (law : RoundLaw round) {s0 s : State} {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s0 base size tmp a b mod acc n) (even : n % 2 = 0) (h : MontInv s0 base tmp a b mod acc n i inv s)
    (hi : i < n)
    (hB : val32 s0.mem (State.addr base) b n < val32 s0.mem (State.addr base) mod n)
    (hInv : (val32 s0.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa round s fun t => MontInv s0 base tmp a b mod acc n (i + 1) inv t ∧
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
  refine WP.mono (law s (ctx.congr h.rest.wr) even h.hdr hi h.ptr
    (by rw [oldM]; exact h.bound) (by rw [oldB, oldM]; exact hB) (by rw [oldM]; exact hInv)) ?_
  intro t post
  obtain ⟨q, _, value⟩ := post.value
  rw [oldA, oldB, oldM] at value
  refine ⟨⟨by omega, post.hdr, post.ptr, ?_, ?_, h.outside.trans post.outside,
    h.rest.trans post.rest⟩, post.zero⟩
  · rw [pow32_succ, Nat.mul_comm (2 ^ 32) (2 ^ (32 * i)), val32_succ s0.mem (State.addr base) a i]
    exact round_step value h.value
  · simpa only [oldM] using post.bound


end VG.Proof.Bignum.Arm.MontPipeline

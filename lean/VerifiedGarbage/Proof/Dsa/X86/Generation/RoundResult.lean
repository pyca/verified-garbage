module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundInvoke
import VerifiedGarbage.Proof.Framework.Sig

/-! Recover the shared mathematical result and reusable workspace from a call. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86
open VG.Spec.Rsa.Mont (wOf numAt)

theorem round_post {s g t u : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (F : Frame [below (s.gpr .esp) 8] s.mem g.mem)
    (first : g.mem.readW ((g.gpr .esp).setWidth 64) 32 =
      s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic)
    (second : g.mem.readW ((g.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic))
    (upper : n ≤ 48) (width : wOf s.mem (off base Layout.arithmetic) = n)
    (value : numAt s.mem (off base Layout.arithmetic) n 0 = candidate)
    (memory : u.mem = t.mem) (result : u.gpr .eax = t.gpr .eax)
    (post : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).post
      (roundCallee g base) u) :
    (∀ b, numAt s.mem (off base Layout.arithmetic) n 5 = b % candidate * 2 ^ (64 * n) % candidate →
      (t.gpr .eax).toNat = if Spec.MillerRabin.round candidate b then 1 else 0) ∧
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem := by
  obtain ⟨a0, a1⟩ := round_callee_arguments room stack first second
  have pointer : (arg (roundCallee g base) 0).setWidth 64 = off base Layout.arithmetic := by
    rw [a0]
    exact scr.ea (by change 28672 < bytes; omega)
  have same := round_workspace_same room capacity stack F
  obtain ⟨_, _, wc⟩ := VG.Proof.MillerRabin.Workspace.workspace_congr same L P
  rw [width] at wc
  have numbers : ∀ j, j = 0 ∨ j = 5 →
      numAt (roundCallee g base).mem (off base Layout.arithmetic) n j =
        numAt s.mem (off base Layout.arithmetic) n j := by
    intro j hj
    apply VG.Proof.MillerRabin.Workspace.numAt_congr (len := 1536) same
    rcases hj with rfl | rfl <;>
      simp only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] <;> omega
  sig_post [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes] at post
  simp only [pointer, a1, memory, result] at post
  rw [BitVec.setWidth_append_eq_right] at post
  change ((∀ b, numAt (roundCallee g base).mem (off base Layout.arithmetic)
      (wOf (roundCallee g base).mem (off base Layout.arithmetic)) 5 =
      b % numAt (roundCallee g base).mem (off base Layout.arithmetic)
        (wOf (roundCallee g base).mem (off base Layout.arithmetic)) 0 *
        2 ^ (64 * wOf (roundCallee g base).mem (off base Layout.arithmetic)) %
        numAt (roundCallee g base).mem (off base Layout.arithmetic)
          (wOf (roundCallee g base).mem (off base Layout.arithmetic)) 0 →
      (t.gpr .eax).toNat = if Spec.MillerRabin.round
        (numAt (roundCallee g base).mem (off base Layout.arithmetic)
          (wOf (roundCallee g base).mem (off base Layout.arithmetic)) 0) b then 1 else 0) ∧
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536
      (wOf (roundCallee g base).mem (off base Layout.arithmetic)) (roundCallee g base).mem t.mem) at post
  rw [wc, numbers 0 (.inl rfl), numbers 5 (.inr rfl), value] at post
  refine ⟨post.1, ?_⟩
  intro i hi headers arrays table
  exact (post.2 i hi headers arrays table).trans (same i hi)

end VG.Proof.Dsa.X86.Generation

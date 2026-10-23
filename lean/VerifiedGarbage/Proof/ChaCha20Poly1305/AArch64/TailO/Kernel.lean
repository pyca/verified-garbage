module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Kernel
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Round
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20.Keystream
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase

/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting: the kernel

`TailO.kernel sve k`, as `Tail.kernel`: the keystream of the four blocks
from the stream's counter in the buffer `x3[0, 256)`, and the `c` blocks from
`W` (`x20`; `x6 = c`, at most `10 k`) absorbed into the accumulator in
`x21`–`x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds LoadSame input input_same input_eq)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_subImm)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (zero_ok Zeroed.byte Zeroed.frame block_eq)
open VG.Spec.ChaCha20 (innerBlock stateAt serialize block)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

theorem kernel_ok (sve : Bool) (k : Nat) {R a : Nat} {W : Addr} {c : Nat} {s : State} (hc : c < 2 ^ 63)
    (hx20 : s.gpr .x20 = W) (hx6 : s.gpr .x6 = BitVec.ofNat 64 c)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ d, d + 16 ≤ 256 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16)
    (hst : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩)
    (hr : Readable W (16 * c) s) (ha : Acc R a s) (hck : c ≤ 10 * k) :
    WP isa (TailO.kernel sve k) s fun u =>
      (∀ k < 256, u.mem (s.gpr .x3 + BitVec.ofNat 64 k) =
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x3, 256⟩] s.mem u.mem ∧
      Poly.hval u % Spec.Poly1305.P = absorbAll R a (bytesAt s.mem W (16 * c)) % Spec.Poly1305.P ∧
      (u.gpr .x23).toNat ≤ 4 ∧ u.gpr .x20 = W + BitVec.ofNat 64 (16 * c) ∧
      (∀ r, r ∉ [Reg.x1, .x4, .x6] → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  unfold TailO.kernel
  -- The four blocks' states.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.setup_ok s hin).mono
    fun s₃ ⟨h₂, l₂, t₂⟩ => ?_)
  -- The count.
  have m₂ : s₃.mem = s.mem := l₂.mem
  apply WP.seq
  apply WP.block_cons_iff.mpr
  refine ⟨s₃.write .x .x4 ((10 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide,
      ite_true]
  -- The loop, from its invariant.
  let s₄ := s₃.write .x .x4 ((10 : BitVec 16).setWidth 64)
  have m₃ : s₃.mem = s.mem := m₂
  let vs : Nat → CState := fun j => ctr (stateAt s.mem (s.gpr .x0)) j
  have h₄ : TI vs R a W c k s₄ s₄ 0 := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, ⟨by omega, ?_, ?_, ?_⟩, ?_⟩
    · intro k j hj
      rw [Stitch.write_v]
      exact h₂ k j hj
    · rw [Stitch.write_v, t₂]
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide), hx20, Nat.mul_zero, Nat.min_zero,
        Nat.mul_zero, BitVec.add_zero]
    · have e : bytesAt s₄.mem W (16 * min c (k * 0)) = [] := by simp [bytesAt]
      rw [e, Poly1305.absorbAll_nil]
      refine ha.of (fun r hr => ?_) m₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        (rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide)]; exact l₂.gpr _ (by decide))
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide), hx6]; simp
    · rw [RegUpd.gpr_write_self]; rfl
  have hr₄ : Readable W (16 * c) s₄ := hr.of (by show s₃.rd = _; rw [l₂.rd]) (by show s₃.wr = _; rw [l₂.wr])
    (by rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide)])
  refine WP.seq ((rounds_ok sve hc hr₄ h₄).mono fun s₅ h₅ => ?_)
  have x3₅ : s₅.gpr .x3 = s.gpr .x3 := by
    rw [h₅.keep _ (by decide) (by decide) (by decide), RegUpd.gpr_write_of_ne s₃ .x _ (by decide),
      l₂.gpr _ (by decide)]
  have wr₅ : s₅.wr = s.wr := by rw [h₅.wr]; show s₃.wr = _; rw [l₂.wr]
  have rd₅ : s₅.rd = s.rd := by rw [h₅.rd]; show s₃.rd = _; rw [l₂.rd]
  have sp₅ : s₅.sp = s.sp := by rw [h₅.sp]; show s₃.sp = _; rw [l₂.sp]
  have mm₅ : s₅.mem = s.mem := by rw [h₅.mem]; exact m₃
  -- The buffer zeroed, then the keystream XORed into it.
  rw [Tail.finish, List.append_assoc]
  apply WP.block_append
  refine (zero_ok x3₅ (by rw [wr₅]; exact hw)).mono fun s₆ ⟨g₆, rd₆, wr₆, sp₆, v₆, z₆⟩ => ?_
  let s₇ := s₆.write .x .x1 (s₆.gpr .x3)
  have hx₇ : exec (VG.Impl.ChaCha20.AArch64.Xor.mov .x1 .x3) s₆ = some s₇ := by
    show exec (.addImm .x .x1 .x3 0) s₆ = some s₇
    simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
      exec_addImm_x (s := s₆) (d := .x1) (n := .x3) (imm := 0) (by decide)
  refine WP.block_cons_iff.mpr ⟨s₇, hx₇, ?_⟩
  show WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.finish) s₇ _
  have u₇ := VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 s₆ .x1 (s₆.gpr .x3)
  have x1₇ : s₇.gpr .x1 = s.gpr .x3 := by rw [u₇.gpr, g₆, x3₅]
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 := by
    rw [u₇.other _ (by decide), g₆, h₅.keep _ (by decide) (by decide) (by decide),
      RegUpd.gpr_write_of_ne s₃ .x _ (by decide), l₂.gpr _ (by decide)]
  have f₆ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₇.mem := by
    rw [u₇.mem, ← mm₅]; exact z₆.frame
  have st₇ : stateAt s₇.mem (s.gpr .x0) = stateAt s.mem (s.gpr .x0) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hst
  have hv₇ : Holds (fun j => Nat.repeat innerBlock 10 (vs j)) s₇ := by
    intro k j hj
    rw [show s₇.v = s₆.v from rfl, v₆ _ (fun e => absurd e
      ((show ∀ k : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v28 by decide) k))]
    exact h₅.vec k j hj
  have hin₇ : ∀ k : Fin 16, InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [u₇.rd, u₇.wr, rd₆, wr₆, rd₅, wr₅, x0₇]; exact hin k
  unfold VG.Impl.ChaCha20.AArch64.Neon4.finish
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv₇ hin₇).mono
    fun s₈ ⟨h₈, l₈⟩ => ?_)
  have hc₈ : Holds (fun j => block (vs j)) s₈ := by
    intro k j hj
    rw [h₈ k j hj, input_eq, x0₇, st₇, block_eq]
  have ho : ∀ r j : Fin 4, InRegions s₈.wr
      (s₈.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j
    rw [l₈.wr, l₈.gpr _ (by decide), u₇.wr, wr₆, wr₅, x1₇]
    exact hw _ (by omega)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hc₈ ho).mono
    fun s₉ ⟨d₉, f₉, k₉⟩ => ?_
  have x1₈ : s₈.gpr .x1 = s.gpr .x3 := by rw [l₈.gpr _ (by decide), x1₇]
  have g₉ (r : Reg) (h4 : r ≠ .x4) : s₉.gpr r = s₇.gpr r := by rw [k₉.gpr, l₈.gpr _ h4]
  have g₅ (r : Reg) (h4 : r ≠ .x4) (h6 : r ≠ .x6) (hp : r ∉ Poly.regs) : s₅.gpr r = s₃.gpr r := by
    rw [h₅.keep _ h4 h6 hp, RegUpd.gpr_write_of_ne s₃ .x _ h4]
  have acc₅ := h₅.abs.acc
  have ptr₅ := h₅.abs.ptr
  rw [show min c (k * 10) = c by omega, show s₄.mem = s.mem from m₃] at acc₅
  rw [show min c (k * 10) = c by omega] at ptr₅
  have e21 : ∀ r ∈ [Reg.x21, .x22, .x23], s₉.gpr r = s₅.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, fun r hr hp => ?_, ?_, ?_, ?_⟩
  · have e := d₉ k hk
    have z : ∀ x : BitVec 8, (0 : BitVec 8) ^^^ x = x := fun x => by ext i; simp
    rw [x1₈, show s₈.mem = s₇.mem from l₈.mem, u₇.mem, z₆.byte hk, z] at e
    exact e
  · rw [← x1₈]
    have f₈ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₈.mem := by rw [l₈.mem]; exact f₆
    rw [x1₈] at f₉ ⊢
    exact f₈.trans f₉
  · rw [show Poly.hval s₉ = Poly.hval s₅ by
      simp only [Poly.hval, e21 .x21 (by simp), e21 .x22 (by simp), e21 .x23 (by simp)]]
    exact acc₅.h
  · rw [e21 .x23 (by simp)]; exact acc₅.h2
  · rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]; exact ptr₅
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h4, h6⟩ := hr
    rw [g₉ _ h4, u₇.other _ h1, g₆, g₅ _ h4 h6 hp, l₂.gpr _ h4]
  · rw [k₉.rd, l₈.rd, u₇.rd, rd₆, rd₅]
  · rw [k₉.wr, l₈.wr, u₇.wr, wr₆, wr₅]
  · rw [k₉.sp, l₈.sp, show s₇.sp = s₆.sp from rfl, sp₆, sp₅]

end VG.Proof.ChaCha20Poly1305.AArch64.TailO

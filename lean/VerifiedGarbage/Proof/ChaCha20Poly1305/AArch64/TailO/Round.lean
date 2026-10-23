module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Round
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase

/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting: the rounds

`TailO.rounds`: ten double rounds of the four-block kernel (`Tail.doubleRound_ok`),
and after each up to `k` of the `c` blocks from `W` (`TailO.maybes`, while
`x6`, the blocks left, is not zero): after `i` rounds, `min c (k i)` blocks
are absorbed. The rounds write only vector registers, the blocks only
`Poly.regs` and `x6`; neither writes memory.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState)
open VG.Impl.ChaCha20.AArch64.Neon4 (rol8Table)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds RoundSame)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable absorb_next)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- `n` of the `c` blocks from `W` absorbed, and `x6` the blocks left. -/
structure Absorbed (R a : Nat) (W : Addr) (c : Nat) (m : Mem) (s : State) (n : Nat) : Prop where
  le : n ≤ c
  ptr : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)
  acc : Acc R (absorbAll R a (bytesAt m W (16 * n))) s
  left : s.gpr .x6 = BitVec.ofNat 64 (c - n)

/-- `maybe`: a block if one is left. -/
theorem maybe_ok {R a : Nat} {W : Addr} {c n : Nat} (hc : c < 2 ^ 63) {s : State}
    (hr : Readable W (16 * c) s) (h : Absorbed R a W c s.mem s n) :
    WP isa TailO.maybe s fun u =>
      Absorbed R a W c s.mem u (min c (n + 1)) ∧ (∀ r, r ≠ .x6 → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ v, u.v v = s.v v) := by
  unfold TailO.maybe
  refine WP.ite (decide (c - n = 0)) (by
      rw [show isa.eval (.zero .x .x6) s = some (s.gpr .x6 == 0) from
        VG.Proof.ChaCha20.AArch64.Xor.eval_zero s .x6, h.left,
        VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = c := by have := of_decide_eq_true hz; have := h.le; omega
    subst hn
    refine WP.block_nil ?_
    rw [show min n (n + 1) = n by omega]
    exact ⟨h, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · have hlt : n < c := by have := of_decide_eq_false hz; have := h.le; omega
    have hv : ∀ i ∈ Poly.block, vdstOf i = none := by decide +kernel
    refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv
      (absorb_next (by omega) h.acc h.ptr hr)).mono fun b ⟨⟨hba, hbp, hbk⟩, hbv, hbsp, _, _⟩ => ?_)
    apply WP.block_cons_iff.mpr
    refine ⟨b.write .x .x6 (b.gpr .x6 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq] using
        exec_subImm_x (s := b) (d := .x6) (n := .x6) (imm := 1) (by decide)
    have hbm : b.mem = s.mem := hbk.2.1
    rw [show min c (n + 1) = n + 1 by omega]
    refine ⟨⟨by omega, ?_, ?_, ?_⟩, fun r h6 hp => ?_, hbm, hbk.2.2.1, hbk.2.2.2, hbsp, fun v => ?_⟩
    · rw [RegUpd.gpr_write_of_ne b .x _ (by decide), hbp]
    · exact hba.of (fun r hr' => RegUpd.gpr_write_of_ne b .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hbk.gpr' (r := .x6), h.left,
        Offset.ofNat_sub_ofNat (by omega : 1 ≤ c - n), Nat.sub_sub]
    · rw [RegUpd.gpr_write_of_ne b .x _ h6, hbk.gpr' (r := r) hp]
    · rw [Stitch.write_v, hbv]

/-- `maybes k`: up to `k` blocks. -/
theorem maybes_ok {R a : Nat} {W : Addr} {c : Nat} (hc : c < 2 ^ 63) :
    ∀ (k : Nat) {n : Nat} {s : State}, Readable W (16 * c) s → Absorbed R a W c s.mem s n →
    WP isa (TailO.maybes k) s fun u =>
      Absorbed R a W c s.mem u (min c (n + k)) ∧ (∀ r, r ≠ .x6 → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ v, u.v v = s.v v)
  | 0, n, s, _, h => WP.block_nil ⟨by rw [Nat.add_zero, Nat.min_eq_right h.le]; exact h,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | k + 1, n, s, hr, h => by
    unfold TailO.maybes
    refine WP.seq ((maybe_ok hc hr h).mono fun d ⟨hda, hdk, hdm, hdrd, hdwr, hdsp, hdv⟩ => ?_)
    have hdr : Readable W (16 * c) d := hr.of hdrd hdwr (hdk _ (by decide) (by decide))
    rw [← hdm] at hda
    refine (maybes_ok hc k hdr hda).mono fun f ⟨hfa, hfk, hfm, hfrd, hfwr, hfsp, hfv⟩ => ?_
    rw [hdm, show min c (min c (n + 1) + k) = min c (n + (k + 1)) by omega] at hfa
    exact ⟨hfa, fun r h6 hp => by rw [hfk r h6 hp, hdk r h6 hp], hfm.trans hdm, hfrd.trans hdrd,
      hfwr.trans hdwr, hfsp.trans hdsp, fun v => by rw [hfv, hdv]⟩

/-- After `i` iterations of the loop. -/
structure TI (vs : Nat → CState) (R a : Nat) (W : Addr) (c k : Nat) (s₀ s : State) (i : Nat) : Prop where
  vec : Holds (fun j => Nat.repeat innerBlock i (vs j)) s
  table : s.v .v30 = rol8Table
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ≠ .x4 → r ≠ .x6 → r ∉ Poly.regs → s.gpr r = s₀.gpr r
  abs : Absorbed R a W c s₀.mem s (min c (k * i))
  cnt : s.gpr .x4 = BitVec.ofNat 64 (10 - i)

/-- The loop body, from `TI … i` to `TI … (i + 1)`. -/
theorem iter_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {c k : Nat} {s₀ s : State}
    {i : Nat} (hc : c < 2 ^ 63) (hi : i < 10) (hr : Readable W (16 * c) s₀)
    (h : TI vs R a W c k s₀ s i) :
    WP isa (TailO.round sve k) s fun u => TI vs R a W c k s₀ u (i + 1) := by
  unfold TailO.round
  apply WP.seq
  refine (Tail.doubleRound_ok sve h.vec h.table).mono fun b ⟨hb, hsb⟩ => ?_
  have hbm : b.mem = s₀.mem := hsb.mem.trans h.mem
  have hbr : Readable W (16 * c) b := hr.of (by rw [hsb.rd, h.rd]) (by rw [hsb.wr, h.wr])
    (by rw [hsb.gpr, h.keep _ (by decide) (by decide) (by decide)])
  have hba : Absorbed R a W c b.mem b (min c (k * i)) := by
    rw [hbm]
    exact ⟨h.abs.le, by rw [hsb.gpr]; exact h.abs.ptr, h.abs.acc.of (fun r _ => by rw [hsb.gpr]) hsb.mem,
      by rw [hsb.gpr]; exact h.abs.left⟩
  apply WP.seq
  refine (maybes_ok hc k hbr hba).mono fun f ⟨hfa, hfk, hfm, hfrd, hfwr, hfsp, hfv⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨f.write .x .x4 (f.gpr .x4 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
  · simpa only [State.read, BitVec.setWidth_eq] using
      exec_subImm_x (s := f) (d := .x4) (n := .x4) (imm := 1) (by decide)
  have hm : min c (min c (k * i) + k) = min c (k * (i + 1)) := by
    rw [Nat.mul_succ]; omega
  have hfm' : f.mem = s₀.mem := hfm.trans hbm
  refine ⟨?_, ?_, hfm', hfrd.trans (hsb.rd.trans h.rd),
    hfwr.trans (hsb.wr.trans h.wr), hfsp.trans (hsb.sp.trans h.sp),
    fun r h4 h6 hp => ?_, ?_, ?_⟩
  · intro k j hj
    rw [Stitch.write_v, hfv]
    exact hb k j hj
  · rw [Stitch.write_v, hfv, hsb.v30, h.table]
  · rw [RegUpd.gpr_write_of_ne f .x _ h4, hfk r h6 hp, hsb.gpr]
    exact h.keep r h4 h6 hp
  · rw [← hm]
    rw [hbm] at hfa
    exact ⟨hfa.le, by rw [RegUpd.gpr_write_of_ne f .x _ (by decide)]; exact hfa.ptr,
      hfa.acc.of (fun r hr' => RegUpd.gpr_write_of_ne f .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl,
      by rw [RegUpd.gpr_write_of_ne f .x _ (by decide)]; exact hfa.left⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hfk _ (by decide) (by decide),
      hsb.gpr, h.cnt, Offset.ofNat_sub_ofNat (by omega : 1 ≤ 10 - i)]
    simp only [Nat.sub_sub]

/-- The loop: ten iterations. -/
theorem rounds_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {c k : Nat} {s₀ s : State}
    (hc : c < 2 ^ 63) (hr : Readable W (16 * c) s₀) (h : TI vs R a W c k s₀ s 0) :
    WP isa (TailO.rounds sve k) s fun u => TI vs R a W c k s₀ u 10 := by
  let Inv : Nat → State → Prop := fun n u => ∃ i, i < 10 ∧ n = 10 - i ∧ TI vs R a W c k s₀ u i
  have hstep : ∀ n u, Inv n u → WP isa (TailO.round sve k) u (fun w =>
      (eval (.nonzero .x .x4) w = some false ∧ TI vs R a W c k s₀ w 10) ∨
      (eval (.nonzero .x .x4) w = some true ∧ ∃ m < n, Inv m w)) := by
    rintro n u ⟨i, hi, rfl, hu⟩
    refine (iter_ok sve hc hi hr hu).mono fun w hw => ?_
    have he : eval (.nonzero .x .x4) w = some (BitVec.ofNat 64 (10 - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hw.cnt]
    by_cases hl : i + 1 = 10
    · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
    · have hn0 : BitVec.ofNat 64 (10 - (i + 1)) ≠ 0 := by
        intro hz
        have hz' := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 10 - (i + 1) < 2 ^ 64)] at hz'
        change 10 - (i + 1) = 0 at hz'
        omega
      exact .inr ⟨by rw [he]; simpa using hn0, 10 - (i + 1), by omega, i + 1, by omega, rfl, hw⟩
  exact WP.loop (M := isa) Inv hstep 10 s ⟨0, by decide, rfl, h⟩

end VG.Proof.ChaCha20Poly1305.AArch64.TailO

module

public import VerifiedGarbage.Proof.Ffdh.X86.Ladder
public import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Ladder
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
import VerifiedGarbage.Proof.Mont.X86.PowerInit
meta import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH on i686: the traces of a power of two

The ladder's runs over the same public count of bits leak the same traces
(`ladderPower_relCT`): each bit's index, `esi`, is public in the read of the
bit (`τAs`) because both runs hold the same count, and the bit itself only
becomes a mask of a select. The squares are the windowed power's.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Ladder

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Impl.Ffdh.X86
open VG.Proof.Ffdh.X86.Cached (bit_ok)

/-! ## The taint checks -/

theorem scalarBit_check :
    (VG.Taint.check taint τAs scalarBit (VG.Taint.hintOf taint τAs scalarBit)).isSome = true := by taint_decide

theorem double_check : XCheck (.seq (.block bitMask) (.seq (addMod .wide 7 6 6)
    (.seq (.block [.mov .ecx (.mem (sc winOff))]) (.seq (select (.slot .wide 7) (.slot .wide 6) (one .wide))
      (.block [.alu .test .esi (.reg .esi)]))))) := by
  dsimp only [XCheck]; taint_decide

theorem bitCount_check : ACheck (.block (bitCount 11)) := by dsimp only [ACheck]; taint_decide

theorem twoTest_check : ACheck twoTest := by dsimp only [ACheck]; taint_decide

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run of the ladder with `n` bits left: one (slot 3) and the accumulator (slot 6) below the modulus. -/
abbrev LSt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (n : Nat) (u : State) : Prop :=
  WSt Ex base bytes len args sp .wide [3, 6] 0 u ∧ u.gpr .esi = BitVec.ofNat 32 n

/-- A run through a change of registers. -/
theorem wst_regs {ks : List Nat} {E : Nat} {s t : State} (W : WSt Ex base bytes len args sp .wide ks E s)
    {rs : List Reg} (K : Keeps rs s t) (m : t.mem = s.mem) (di : .edi ∉ rs := by decide)
    (hsp : .esp ∉ rs := by decide) : WSt Ex base bytes len args sp .wide ks E t :=
  let ⟨M, C, Hk, He, A, e⟩ := W
  ⟨M, C.regs K m di hsp, fun j hj => by rw [sv, m]; exact Hk j hj, fun j hj => by rw [m]; exact He j hj,
    A.keep K hsp, (K.1 _ hsp).trans e⟩

/-- With the same bits left, the runs' bit indices are the same. -/
theorem lst_agreeS {n : Nat} {u₁ u₂ : State} (W₁ : LSt Ex base bytes len args sp n u₁)
    (W₂ : LSt Ex base bytes len args sp n u₂) : VG.X86.Taint.Agree τAs u₁ u₂ := by
  obtain ⟨⟨_, C₁, -, -, A₁, e₁⟩, i₁⟩ := W₁
  obtain ⟨⟨_, C₂, -, -, A₂, e₂⟩, i₂⟩ := W₂
  exact agreeAs C₁.inp C₂.inp A₁ A₂ (e₁.trans e₂.symm) (i₁.trans i₂.symm)

/-- A bit's step: the square is the windowed power's, the bit's index public in its read, and the rest
checked from the arguments. -/
theorem ladderStep_trace {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 32) :
    RelCT isa (Both (LSt Ex base bytes len args sp n)) ladderStep fun _ _ => True := by
  have hc := winChecks .wide
  unfold ladderStep
  refine VG.RelCT.seq (R := Both (LSt Ex base bytes len args sp n))
    (mul_wst_relCT (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hc.m666 (ks := [3, 6]) (ks' := [3, 6]) (E := 0) (by decide) (by decide) (by decide)
      (X := fun u => u.gpr .esi = BitVec.ofNat 32 n) (X' := fun u => u.gpr .esi = BitVec.ofNat 32 n)
      fun s u e K => by rw [K.1 _ (by decide)]; exact e) ?_
  refine VG.RelCT.seq (R := Both (LSt Ex base bytes len args sp (n - 1)))
    (taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ hc.dec fun x W =>
      wp_subS rfl fun u U _ => WP.block_nil ⟨wst_regs W.1 U.keeps U.mem, by
        rw [U.gpr, W.2]; exact VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0⟩) ?_
  refine VG.RelCT.seq (R := Both (LSt Ex base bytes len args sp (n - 1)))
    (relCT_both (VG.RelCT.taint (A := taint) τAs (fun _ _ h => lst_agreeS h.1 h.2) scalarBit_check) fun x W =>
      WP.mono (bit_ok W.1.run.1 (k := n - 1) (by omega_arith) W.2) fun u ⟨m, K, _⟩ =>
        ⟨wst_regs W.1 K m, by rw [K.1 _ (by decide)]; exact W.2⟩) ?_
  exact VG.RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.1.agree h.2.1) double_check

/-- A bit's step, with what each run reaches. -/
theorem ladderStep_relCT {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 32) :
    RelCT isa (Both (LSt Ex base bytes len args sp n)) ladderStep
      (Both fun u => LSt Ex base bytes len args sp (n - 1) u ∧ u.zf = some (decide (n = 1))) := by
  refine relCT_both (ladderStep_trace hn0 hn) fun x W => ?_
  obtain ⟨⟨M, C, Hk, -, A, e⟩, esi⟩ := W
  refine WP.mono (ladderStep_ok C (Hk 6 (by decide)) hn0 hn esi) fun u ⟨Cu, F, K, eu, zu, lt, _⟩ =>
    ⟨⟨⟨M, Cu, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans e⟩, eu⟩,
      zu⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [pw_one C.inp F C.inp.room]; exact Hk 3 (by decide)
  · exact lt

/-- The bits, from the count down to none. -/
theorem ladderLoop_relCT {N : Nat} (hN : 0 < N) (hN32 : N < 2 ^ 32) :
    RelCT isa (Both (LSt Ex base bytes len args sp N)) (.loop ladderStep .ne)
      (Both (LSt Ex base bytes len args sp 0)) := by
  refine (relCT_countLoop (I := fun j => LSt Ex base bytes len args sp (N - j)) hN fun j hj => ?_).mono
    (fun _ _ h => by simpa only [Nat.sub_zero] using h) (fun _ _ h => by simpa only [Nat.sub_self] using h)
  refine (ladderStep_relCT (n := N - j) (by omega_arith) (by omega_arith)).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
  have e : N - j - 1 = N - (j + 1) := by omega_arith
  have d : (N - j = 1) = (j + 1 = N) := propext (by omega_arith)
  rw [e] at W₁ W₂
  simp only [d] at z₁ z₂
  exact ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩

/-- The ladder's runs over the bits of the public length `L` in argument 11. -/
theorem ladderPower_relCT {L : Nat} (hx : args 11 = BitVec.ofNat 32 L) (hL0 : 0 < L) (hL : L ≤ 1024) :
    RelCT isa (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) ladderPower
      (Both (WSt Ex base bytes len args sp .wide [6] 0)) := by
  have hc := winChecks .wide
  unfold ladderPower
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m643 (ks := [3, 4]) (ks' := [3, 6]) (E := 0) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (R := Both (LSt Ex base bytes len args sp (8 * L)))
    (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ bitCount_check fun x W => ?_) ?_
  · obtain ⟨M, C, Hk, He, A, e⟩ := W
    unfold bitCount
    refine wp_movS (C.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ =>
      wp_addS rfl fun t₃ a₃ _ => wp_addS rfl fun t₄ a₄ _ => WP.block_nil ⟨?_, ?_⟩
    · exact wst_regs ⟨M, C, Hk, He, A, e⟩
        (((a₁.keeps.trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
          (a₄.keeps.mono (by decide)) : Keeps [.esi] x t₄) (by rw [a₄.mem, a₃.mem, a₂.mem, a₁.mem])
    · rw [a₄.gpr, a₃.gpr, a₂.gpr, a₁.gpr, hx, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
        BitVec.ofNat_add_ofNat]
      congr 1; omega_arith
  refine VG.RelCT.seq (ladderLoop_relCT (N := 8 * L) (by omega_arith) (by omega_arith)) ?_
  exact (mul_wst_relCT0 (o := 6) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m663 (ks := [3, 6]) (ks' := [6]) (E := 0) (by decide) (by decide) (by decide)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

/-- `ladderCall`, for synthetic argument 11 the public length `L`. -/
theorem ladderCall_relCT {L : Nat} (hx : args 11 = BitVec.ofNat 32 L) (hL0 : 0 < L) (hL : L ≤ 1024) :
    RelCT isa (Both (WinPre Ex base bytes len args sp)) ladderCall
      (Both (Run Ex base bytes len args sp)) := by
  refine relCT_both (argCall_trace (Pc := WSt (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) .wide [3, 4] 0)
    (fun _ W => ⟨W.1.1.run, W.1.2⟩) (fun s u W C Fs => ?_)
    ((ladderPower_relCT hx hL0 hL).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun x W => ?_
  · obtain ⟨M, Cn, Wn, one, r2, -⟩ := winPre_callee W C Fs
    exact ⟨Wn, _, ladderPower_ok Cn one r2 hx hL0 hL⟩
  · obtain ⟨⟨⟨M, C, -, -, A, e⟩, RF⟩, one, r2⟩ := W
    rw [← e] at RF
    exact WP.mono (ladderCall_ok C RF one (by rw [r2, C.mod]) hx hL0 hL) fun u ⟨Cu, _, K, _⟩ =>
      ⟨Cu.inp, A.keep K, (K.1 _ (by decide)).trans e⟩

end

end VG.Proof.Ffdh.X86.Ladder

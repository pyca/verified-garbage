module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA key generation on RISC-V: masking a sampled polynomial

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/Mask.lean`): after each sampler,
its result (0 or 1, the low word of `a0`, which `and24` zero-extends) is
ANDed into `s4`, and each coefficient of the polynomial it wrote with
`-a0`: the polynomial is kept if the sampler succeeded, and zeroed if it
failed (`mask_ok`), without a branch (`mask_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-- A coefficient masked with `-r`, for `r` 0 or 1. -/
theorem and_mask {r : BitVec 64} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    (x.setWidth 64 &&& (0 - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    simp only [BitVec.toNat_setWidth]; omega

/-! ## One coefficient -/

section
variable {s : State} {x c M : BitVec 64}

theorem maskBody_ok (h4 : s.gpr .a1 = x) (h5 : s.gpr .a2 = c) (h12 : s.gpr .t2 = M)
    (ir : InRegions (s.rd ++ s.wr) x 4) (ow : InRegions s.wr x 4) (al : x.toNat % 4 = 0) :
    WP isa (.block maskBody) s fun s' =>
      s'.gpr .a1 = x + 4 ∧ s'.gpr .a2 = c - 1 ∧ s'.gpr .t2 = M ∧
      s'.mem = s.mem.writeW x (((s.mem.readW x 32).setWidth 64 &&& M).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  mrun [maskBody, h4, h5, h12, ir, ow, al, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  exact ⟨rfl, rfl⟩

end

/-- After masking `k` coefficients of the polynomial at `P` with `M`. -/
structure MaskInv (P M : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  a1 : s.gpr .a1 = P + BitVec.ofNat 64 (4 * k)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (256 - k)
  t2 : s.gpr .t2 = M
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [reg P 1024] s₀.mem s.mem
  co : ∀ t < 256, coeffAt s.mem P t =
    if t < k then ((coeffAt s₀.mem P t).setWidth 64 &&& M).setWidth 32 else coeffAt s₀.mem P t

theorem mask_step {P M : Addr} {s₀ : State} (cw : Covers [reg P 1024] s₀.wr) (alP : P.toNat % 4 = 0)
    {k : Nat} (hk : k < 256) {s : State} (h : MaskInv P M s₀ k s) :
    WP isa (.block maskBody) s fun s' => MaskInv P M s₀ (k + 1) s' ∧ (s'.gpr .a2 != 0) = decide (k + 1 ≠ 256) := by
  have cP : (reg P 1024).Contains (P + BitVec.ofNat 64 (4 * k)) 4 := Offset.contains_base _ (by omega) (by omega)
  have ow : InRegions s.wr (P + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩
  have ir : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (4 * k)) 4 :=
    let ⟨r, hr, hc⟩ := ow; ⟨r, List.mem_append_right _ hr, hc⟩
  have al : (P + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine WP.mono (maskBody_ok h.a1 h.a2 h.t2 ir ow al)
    fun s' ⟨r4, r5, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, r12, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r4]; exact ptr_succ _ 4 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, coeffAt_writeW32 _ _ ht hk]
    by_cases e : k = t
    · subst e
      have := h.co k hk
      rw [ifn (Nat.lt_irrefl _)] at this
      rw [ifp rfl, ifp (Nat.lt_succ_self _), ← this]; rfl
    · rw [ifn e, h.co t ht]
      by_cases htk : t < k
      · rw [ifp htk, ifp (by omega)]
      · rw [ifn htk, ifn (by omega)]
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hk]; exact count_nz hk (by decide)

theorem mask_loop {P M : Addr} {s₀ : State} (cw : Covers [reg P 1024] s₀.wr) (alP : P.toNat % 4 = 0)
    (h4 : s₀.gpr .a1 = P) (h5 : s₀.gpr .a2 = BitVec.ofNat 64 256) (h12 : s₀.gpr .t2 = M) :
    WP isa (.loop (.block maskBody) (.nonzero .a2)) s₀ fun s =>
      Kept [reg P 1024] s₀ s ∧ ∀ t < 256, coeffAt s.mem P t = ((coeffAt s₀.mem P t).setWidth 64 &&& M).setWidth 32 :=
  wp_loop_nz (MaskInv P M s₀) (N := 256) (by decide) (fun k hk s h => mask_step cw alP hk h)
    (fun s h => ⟨⟨h.cs, h.sp, h.rd, h.wr, h.frame⟩, fun t ht => by rw [h.co t ht, ifp ht]⟩)
    ⟨by rw [h4]; simp, by rw [h5], h12, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t _ => by rw [ifn (Nat.not_lt_zero t)]⟩

/-! ## The polynomial -/

abbrev maskPre (a : Ptr) : List Instr :=
  ([.li .t2 0, .sub .t2 .t2 .a0] : List Instr) ++ Arg.instrs .a1 (.ptr a) ++ ([.li .a2 256] : List Instr)

theorem maskPre_ok {a : Ptr} (ha : argOk (.ptr a) = true) (s : State) :
    WP isa (.block (maskPre a)) s fun s' =>
      Only s s' ∧ s'.gpr .t2 = 0 - s.gpr .a0 ∧ s'.gpr .a1 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧
        s'.gpr .a2 = BitVec.ofNat 64 256 := by
  have hb := baseReg_of ha
  have ha2 : a.2 < 2 ^ 31 - 2048 := by simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at ha; exact ha.2
  have hn : a.1 ≠ .a1 ∧ a.1 ≠ .a2 ∧ a.1 ≠ .t2 := by
    simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h <;> rw [h] <;> decide
  rw [maskPre, WP.block_append_iff, WP.block_append_iff]
  refine Steps.WP.cons (exec_li (by decide)) (Steps.WP.cons exec_sub (WP.block_nil ?_))
  refine WP.mono (arg_ok .a1 ha (argOk_ne (by decide) ha) _) fun s1 e1 => ?_
  subst e1
  refine Steps.WP.cons (exec_li (by decide)) (WP.block_nil ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩)
  · have : r ≠ .t2 ∧ r ≠ .a1 ∧ r ≠ .a2 := by revert r; decide
    simp only [RegUpd.gpr_write, this.1, this.2.1, this.2.2, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofNat]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, argVal, hn.2.2]
  · simp only [RegUpd.gpr_write, ite_true, BitVec.ofInt_ofNat]

theorem mask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (aa : AlS a) (hw : ix a.1 ∈ Wb) (hr : s.gpr .a0 = 0 ∨ s.gpr .a0 = 1) :
    WP isa (mask a) s fun s' => Kept (L.RL [tri a 1024]) s s' ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .a0 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  have gb := hs.val pa.1
  simp only [argVal] at gb
  have cw := hs.cwE pa hw
  unfold mask
  refine WP.seq (WP.mono (maskPre_ok pa.1 s) fun s₁ ⟨o₁, g12, g4, g5⟩ => ?_)
  rw [gb] at g4
  refine WP.mono (mask_loop (by rw [o₁.wr]; exact cw) (hs.alS4 aa) g4 g5 g12) fun s' ⟨k, co⟩ => ⟨?_, fun t ht => ?_⟩
  · exact (o₁.kept _).trans k
  · rw [co t ht, o₁.mem, and_mask hr]

/-! ## Constant time -/

/-- The check is the same for every offset: its hint is computed once. -/
theorem mask_taint : ∀ j < 128, (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) (mask (sc (oP j)))
    (VG.Taint.hintOf VG.RISCV64.taint (Taint.ofRegs [.s11]) (mask (sc 0)))).isSome = true := by decide +kernel

theorem mask_tr {j : Nat} (hj : j < 128) {P : State → State → Prop} (hsp : ∀ x y, P x y → x.sp = y.sp)
    (h : ∀ x y, P x y → x.gpr .s11 = y.gpr .s11) : RelCT isa P (mask (sc (oP j))) fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs [.s11])
    (fun a b hab => ⟨hsp a b hab, fun r hr => by
      rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact h a b hab⟩) (mask_taint j hj)

end VG.Proof.MlDsa.RISCV64.KeyGen

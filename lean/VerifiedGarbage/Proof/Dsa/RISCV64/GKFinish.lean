module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKSampler
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: the exit

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Finish.lean`). `finish_ok`:
unless the status is 1, `out` is zeroed; the nonce is zeroed, the octets
consumed are written to `used`, the status returned and the registers
restored (`Fin`); after the frame is freed, that meets the contract
(`fin_post`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR sub1_beq zeroLoopA_ok preserved_cs bytes_frame)

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : GL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  have hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega)] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 32 + (x - L.F).toNat = (x - L.F).toNat - 32 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)] at hn
  omega

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  a0 : t.gpr .a0 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    R.key.getD (List.replicate (glOf s₀).ol 0)
  used : t.mem.readW (glOf s₀).used 64 = BitVec.ofNat 64 R.used
  cs : ∀ i < 12, t.gpr (cs i) = s₀.gpr (cs i)
  ra : t.gpr .ra = s₀.gpr .ra
  sp : t.sp = (glOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.GenerateKeyResult} (h : gkContract.pre s₀)
    (hc : Ctx (glOf s₀) s₀ t) (h5 : t.gpr .s5 = BitVec.ofNat 64 R.used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
      R.key.getD (List.replicate (glOf s₀).ol 0))
    (hnone : R.status ≠ 1 → R.key = none) :
    WP isa (finish outLen) t (Fin s₀ R) := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-1)]) [.a0] (Q := fun t₁ =>
    t₁.mem = t.mem ∧ t₁.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₁ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ => ?_)
  have hc₁ : Ctx (glOf s₀) s₀ t₁ := hc.step hL sp1 k1.2.1 k1.2.2
    (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (glOf s₀) s₀ t₂ → Keep [.a0, .t1, .t2, .t3, .t4, .t5] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (glOf s₀).out (glOf s₀).ol =
        R.key.getD (List.replicate (glOf s₀).ol 0) → P t₂) →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut outLen)) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [Steps.eval_zero, a0, h10, sub1_beq _ (by omega)])
      (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      obtain ⟨i64, l64⟩ := hc₁.word hL rfl (d := 64) (by decide) (by decide)
      have o64 := hc₁.out
      simp only [oOut] at o64
      have e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega) (by omega)
      have e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega) (by omega)
      refine WP.seq (WP.mono (wp_sp (WP.keep [.t3, .t4, .t5, .a0, .t2, .t1] (Q := fun t₂ => t₂.gpr .a0 = 0 ∧
        t₂.gpr .t4 = (glOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (glOf s₀).ol ∧ t₂.mem = t₁.mem)
        (by
          brun [outLen, lenP, lenQ, hc₁.sp, hc₁.s2, e1, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut, i64, l64,
            o64, exec_li_zero, ← BitVec.ofNat_add]
          simp only [GL.ol]; congr 1; omega) (by decide) (by rfl)))
        fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
      have ho : ∀ i < (glOf s₀).ol, InRegions t₂.wr (off (glOf s₀).out i) 1 := fun i hi =>
        ⟨(glOf s₀).outR, by rw [k2.2.2, hc₁.wr, hwr]; simp,
          VG.Offset.contains_base _ (by omega) (by have := hL.nwOut; simp only [GL.ol] at hi this ⊢; omega)⟩
      refine WP.mono (wp_sp (zeroLoopA_ok (by simp only [GL.ol]; omega) (by simp only [GL.ol]; omega) ho hL.nwOut
        b0 b4 b5))
        fun t₃ ⟨⟨⟨z3, o3⟩, k3⟩, sp3⟩ => ?_
      have k23 := k2.trans k3
      refine hP t₃ (hc₁.step hL (sp3.trans sp2) k23.2.1 k23.2.2
        (fun r hr => k23.1 r (by revert r hr; decide)) ?_) (k23.mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega)
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c5 : t₂.gpr .s5 = BitVec.ofNat 64 R.used := (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h5)
  have c10 : t₂.gpr .s10 = BitVec.ofNat 64 R.status :=
    (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h10)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)))
    fun t₃ ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  have hc₃ : Ctx (glOf s₀) s₀ t₃ := hc₂.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr (glOf s₀).used 8 := by
    rw [hc₃.wr, hwr]
    exact ⟨(glOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hal := hL.alU
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep (c := .block [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0])
    [.t4, .a0] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW (glOf s₀).used (BitVec.ofNat 64 R.used) ∧ t₄.gpr .a0 = BitVec.ofNat 64 R.status)
    (by
      brun [t0, oUsed, i72, l72, o72, BitVec.add_zero, (k3.1 _ (by decide)).trans c5,
        (k3.1 _ (by decide)).trans c10, hus, hal]) (by decide) (by rfl)))
    fun t₄ ⟨⟨⟨m4, a4⟩, k4⟩, sp4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (glOf s₀).usedR.Contains (glOf s₀).used 8 := Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (glOf s₀).F d) 64 = t₃.mem.readW (off (glOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (GL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hsw : SaveW t₄ (glOf s₀).F := fun i hi =>
    frame_word hL rfl (by rw [k4.2.2, hc₃.wr]) (by simp only [oSave, frameBytes]; omega)
      (by simp only [oSave]; omega)
  refine WP.mono (restoreRegs_ok t₄ (sp4.trans hc₃.sp) hsw (v := fun i => if i < 12 then s₀.gpr (cs i) else s₀.gpr .ra)
    (fun i hi => by rw [ite_eq_left hi]; exact (fw _ (by simp only [oSave, frameBytes]; omega)).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.ra)) fun t₅ ⟨r5, ra5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, fun i hi => by rw [r5 i hi, ite_eq_left hi], ra5, sp5.trans (sp4.trans hc₃.sp),
    rd5.trans (k4.2.1.trans hc₃.rd), wr5.trans (k4.2.2.trans hc₃.wr)⟩
  · rw [o5 .a0 (by decide) (by decide) (by decide)]; exact a4
  · rw [m5, m4, bytes_frame (rs := [(glOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by simp only [GL.ol]; omega)]
    rw [bytes_outside (o3.mono (by omega) (by simp only [oNonce, frameBytes]; omega)) hL.dFO
      (by simp only [GL.ol]; omega)]
    exact o2
  · rw [m5, m4, Mem.readW_writeW_self64]

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : gkContract.pre s₀) (hst : (gkRes s₀).status ≤ 2) (hf : Fin s₀ (gkRes s₀) t) :
    abiPreserved s₀ (freed frameBytes t) ∧ gkContract.post s₀ (freed frameBytes t) := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.ra⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨i, hi, rfl⟩ := preserved_cs r hr
    exact hf.cs i hi
  · simp only [freed, hf.sp, GL.F, glOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.a0, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [freed]
    have e0 : s₀.gpr .a0 = (glOf s₀).out := rfl
    have e1 : (s₀.gpr .a1).toNat = (glOf s₀).ol := hol
    rw [e0, e1]; exact hf.out
  · simp only [freed, Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) hf.used

end VG.Proof.Dsa.RISCV64.GK

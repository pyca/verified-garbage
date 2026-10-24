module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.DeriveCall
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Ctx
public import VerifiedGarbage.Spec.RsaPss

/-!
# DSA key generation on PPC64LE: the exit

`finish_ok`: unless the status is 1, `out` is zeroed; the nonce is zeroed,
the octets consumed are written to `used`, the status returned and the
registers restored (`Fin`); after the frame is freed, that meets the
contract (`fin_post`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

theorem ctx_r3 : ∀ r ∈ ctxRegs, r ∉ ([.r3] : List Reg) := by decide

theorem ctx_31 : ∀ r ∈ ctxRegs, r ∉ ([.r31] : List Reg) := by decide

theorem ctx_012 : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r12] : List Reg) := by decide

theorem ctx_z : ∀ r ∈ ctxRegs, r ∉ (([.r0, .r16, .r17] : List Reg) ++ ([.r16, .r17] : List Reg)) := by decide

theorem preserved_nv : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = nv i := by decide

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
  rw [show 2 ^ 64 - 120 + (x - L.F).toNat = (x - L.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)] at hn
  omega

/-- The length of the key, into `r17`. -/
abbrev olen : List Instr := [.add .r17 .r20 .r20, .add .r17 .r17 .r20, .add .r17 .r17 .r21, .add .r17 .r17 .r21]

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  r3 : t.gpr .r3 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol = R.key.getD (List.replicate (glOf s₀).ol 0)
  used : t.mem.readW (glOf s₀).used 64 = BitVec.ofNat 64 R.used
  nv : ∀ i < 18, t.gpr (nv i) = s₀.gpr (nv i)
  r2 : t.gpr .r2 = s₀.gpr .r2
  lr : t.lr = s₀.lr
  sp : t.sp = (glOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.GenerateKeyResult} (h : gkContract.pre s₀)
    (hc : Ctx (glOf s₀) s₀ t) (h25 : t.gpr .r25 = BitVec.ofNat 64 R.used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
      R.key.getD (List.replicate (glOf s₀).ol 0))
    (hnone : R.status ≠ 1 → R.key = none) :
    WP isa (finish olen) t (Fin s₀ R) := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (WP.keep (c := .block [.subi .r3 .r31 1]) [.r3] (Q := fun t₁ => t₁.mem = t.mem ∧
    t₁.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₁ ⟨⟨m1, a3⟩, k1⟩ => ?_)
  have hc₁ : Ctx (glOf s₀) s₀ t₁ := hc.step hL k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr))
    (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (glOf s₀) s₀ t₂ → Keep [.r0, .r3, .r16, .r17] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (glOf s₀).out (glOf s₀).ol =
        R.key.getD (List.replicate (glOf s₀).ol 0) → P t₂) →
      WP isa (.ite (.zero .d .r3) (.block []) (zeroOut olen)) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega)]) (fun hs => ?_)
      (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      refine WP.seq (WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t₂ => t₂.gpr .r0 = 0 ∧
        t₂.gpr .r16 = off (glOf s₀).out 0 ∧ t₂.gpr .r17 = BitVec.ofNat 64 (glOf s₀).ol ∧ t₂.mem = t₁.mem)
        (by prun [hc₁.r18, hc₁.r20, hc₁.r21, ← BitVec.ofNat_add]; exact ⟨rfl, by simp only [GL.ol]; congr 1; omega⟩)
        (by decide))
        fun t₂ ⟨⟨b0, b16, b17, m2⟩, k2⟩ => ?_)
      have ho : Scr t₂ (glOf s₀).out (glOf s₀).ol :=
        Scr.of_mem (by rw [k2.wr, hc₁.wr, hwr]; simp) hL.nwOut
      refine WP.mono (zeroLoop_ok (by simp only [GL.ol]; omega) (by simp only [GL.ol]; omega) ho b0 b16 b17)
        fun t₃ ⟨⟨z3, o3⟩, k3⟩ => ?_
      refine hP t₃ (hc₁.step hL (k2.trans k3).sp (k2.trans k3).rd (k2.trans k3).wr
        (fun r hr => (k2.trans k3).gpr r (ctx_z r hr)) ?_) ((k2.trans k3).mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega)
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c25 : t₂.gpr .r25 = BitVec.ofNat 64 R.used := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h25)
  have c31 : t₂.gpr .r31 = BitVec.ofNat 64 R.status := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h31)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)) fun t₃ ⟨⟨_, _, o3⟩, k3⟩ => ?_
  have hc₃ : Ctx (glOf s₀) s₀ t₃ := hc₂.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_012 r hr))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [hc₃.wr, hwr, BitVec.add_zero]
    exact ⟨(glOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hus' : InRegions t₃.wr (glOf s₀).used 8 := by rw [← BitVec.add_zero (glOf s₀).used]; exact hus
  refine WP.mono (WP.keep (c := .block [.store .d .r25 .r30 0, .addi .r3 .r31 0]) [.r3] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW ((glOf s₀).used + BitVec.ofNat 64 0) (BitVec.ofNat 64 R.used) ∧
      t₄.gpr .r3 = BitVec.ofNat 64 R.status)
    (by prun [hc₃.r30, (k3.gpr _ (by decide)).trans c25, (k3.gpr _ (by decide)).trans c31, hus, hus', add0]) (by decide))
    fun t₄ ⟨⟨m4, a3⟩, k4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (glOf s₀).usedR.Contains ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (glOf s₀).F d) 64 = t₃.mem.readW (off (glOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (GL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hin : ∀ i < 19, InRegions (t₄.rd ++ t₄.wr) (off (glOf s₀).F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k4.rd, k4.wr, hc₃.rd, hc₃.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains hL rfl (by simp only [oSave]; omega)
      (by simp only [oSave, frameBytes]; omega)⟩
  refine WP.mono (restoreRegs_ok t₄ (k4.sp.trans hc₃.sp) hin
    (fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega)).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.lr)) fun t₅ ⟨r5, l5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, r5, ?_, l5, sp5.trans (k4.sp.trans hc₃.sp), rd5.trans (k4.rd.trans hc₃.rd),
    wr5.trans (k4.wr.trans hc₃.wr)⟩
  · rw [o5 .r3 (by decide) (by decide) (by decide)]; exact a3
  · rw [m5, m4, RS.bytes_frame (rs := [(glOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by simp only [GL.ol]; omega)]
    rw [bytes_outside (o3.mono (by omega) (by simp only [oNonce, frameBytes]; omega)) hL.dFO
      (by simp only [GL.ol]; omega)]
    exact o2
  · rw [m5, m4, BitVec.add_zero, Mem.readW_writeW_self64]
  · rw [o5 .r2 (by decide) (by decide) (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact hc₂.r2

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : gkContract.pre s₀) (hst : (gkRes s₀).status ≤ 2) (hf : Fin s₀ (gkRes s₀) t) :
    abiPreserved s₀ (freed frameBytes t) ∧ gkContract.post s₀ (freed frameBytes t) := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.lr⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    rcases preserved_nv r hr with rfl | ⟨i, hi, rfl⟩
    · exact hf.r2
    · exact hf.nv i hi
  · simp only [freed, hf.sp, GL.F, glOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.r3, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · simp only [freed]
    have e3 : s₀.gpr .r3 = (glOf s₀).out := rfl
    have e4 : (s₀.gpr .r4).toNat = (glOf s₀).ol := hol
    rw [e3, e4]; exact hf.out
  · simp only [freed, Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) hf.used

end VG.Proof.Dsa.PPC64LE.GK

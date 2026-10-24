module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Hash
import VerifiedGarbage.Proof.MlKem.PPC64LE.CmpSel
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Hash
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA verification on PPC64LE: `c̃′ = c̃`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Cmp.lean`): `r24 ← 0` unless
`c̃′ = c̃`, without a branch (`cmp_piece`), by ML-KEM's loop comparing two
buffers (`Proof/MlKem/PPC64LE/CmpSel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk arg_ok
  argOk_ne baseReg_of base_pres)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (Ptr Arg)
open VG.Impl.MlKem.PPC64LE (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (hr : ∀ r ∈ [Reg.r28, .r29, .r30, .r31], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s48, by rw [hsp]; exact h.spk,
    by rw [hr _ (by decide)]; exact h.r31, by rw [hr _ (by decide)]; exact h.r30,
    by rw [hr _ (by decide)]; exact h.r29, by rw [hr _ (by decide)]; exact h.r28,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ preserved, r ≠ .r24 → r ≠ .r26 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide) (by decide) (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .r24 ∧ r ≠ .r26 := ⟨fun e => by subst e; simp [savedTop] at hs,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr r hp this.1 this.2]; exact h.pres r hp hs,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu, by rw [hm]; exact h.sg⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) {n : Nat} (hn : n < 2 ^ 31)
    (s : State) :
    WP isa (.block (Arg.instrs .r3 (.ptr a) ++ Arg.instrs .r4 (.ptr b) ++ Arg.instrs .r26 (.imm n) ++
      ([.li .r12 0] : List Instr))) s fun s' =>
      s'.gpr .r3 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧ s'.gpr .r4 = s.gpr b.1 + BitVec.ofNat 64 b.2 ∧
      s'.gpr .r26 = BitVec.ofNat 64 n ∧ s'.gpr .r12 = 0 ∧ (∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have pa := base_pres (baseReg_of ha)
  have pb := base_pres (baseReg_of hb)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok .r3 ha (argOk_ne (by decide) ha) s) fun s1 e1 => ?_
  refine WP.mono (arg_ok .r4 hb (argOk_ne (by decide) hb) s1) fun s2 e2 => ?_
  refine WP.mono (arg_ok .r26 (a := .imm n) (by simp only [argOk, decide_eq_true_eq]; exact hn)
    (fun _ e => by cases e) s2) fun s3 e3 => ?_
  subst e1 e2 e3
  prun []
  have nb3 : b.1 ≠ .r3 := fun e => by rw [e] at pb; simp [preserved] at pb
  refine ⟨rfl, by simp only [KeyGen.argVal, RegUpd.gpr_write_of_ne _ _ nb3], rfl, rfl, fun r hr hs => ?_, trivial⟩
  simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr]

theorem shr63_eq : ∀ n < 256, (BitVec.ofNat 64 n - 1) >>> 63 = if n = 0 then (1 : BitVec 64) else 0 := by
  decide +kernel

theorem shr63_of {v : BitVec 64} (h : v.toNat < 256) : (v - 1) >>> 63 = if v = 0 then (1 : BitVec 64) else 0 := by
  have hv := shr63_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
  rw [hv]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.subi .r12 .r12 1, .lsr .d .r12 .r12 63, .logic .and .r24 .r24 .r12]) s
      fun s' => s'.gpr .r24 = s.gpr .r24 &&& ((s.gpr .r12 - 1) >>> 63) ∧
        (∀ r ∈ preserved, r ≠ .r24 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  prun []
  refine ⟨rfl, fun r hr hs => ?_, trivial⟩
  simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr]

/-- `r24 ← r24 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 31) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .r24 = s.gpr .r24 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ preserved, r ≠ .r24 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have cr : Covers [⟨lpa L a, n⟩, ⟨lpa L b, n⟩] (s.rd ++ s.wr) :=
    Covers.cons (hs.crE pa) (Covers.cons (hs.crE pb) Covers.nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (cmpPre_ok pa.1 pb.1 hn' s) fun s₁ ⟨g3, g4, g26, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (baseReg_of pa.1)] at g3
  rw [hs.base (baseReg_of pb.1)] at g4
  refine WP.seq (wp_loop_nz (CmpInv (lpa L a) (lpa L b) n s₁) (N := n) hn
      (fun k hk s h => cmp_step (by omega) (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g3]; simp [lpa, Lay.A], by rw [g4]; simp [lpa, Lay.A], by rw [g26, Nat.sub_zero], fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl, by rw [g12]; decide,
      by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (cmpPost_ok s₂) fun s' ⟨r24, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr h24 h26 => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e24 : s₂.gpr .r24 = s.gpr .r24 := (h.cs .r24 (by decide) (by decide)).trans (cs .r24 (by decide) (by decide))
    rw [r24, shr63_of h.lt, e24]
    congr 1
    have key : s₂.gpr .r12 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by
          rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .r12 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr h24]
    exact (h.cs r hr h26).trans (cs r hr h26)

/-! ## After the comparison -/

/-- At the end of `compute`: `r24` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .r24 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.r28, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.r28, 0) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega) (by omega))
    fun s' ⟨r24, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.r28, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r24, e0, e4, hk5.r24]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.PPC64LE.taint.check
    (Taint.ofRegs [.r28, .r29, .r30, .r31]) (cmpAnd (sc oCT) (.r28, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.r28, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.PPC64LE.Verify

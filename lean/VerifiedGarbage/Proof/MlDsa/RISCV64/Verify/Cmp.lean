module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Hash
import VerifiedGarbage.Proof.MlKem.RISCV64.CmpSel
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Hash
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-!
# ML-DSA verification on RISC-V: `c̃′ = c̃`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Verify/Cmp.lean`): `r24 ← 0` unless
`c̃′ = c̃`, without a branch (`cmp_piece`), by ML-KEM's loop comparing two
buffers (`Proof/MlKem/RISCV64/CmpSel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk arg_ok
  argOk_ne baseReg_of base_pres)
open VG.Impl.MlDsa.RISCV64.Verify
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg)
open VG.Impl.MlKem.RISCV64 (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (hr : ∀ r ∈ [Reg.s8, .s9, .s10, .s11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s1168, by rw [hsp]; exact h.spk,
    by rw [hsp]; exact h.al, h.al0,
    by rw [hr _ (by decide)]; exact h.s11, by rw [hr _ (by decide)]; exact h.s10,
    by rw [hr _ (by decide)]; exact h.s9, by rw [hr _ (by decide)]; exact h.s8,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide) (by decide) (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .s4 ∧ r ≠ .s6 := ⟨fun e => by subst e; simp [savedTop] at hs,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr r hp this.1 this.2]; exact h.pres r hp hs,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu, by rw [hm]; exact h.sg⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) {n : Nat} (hn : n < 2 ^ 31 - 2048)
    (s : State) :
    WP isa (.block (Arg.instrs .a0 (.ptr a) ++ Arg.instrs .a1 (.ptr b) ++ Arg.instrs .s6 (.imm n) ++
      ([.li .t2 0] : List Instr))) s fun s' =>
      s'.gpr .a0 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧ s'.gpr .a1 = s.gpr b.1 + BitVec.ofNat 64 b.2 ∧
      s'.gpr .s6 = BitVec.ofNat 64 n ∧ s'.gpr .t2 = 0 ∧ (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have pa := base_pres (baseReg_of ha)
  have pb := base_pres (baseReg_of hb)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok .a0 ha (argOk_ne (by decide) ha) s) fun s1 e1 => ?_
  refine WP.mono (arg_ok .a1 hb (argOk_ne (by decide) hb) s1) fun s2 e2 => ?_
  refine WP.mono (arg_ok .s6 (a := .imm n) (by simp only [argOk, decide_eq_true_eq]; exact hn)
    (fun _ e => by cases e) s2) fun s3 e3 => ?_
  subst e1 e2 e3
  mrun []
  have nb3 : b.1 ≠ .a0 := fun e => by rw [e] at pb; simp [preserved] at pb
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       have h2 : r ≠ .a1 := fun e => by subst e; simp [preserved] at hr
       have h3 : r ≠ .a0 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, h2, h3, hs, ite_false])
    | simp only [KeyGen.argVal, nb3, ite_false]

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
    WP isa (.block [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .logic .and .s4 .s4 .t2]) s
      fun s' => s'.gpr .s4 = s.gpr .s4 &&& ((s.gpr .t2 - 1) >>> 63) ∧
        (∀ r ∈ preserved, r ≠ .s4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  mrun []
  and_intros
  all_goals first
    | rfl
    | trivial
    | (intro r hr hs
       have h1 : r ≠ .t2 := fun e => by subst e; simp [preserved] at hr
       simp only [h1, hs, ite_false])

/-- `s4 ← s4 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 31 - 2048) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .s4 = s.gpr .s4 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ preserved, r ≠ .s4 → r ≠ .s6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
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
  · have e24 : s₂.gpr .s4 = s.gpr .s4 := (h.cs .s4 (by decide) (by decide)).trans (cs .s4 (by decide) (by decide))
    rw [r24, shr63_of h.lt, e24]
    congr 1
    have key : s₂.gpr .t2 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by
          rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .t2 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr h24]
    exact (h.cs r hr h26).trans (cs r hr h26)

/-! ## After the comparison -/

/-- At the end of `compute`: `s4` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .s4 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.s8, 0) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega) (by omega))
    fun s' ⟨r24, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.s8, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r24, e0, e4, hk5.s4]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.RISCV64.taint.check
    (Taint.ofRegs [.s8, .s9, .s10, .s11]) (cmpAnd (sc oCT) (.s8, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.s8, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.RISCV64.Verify

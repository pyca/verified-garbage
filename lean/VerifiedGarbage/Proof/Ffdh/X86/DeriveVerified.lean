module

public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Ffdh.X86.Entry
meta import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
meta import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
meta import VerifiedGarbage.Proof.Ffdh.X86.Ops
meta import VerifiedGarbage.Impl.Ffdh.X86.Derive
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.Power
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import Mathlib.Logic.Function.Basic
meta import Mathlib.Tactic.Set
meta import Mathlib.Tactic.SplitIfs

/-! ### `Ffdh.X86.DeriveCT`, which only this module used -/

section

/-! ### `Ffdh.X86.DeriveTop`, which only this module used -/

section

/-! ### `Ffdh.X86.Derive`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_derive_public` on i686: the public value

`front_ok`: ZF tells whether x is an invalid scalar, as for
`vg_ffdh_check_private`. `tail_ok`: `y = g^x mod P` over x's `xl` bytes, its
range as the acceptance, y (zeros unless accepted) written and `3 − 2 flag`
returned. `body_ok`: for a valid domain, the status is `keyStatus`, since a
power of the checked generator is in its subgroup (`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes argNum_comp)
open VG.Proof.Ffdh.X86.CheckPublic (bytes_keep)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv loadX_ok boundTest_ok scalar_iff params powTop_ok)
open VG.Proof.Ffdh.X86.KeyGen (OutAt export_ok copy19_ok statusOf_ok comp_lt)
open VG.Impl.Ffdh.X86

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen xl : Nat}
  {args : Nat → BitVec 32}

/-- The body up to its branch on the scalar. -/
abbrev dFront : List (Prog isa) :=
  [pSetup, load (.slot .wide 10) (one .wide) 4 5, load (.slot .wide 13) (one .wide) 10 11,
    CheckPrivate.bound, CheckPrivate.scalarMask, testMask]

theorem body_eq : DerivePublic.body = Prog.chain dFront (.ite .e DerivePublic.fail DerivePublic.tail) := rfl

/-- p, g, x and one into slots 9, 10, 13 and 14, `pm1 p` into 15, and ZF telling whether x is an invalid
scalar. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (X : XGeo args base bytes len xl s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) :
    WP isa (Prog.chain dFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = false) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 10 = comp s.mem args len 1 ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have xf := X.fit
  have xle := X.le
  have h2 : 2 * len ≤ dlen := by omega_using [dl]
  have hpa := comp_p s.mem args h2
  have hqa : (params s.mem args len dlen).q = if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega_using [lw])
    · have : ¬ 3 * len = 2 * len := by omega_using [lw]
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  generalize hX : xv s.mem args xl = x
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_using [dl, fit])
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_using [dl]) (by omega_using [fit])
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_using [dl]))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g and x.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega_using [dl])
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega_using [dl]), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  have S₁₂ := S₁.trans S₂
  refine WP.seq (WP.mono (loadX_ok S₂.inp (X.keep ⟨rfl, rfl⟩ S₁₂.keeps)) fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  rw [show xv u₂.mem args xl = x by rw [xv, bytes_keep h X.apart (by omega_using [xf]) hx40 S₁₂.frame]; exact hX] at V₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot S₂.inp (by decide) O₃ K₃
  have k₃ := kept_slot S₂.inp (a := 13) O₃
  have S₁₃ := S₁₂.trans S₃
  have v9 : sv u₃.mem base len .wide 9 = p := by rw [k₃.slot_eq, k₂.slot_eq, V9]
  have v10 : sv u₃.mem base len .wide 10 = g := by rw [k₃.slot_eq, V₂]
  have v14 : sv u₃.mem base len .wide 14 = 1 := by rw [k₃.slot_eq, k₂.slot_eq, V14]
  have v15 : sv u₃.mem base len .wide 15 = pm1 len p := by rw [k₃.slot_eq, k₂.slot_eq, V15]
  -- The bound and the scalar's test.
  refine WP.mono (boundTest_ok S₃.inp (G.keep ⟨rfl, rfl⟩ S₁₃.keeps) v15 V₃ v9
    (fun n2 => comp_keep h G hb40 S₁₃.frame (by omega_using [dl, n2]))) fun u ⟨S₄, k₄, z, _⟩ => ?_
  have kk : ∀ {j}, 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [16, 17] →
      sv u.mem base len .wide j = sv u₃.mem base len .wide j := fun hj => k₄.slot_eq hj
  refine ⟨S₁₃.trans S₄, Gate.of_eval z (scalar_iff hpa.symm hqa), ?_, ?_, ?_, ?_⟩
  · rw [kk (by decide), v9]
  · rw [kk (by decide), v10]
  · rw [kk (by decide), v14]
  · rw [kk (by decide), v15]

/-- Zeros written for y, and 2 returned. -/
theorem fail_ok (h : In Ex base bytes len args s) (O : OutAt args base bytes len 0 (s.gpr .esp) s.wr)
    (h1 : args 1 = BitVec.ofNat 32 len) :
    WP isa DerivePublic.fail s fun t =>
      t.gpr .eax = BitVec.ofNat 32 2 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = List.replicate len 0 ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold DerivePublic.fail
  refine WP.seq (show WP isa (.block ([.mov .ecx (.imm 0)] ++ [.store (sc accOff) .ecx])) s _ from
    WP.block_append (wp_movS rfl fun u a _ => WP.block_nil ?_))
  have hu : In Ex base bytes len args u := h.regs a.keeps a.mem
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega_using [ao, nb]) a.gpr) fun v ⟨I, Ov, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega_using [ao]) Ov K)
  have hm : v.mem.readW (off base accOff) 32 = cmask false := BitVec.eq_of_toNat_eq W
  refine WP.seq (WP.mono (export_ok I (p := 0) (l := 1) (by decide) (by decide) h1
    (by rw [S.esp]; exact O.keep rfl S.keeps) hm rfl (fun e => nomatch e)) fun w ⟨B, _, F, Kw, _⟩ => ?_)
  refine WP.mono ret_ok fun t ⟨E, M, Kt⟩ => ⟨E, ?_, ?_, (S.keeps.trans Kw).trans (Kt.mono (by decide))⟩
  · rw [M, B]; exact VG.Proof.Bignum.i2osp_zero' _
  · rw [M]; rw [S.esp] at F
    exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans F

/-- The acceptance of y: its range. -/
abbrev accept (len p y : Nat) : Bool := decide (y < pm1 len p) && decide (1 < y)

/-- The tail: y over x's `xl` bytes, its range as the acceptance, y written (zeros unless accepted), and
`3 − 2 flag`. -/
theorem tail_ok (h : In Ex base bytes len args s) (X : XGeo args base bytes len xl s.rd s.wr)
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96))
    (O : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (h1 : args 1 = BitVec.ofNat 32 len)
    {p g x P : Nat} (h9 : sv s.mem base len .wide 9 = p) (hP : safeM p = P) (h10 : sv s.mem base len .wide 10 = g)
    (hx : xv s.mem args xl = x) (h14 : sv s.mem base len .wide 14 = 1)
    (h15 : sv s.mem base len .wide 15 = pm1 len p) (Plt : P < 2 ^ (8 * len)) (Ppos : 0 < P) :
    WP isa DerivePublic.tail s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (if accept len p (g ^ x % P) then 1 else 3) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if accept len p (g ^ x % P) then g ^ x % P else 0) len ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have ao : accOff = 8 := rfl
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  have ylt : g ^ x % P < 2 ^ (8 * len) := Nat.lt_trans (Nat.mod_lt _ Ppos) Plt
  unfold DerivePublic.tail
  -- y.
  refine WP.seq (WP.mono (powTop_ok h X hx40 (b := 10) (by decide) (by decide) (P := P) (by rw [h9, hP]))
    fun u₁ ⟨C₁, Y₁, _, F₁, k₁, K₁⟩ => ?_)
  rw [h10, hx] at Y₁
  have S₁ : Step Ex base bytes len args s u₁ := Step.ops h F₁ K₁
  -- Its range as the acceptance mask.
  refine WP.seq (WP.mono (rangeMask_ok S₁.inp (a := 6) (by decide)) fun u₂ ⟨I₂, e₂, O₂, K₂⟩ => ?_)
  rw [Y₁, k₁.slot_eq, h15, k₁.slot_eq, h14] at e₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.word S₁.inp (by decide) O₂ K₂
  have k₂ := kept_word S₁.inp (d := maskOff) (by decide) (by decide) O₂
  refine WP.seq (WP.mono (storeMask_ok I₂ (d := accOff) (by omega_using [ao, nb]) e₂) fun u₃ ⟨_, O₃, W₃, _, K₃⟩ => ?_)
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word I₂ (by omega_using [ao]) O₃ K₃
  have k₃ := kept_word I₂ (d := accOff) (by omega_using [ao, nb]) (by decide) O₃
  -- y into slot 19, and written.
  refine WP.seq (WP.mono (copy19_ok S₃.inp (a := 6) (by decide)) fun u₄ ⟨S₄, V₄, k₄⟩ => ?_)
  have bl := h.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e6 := lo_wide len 6
  have bw := bc_eq_cwc len .wide
  have f6 := slot_fit1 I₂ (j := 6) (by decide)
  rw [cb1] at f6
  rw [show sv u₃.mem base len .wide 6 = sv u₁.mem base len .wide 6 by
    rw [sv, sv, Outside.val32 O₃ (.inr (by omega_using [ao, nb, e6])) (by omega_using [bl, bw, f6]), Outside.val32 O₂ (.inr (by omega_using [mo, nb, e6])) (by omega_using [bl, bw, f6])],
    Y₁] at V₄
  have hm : u₄.mem.readW (off base accOff) 32 = cmask (accept len p (g ^ x % P)) :=
    BitVec.eq_of_toNat_eq ((k₄.word_eq (d := accOff)).trans W₃)
  have Sall := ((S₁.trans S₂).trans S₃).trans S₄
  refine WP.seq (WP.mono (export_ok S₄.inp (p := 0) (l := 1) (by decide) (by decide) h1
    (by rw [Sall.esp]; exact O.keep rfl Sall.keeps) hm V₄ (fun _ => ylt)) fun u₅ ⟨B, A, F, K, _⟩ => ?_)
  refine WP.mono (statusOf_ok A) fun t ⟨E, M, Kt⟩ => ⟨E, by rw [M]; exact B, ?_,
    (Sall.keeps.trans K).trans (Kt.mono (by decide))⟩
  rw [M]; rw [Sall.esp] at F
  exact (Sall.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans F

/-- What the contract asks of the status and the output, for a valid domain. -/
def DerivePost (len dlen xl : Nat) (m : Mem) (args : Nat → BitVec 32) (r : Nat) (m' : Mem) : Prop :=
  Spec.Ffdh.domainValid len (domBytes m args dlen) = true →
    let a := params m args len dlen
    let x := xv m args xl
    r = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) len
      else Spec.Rsa.bytesAt m' (byteAddr (args 0)) len = List.replicate len 0

theorem body_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (X : XGeo args base bytes len xl s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96))
    (O : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (h1 : args 1 = BitVec.ofNat 32 len) :
    WP isa DerivePublic.body s fun t => ∃ r, t.gpr .eax = BitVec.ofNat 32 r ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ DerivePost len dlen xl s.mem args r t.mem := by
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega_using [dl]
  have hpa := comp_p s.mem args h2
  have hga := comp_g s.mem args h2
  rw [body_eq]
  refine WP.chain_split (front_ok h G X hb40 hx40) fun u ⟨S, Gt, V9, V10, V14, V15⟩ => ?_
  have Ou : OutAt args base bytes len 0 (u.gpr .esp) u.wr := by rw [S.esp]; exact O.keep rfl S.keeps
  have FF : ∀ {t : State}, Frame (⟨byteAddr (args 0), len⟩ :: frameR base (u.gpr .esp) (fR len)) u.mem t.mem →
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem := fun {t} Ft => by
    rw [S.esp] at Ft
    exact (S.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans Ft
  have pvOf : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true →
      Spec.Ffdh.parametersValid (params s.mem args len dlen) = true := fun e => by
    unfold Spec.Ffdh.domainValid at e
    simp only [Bool.and_eq_true] at e
    exact e.1
  refine WP.gate Gt (fun inval => WP.mono (fail_ok S.inp Ou h1) fun t ⟨E, B, Ft, Kt⟩ =>
    ⟨2, E, FF Ft, S.keeps.trans Kt, fun e => ?_⟩) (fun val => ?_)
  · have ks : Spec.Ffdh.keyStatus (params s.mem args len dlen) (xv s.mem args xl) = 2 := by
      unfold Spec.Ffdh.keyStatus; rw [inval]; rfl
    refine ⟨ks.symm, ?_⟩
    simp only [ks]
    exact B
  · have Plt : safeM (comp s.mem args len 0) < 2 ^ (8 * len) := by
      unfold safeM
      split
      · exact comp_lt s.mem 0
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ 8 * len by omega_using [lw])
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega_arith
    have Xu := X.keep ⟨rfl, rfl⟩ S.keeps
    have xf := X.fit
    refine WP.mono (tail_ok (x := xv s.mem args xl) S.inp Xu (by rw [S.esp]; exact hx40) Ou h1 V9 rfl V10
      (by rw [xv, bytes_keep h X.apart (by omega_using [xf]) hx40 S.frame]) V14 V15 Plt
      (Nat.lt_trans Nat.zero_lt_one (safeM_gt _))) fun t ⟨E, B, Ft, Kt⟩ =>
      ⟨_, E, FF Ft, S.keeps.trans Kt, fun e => ?_⟩
    dsimp only
    have mv := VG.Proof.Ffdh.domainValid_mod e
    rw [← comp_p s.mem args h2] at mv
    unfold Spec.Rsa.modulusValid at mv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
    have p1 : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega_using [mv]
    have sP : safeM (comp s.mem args len 0) = comp s.mem args len 0 := safeM_of p1 mv.1.1.1
    have pv : Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = true := by
      cases c : Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl)
      · exact absurd c val
      · rfl
    rw [sP] at E B ⊢
    rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq (pvOf e), pv, VG.Proof.Bignum.powMod_eq]
    have pw := VG.Proof.Ffdh.publicValid_power (pvOf e) (xv s.mem args xl)
    rw [show (params s.mem args len dlen).g = comp s.mem args len 1 from hga.symm,
      show (params s.mem args len dlen).p = comp s.mem args len 0 from hpa.symm] at pw ⊢
    simp only [Bool.true_eq_false, ↓reduceIte]
    generalize xv s.mem args xl = x at E B pw ⊢
    generalize comp s.mem args len 1 ^ x % comp s.mem args len 0 = y at E B pw ⊢
    have ai : accept len (comp s.mem args len 0) y = true ↔ (1 < y ∧ y < comp s.mem args len 0 - 1) := by
      simp only [accept, pm1_of (show 0 < comp s.mem args len 0 by omega_using [mv]), Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
    by_cases hc : accept len (comp s.mem args len 0) y = true
    · rw [hc] at E B ⊢
      rw [pw.mpr (ai.mp hc)]
      simp only [↓reduceIte] at E B ⊢
      exact ⟨trivial, B⟩
    · have hc' : accept len (comp s.mem args len 0) y = false := by simpa using hc
      have hv : Spec.Ffdh.publicValid ⟨params s.mem args len dlen, y⟩ = false := by
        cases c : Spec.Ffdh.publicValid ⟨params s.mem args len dlen, y⟩
        · rfl
        · exact absurd (ai.mpr (pw.mp c)) hc
      rw [hc'] at E B ⊢
      rw [hv]
      simp only [Bool.false_eq_true, ↓reduceIte] at E B ⊢
      exact ⟨trivial, by rw [B]; exact VG.Proof.Bignum.i2osp_zero' _⟩

end VG.Proof.Ffdh.X86.Derive

end

end

/-! # `vg_ffdh_derive_public` on i686 against its contract: the public value -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)
open VG.Proof.Ffdh.X86.KeyGen (OutAt)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

/-- What the contract gives `vg_ffdh_derive_public(y, y_len, domain, domain_len, p_len, x, x_len, scratch,
scratch_len)`. -/
structure DerivePublicABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩,
    ⟨argAddr s 0, 36⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  domScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  xScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outX : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  scratchArgs : (⟨argumentPointer s 7, (arg s 8).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  belowOut : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  domBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  xBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratchBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 4).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 4).toNat (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 4).toNat
  xPos : 1 ≤ (arg s 6).toNat
  xLen : (arg s 6).toNat ≤ (arg s 4).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 4).toNat ≤ (arg s 8).toNat

theorem derivePublicABI_of {s : State} (h : (Spec.Ffdh.derivePublicContract abi stack).pre s) :
    DerivePublicABI s := by
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem wrapABI {s : State} (A : DerivePublicABI s) : WrapABI Impl.Ffdh.X86.DerivePublic.args 9 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h),
    (fun _ h => by cases h; decide), by decide, (fun _ h => by cases h)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega_using [this]
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.DerivePublic.args)) Impl.Ffdh.X86.DerivePublic.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The domain's and x's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat
abbrev entryX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat

/-- The output. -/
abbrev outR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩

/-- What the body may read: the domain and x; and write: y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat ∧ InRegions wr (argumentPointer s 0) (arg s 1).toNat

/-- The inputs and the output, as the synthetic arguments give them. -/
structure Geo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen xl : Nat) (sp : BitVec 32)
    (rd wr : List Region) : Prop where
  dom : DomGeo args base bytes len dlen rd wr
  dom40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  x : XGeo args base bytes len xl rd wr
  x40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  out : OutAt args base bytes len 0 sp wr
  e1 : args 1 = BitVec.ofNat 32 len

theorem frame_geo {s : State} (A : DerivePublicABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    Geo (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (wsBase Impl.Ffdh.X86.DerivePublic.args s)
      (wsSize Impl.Ffdh.X86.DerivePublic.args s) (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (arg s 3).toNat
      (arg s 6).toNat sp rd wr := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, low, st'])
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega_using [fb, low, st'])
  have sub40 : Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [low, st']), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  have subF : Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.DerivePublic.args s := A.outLen
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, (A.belowDom.sub_left sub40).symm,
    ⟨(ofn _).symm, A.xPos, A.xLen, A.xBound, hrd.2.1, A.xScratch⟩, (A.belowX.sub_left sub40).symm,
    ⟨?_, ?_, ?_, ?_, ?_⟩, (ofn _).symm⟩
  · show (arg s 0).toNat + _ ≤ _
    rw [← oR]; exact A.outBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← oR]; exact hrd.2.2
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.outScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.belowOut.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← oR]; exact (A.belowOut.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : DerivePublicABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- What the contract asks of the status and the output. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Ffdh.domainValid (arg s 4).toNat (entryDom s) = true →
    let a := Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)
    let x := Spec.Rsa.os2ip (entryX s)
    r.toNat = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 4).toNat =
          Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg s 4).toNat
      else Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 4).toNat = List.replicate (arg s 4).toNat 0

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : DerivePublicABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s)
      (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.DerivePublic.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([outR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.DerivePublic.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.DerivePublic.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  have Gm := frame_geo A espf I.extra
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.DerivePublic.args s := A.outLen
  have D : CheckDomain.domBytes f.mem (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (arg s 3).toNat =
      entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  have Xv : xv f.mem (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (arg s 6).toNat = Spec.Rsa.os2ip (entryX s) :=
    congrArg _ (frame_keep A Ft A.xScratch A.belowX (by have := A.xBound; omega_using []))
  refine WP.mono (body_ok I Gm.dom Gm.x Gm.dom40 Gm.x40 Gm.out Gm.e1) fun t ⟨r, E, F, K, P⟩ => ⟨fun v => ?_, ?_, K⟩
  · have P' := P (by rw [D]; exact v)
    simp only [CheckPrivate.params] at P'
    rw [D, Xv] at P'
    obtain ⟨hr, hb⟩ := P'
    refine ⟨?_, hb⟩
    rw [E, BitVec.toNat_ofNat, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (KeyGen.keyStatus_le _ _) (by decide))
  · rw [List.singleton_append, outR, oR]; exact F

theorem operation_ok {s : State} (A : DerivePublicABI s) :
    WP isa Impl.Ffdh.X86.DerivePublic.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [outR s])
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retOut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.outScratch.symm)
    (P := fun m e => spec s m e) (hP := fun m m' e F h => by
      obtain hb := VG.Proof.Rsa.rsa_bytes_frame F (src := argumentPointer s 0) (k := (arg s 4).toNat)
        (by have := (arg s 4).isLt; omega_arith) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr; rw [← A.outLen]; exact A.belowOut.symm)
      simpa only [spec, hb] using h)
    fun f I espf Ft => frame_ok A f I espf Ft

theorem correct (s : State) (h : (Spec.Ffdh.derivePublicContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.DerivePublic.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.derivePublicContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (derivePublicABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro v
  exact V v

end VG.Proof.Ffdh.X86.Derive

end

end

/-!
# `vg_ffdh_derive_public` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status: runs with the same ones
leak the same traces. The one branch on x, whether it is an invalid scalar,
is whether the status is 2; the rest, x's power over its public `x_len`
bytes (`CheckPrivate.powTop_trace`) and the masked output, has no branch on
it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv RX RG loadX_ok)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem loads_check : ACheck (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 13) (one .wide) 10 11] (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem fail_check : ACheck Impl.Ffdh.X86.DerivePublic.fail := by dsimp only [ACheck]; taint_decide
theorem rest_check : ACheck (.seq (Impl.Ffdh.X86.rangeMask 6) <| .seq (.block [.store (sc accOff) .ecx]) <|
    .seq (copy (.slot .wide 6) (.slot .wide 19) (one .wide)) <| .seq (Impl.Ffdh.X86.exportTo 0 1)
      (.block [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)])) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.DerivePublic.args))
      (.block [])).isSome = true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen xl : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

/-- A run of the body, with the domain `D` and the status `St`. -/
structure DAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen xl : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : DomGeo args base bytes len dlen u.rd u.wr
  hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  x : XGeo args base bytes len xl u.rd u.wr
  hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  dom : domBytes u.mem args dlen = D
  st : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf len D) (xv u.mem args xl) = St

theorem loads_rg {x : State} (A : DAt Ex base bytes len dlen xl args sp D St x) :
    WP isa (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
      load (.slot .wide 13) (one .wide) 10 11] (.block [])) x (RG Ex base bytes len dlen args sp) := by
  have h := A.run.1
  have G := A.geo
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_using [dl, fit])
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_using [dl]) (by omega_using [fit])
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_using [dl]))))
    fun u₁ ⟨I₁, F₁, _, _, _, _, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args x u₁ := ⟨I₁, F₁, K₁⟩
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega_using [dl])
    (by decide)) fun u₂ ⟨_, O₂, K₂⟩ => ?_)
  have S₂ := S₁.trans (Step.slot I₁ (by decide) O₂ K₂)
  refine WP.seq (WP.mono (loadX_ok S₂.inp (A.x.keep ⟨rfl, rfl⟩ S₂.keeps)) fun u₃ ⟨_, O₃, K₃⟩ => WP.block_nil ?_)
  have S₃ := S₂.trans (Step.slot S₂.inp (by decide) O₃ K₃)
  exact ⟨run_step A.run S₃, G.keep ⟨rfl, rfl⟩ S₃.keeps⟩

theorem front_trace :
    RelCT isa (Both (DAt Ex base bytes len dlen xl args sp D St)) (Prog.chain dFront (.block []))
      fun _ _ => True := by
  show RelCT isa _ (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 13) (one .wide) 10 11]
    (.seq Impl.Ffdh.X86.CheckPrivate.bound
      (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, Impl.Ffdh.X86.testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (fun _ A => A.run) loads_check fun _ A => loads_rg A) ?_
  exact VG.RelCT.seq CheckPrivate.bound_relCT (aEnd (fun _ h => h) CheckPrivate.mask_check)

/-- The tail: x's power over its `xl` bytes, then the mask, the output and the status by the taint
analysis. -/
theorem tail_trace {P : State → Prop}
    (hP : ∀ x, P x → RX Ex base bytes len xl args sp x ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)) :
    RelCT isa (Both P) Impl.Ffdh.X86.DerivePublic.tail fun _ _ => True := by
  by_cases hx : (args 11 = BitVec.ofNat 32 xl ∧ 0 < xl ∧ xl ≤ 1024) ∧
    Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  swap
  · refine VG.RelCT.of_false fun s₁ _ h => hx ?_
    obtain ⟨⟨R, X⟩, d⟩ := hP _ h.1
    exact ⟨⟨X.e11, X.pos, by have := X.le; have := R.1.upper'; omega_arith⟩, d⟩
  unfold Impl.Ffdh.X86.DerivePublic.tail
  exact VG.RelCT.seq ((CheckPrivate.powTop_trace hx.1 hx.2).mono (fun _ _ h => ⟨(hP _ h.1).1, (hP _ h.2).1⟩)
    fun _ _ h => h) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) rest_check)

theorem body_relCT :
    RelCT isa (Both (DAt Ex base bytes len dlen xl args sp D St)) Impl.Ffdh.X86.DerivePublic.body
      fun _ _ => True := by
  rw [body_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both
    (F := fun u => (RX Ex base bytes len xl args sp u ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)) ∧
      Gate u (St = 2)) front_trace fun x A => ?_) ?_
  · refine WP.mono (front_ok A.run.1 A.geo A.x (by rw [A.run.2.2]; exact A.hb40) (by rw [A.run.2.2]; exact A.hx40))
      fun u ⟨S, G, _⟩ => ⟨⟨⟨run_step A.run S, A.x.keep ⟨rfl, rfl⟩ S.keeps⟩, A.hx40⟩, G.congr ?_⟩
    rw [← A.st, KeyGen.keyStatus_two, CheckPrivate.params, A.dom]
  · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1.1) fail_check) (tail_trace fun _ h => h.1.1)

end

/-! ## Against the contract -/

/-- The status at entry. -/
abbrev entryStatus (s : State) : Nat :=
  Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)) (Spec.Rsa.os2ip (entryX s))

theorem pub_facts {s t : State} (H : (Spec.Ffdh.derivePublicContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 9, arg s i = arg t i) ∧ entryDom s = entryDom t ∧
      entryStatus s = entryStatus t := by
  sig_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a3])
  refine ⟨SP, fun i hi => ?_, inj L₁, List.cons.inj L₂ |>.1⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [hi])
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) :
    Rd s (rd ++ wr) [x, outR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, _⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.contains_self _ _⟩⟩

/-- The narrowed state the body runs from, the output writable: a run with the domain and the status at
entry. -/
theorem dAt_of {s f : State} (A : DerivePublicABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.DerivePublic.args s f) :
    DAt (Rd s) (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s)
      (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (arg s 3).toNat (arg s 6).toNat
      (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s)
      (entryStatus s)
      (narrowed (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s) f
        [outR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩
  have Gm := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  refine ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [outR s]) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact A.belowOut.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide)), Bf.2.1⟩,
    Gm.dom, Gm.dom40, Gm.x, Gm.x40, ?_, ?_⟩
  · exact frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  · show Spec.Ffdh.keyStatus _ (Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 5) _)) = _
    rw [frame_keep A Bf.2.2.2.2 A.xScratch A.belowX (by have := A.xBound; omega_using [])]
    rfl

theorem constantTime : ConstantTime isa (Spec.Ffdh.derivePublicContract abi stack).pre
    (Spec.Ffdh.derivePublicContract abi stack).pub Impl.Ffdh.X86.DerivePublic.code := by
  intro s t tr ur sf tf S T H E F
  have A := derivePublicABI_of S
  have B := derivePublicABI_of T
  obtain ⟨SP, args, dom, st⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.DerivePublic.args s = wsBase Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 7).setWidth 64 = (arg t 7).setWidth 64
    rw [args 7 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.DerivePublic.args s = wsSize Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 8).toNat * 8 = (arg t 8).toNat * 8
    rw [args 8 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.DerivePublic.args s = pLenOf Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 4).toNat = (arg t 4).toNat
    rw [args 4 (by decide)]
  have hsy : synth Impl.Ffdh.X86.DerivePublic.args (arg t) = synth Impl.Ffdh.X86.DerivePublic.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hout : outR t = outR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 5 (by decide),
      args 6 (by decide)]
  have hl3 : (arg t 3).toNat = (arg s 3).toNat := by rw [args 3 (by decide)]
  have hl6 : (arg t 6).toNat = (arg s 6).toNat := by rw [args 6 (by decide)]
  have hx : ∀ {x : State}, DerivePublicABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : DerivePublicABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.DerivePublic.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.DerivePublic.body
        (narrowed (wsBase Impl.Ffdh.X86.DerivePublic.args x) (wsSize Impl.Ffdh.X86.DerivePublic.args x) f
          [outR x]) F := fun {x f} X Bf => by
    have Gm := frame_geo X (sp := x.gpr .esp - BitVec.ofNat 32 argsFrame) rfl
      (narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.DerivePublic.args x, wsSize Impl.Ffdh.X86.DerivePublic.args x⟩)
    have D := dAt_of X Bf
    exact ⟨_, body_ok D.run.1 D.geo D.x (by rw [D.run.2.2]; exact D.hb40) (by rw [D.run.2.2]; exact D.hx40)
      (by rw [D.run.2.2]; exact Gm.out) Gm.e1⟩
  have ho : ∀ {x f : State}, DerivePublicABI x → BodyAt (Rd x) Impl.Ffdh.X86.DerivePublic.args x f →
      outR x ∈ f.wr :=
    fun X Bf => by rw [Bf.2.2.2.1, X.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [outR s]) hws hwz (fun f Bf => hw A Bf) (fun g Bg => by rw [← hout]; exact hw B Bg)
      (fun f g Bf Bg => ⟨dAt_of A Bf, ?_⟩) body_relCT
      (fun f Bf r hr => by rw [List.mem_singleton.mp hr]; exact ho A Bf)
      (fun g Bg r hr => by rw [List.mem_singleton.mp hr, ← hout]; exact ho B Bg)) E F
  have D₂ := dAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl3, hl6, ← SP, ← dom, ← st, hout] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.Derive

end

end

/-! # `vg_ffdh_derive_public` on i686 against its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86

/-- An output of 64 bytes, a domain of 128, `p_len` 64, x of one byte and a working space of 1056 words,
apart. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 0x10
    else if a = 0x20008 then 64
    else if a = 0x2000d then 0x20
    else if a = 0x20010 then 128
    else if a = 0x20014 then 64
    else if a = 0x20019 then 0x40
    else if a = 0x2001c then 1
    else if a = 0x20021 then 0x90
    else if a = 0x20024 then 0x20
    else if a = 0x20025 then 4 else 0
  rd := [⟨8192, 128⟩, ⟨16384, 1⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 36⟩]

theorem satisfiable : ∃ s, (Spec.Ffdh.derivePublicContract abi stack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 128 := by decide
  have a4 : arg satState 4 = 64 := by decide
  have a5 : arg satState 5 = 16384 := by decide
  have a6 : arg satState 6 = 1 := by decide
  have a7 : arg satState 7 = 36864 := by decide
  have a8 : arg satState 8 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes,
    stackBelow, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp, satState, Spec.Rsa.scratchWords] using satState

theorem verified : Verified target Impl.Ffdh.X86.DerivePublic.code (Spec.Ffdh.derivePublicContract abi stack) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Derive

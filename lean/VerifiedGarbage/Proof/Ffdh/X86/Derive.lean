module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.X86.Checks

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
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40)) :
    WP isa (Prog.chain dFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = false) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 10 = comp s.mem args len 1 ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have xf := X.fit
  have xle := X.le
  have h2 : 2 * len ≤ dlen := by omega
  have hpa := comp_p s.mem args h2
  have hqa : (params s.mem args len dlen).q = if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega)
    · have : ¬ 3 * len = 2 * len := by omega
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  generalize hX : xv s.mem args xl = x
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g and x.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  have S₁₂ := S₁.trans S₂
  refine WP.seq (WP.mono (loadX_ok S₂.inp (X.keep ⟨rfl, rfl⟩ S₁₂.keeps)) fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  rw [show xv u₂.mem args xl = x by rw [xv, bytes_keep h X.apart (by omega) hx40 S₁₂.frame]; exact hX] at V₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot S₂.inp (by decide) O₃ K₃
  have k₃ := kept_slot S₂.inp (a := 13) O₃
  have S₁₃ := S₁₂.trans S₃
  have v9 : sv u₃.mem base len .wide 9 = p := by rw [k₃.slot_eq, k₂.slot_eq, V9]
  have v10 : sv u₃.mem base len .wide 10 = g := by rw [k₃.slot_eq, V₂]
  have v14 : sv u₃.mem base len .wide 14 = 1 := by rw [k₃.slot_eq, k₂.slot_eq, V14]
  have v15 : sv u₃.mem base len .wide 15 = pm1 len p := by rw [k₃.slot_eq, k₂.slot_eq, V15]
  -- The bound and the scalar's test.
  refine WP.mono (boundTest_ok S₃.inp (G.keep ⟨rfl, rfl⟩ S₁₃.keeps) v15 V₃ v9
    (fun n2 => comp_keep h G hb40 S₁₃.frame (by omega))) fun u ⟨S₄, k₄, z, _⟩ => ?_
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
  refine WP.mono (storeMask_ok hu (d := accOff) (c := false) (by omega) a.gpr) fun v ⟨I, Ov, W, _, K⟩ => ?_
  have S : Step Ex base bytes len args s v := (Step.regs h a.mem a.keeps).trans (Step.word hu (by omega) Ov K)
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
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40))
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
  refine WP.seq (WP.mono (storeMask_ok I₂ (d := accOff) (by omega) e₂) fun u₃ ⟨_, O₃, W₃, _, K₃⟩ => ?_)
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word I₂ (by omega) O₃ K₃
  have k₃ := kept_word I₂ (d := accOff) (by omega) (by decide) O₃
  -- y into slot 19, and written.
  refine WP.seq (WP.mono (copy19_ok S₃.inp (a := 6) (by decide)) fun u₄ ⟨S₄, V₄, k₄⟩ => ?_)
  have bl := h.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e6 := lo_wide len 6
  have bw := bc_eq_cwc len .wide
  have f6 := slot_fit1 I₂ (j := 6) (by decide)
  rw [cb1] at f6
  rw [show sv u₃.mem base len .wide 6 = sv u₁.mem base len .wide 6 by
    rw [sv, sv, Outside.val32 O₃ (.inr (by omega)) (by omega), Outside.val32 O₂ (.inr (by omega)) (by omega)],
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
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40))
    (O : OutAt args base bytes len 0 (s.gpr .esp) s.wr) (h1 : args 1 = BitVec.ofNat 32 len) :
    WP isa DerivePublic.body s fun t => ∃ r, t.gpr .eax = BitVec.ofNat 32 r ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ DerivePost len dlen xl s.mem args r t.mem := by
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega
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
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ 8 * len by omega)
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega
    have Xu := X.keep ⟨rfl, rfl⟩ S.keeps
    have xf := X.fit
    refine WP.mono (tail_ok (x := xv s.mem args xl) S.inp Xu (by rw [S.esp]; exact hx40) Ou h1 V9 rfl V10
      (by rw [xv, bytes_keep h X.apart (by omega) hx40 S.frame]) V14 V15 Plt
      (Nat.lt_trans Nat.zero_lt_one (safeM_gt _))) fun t ⟨E, B, Ft, Kt⟩ =>
      ⟨_, E, FF Ft, S.keeps.trans Kt, fun e => ?_⟩
    dsimp only
    have mv := VG.Proof.Ffdh.domainValid_mod e
    rw [← comp_p s.mem args h2] at mv
    unfold Spec.Rsa.modulusValid at mv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
    have p1 : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega
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
      simp only [accept, pm1_of (show 0 < comp s.mem args len 0 by omega), Bool.and_eq_true, decide_eq_true_eq]
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

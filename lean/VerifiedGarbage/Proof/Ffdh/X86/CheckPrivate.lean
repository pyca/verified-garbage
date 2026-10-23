module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublic
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Framework.RelCTChain
public import VerifiedGarbage.Spec.Ffdh

/-!
# `vg_ffdh_check_private` on i686: the checks

`front_ok`: ZF tells whether x is an invalid scalar (`privateValid`, for
any domain: below q, or without q below `p − 1`, which for a p of zero is
also below p). `body_ok`: for a valid domain, the status is
`privateStatus`: 2 for an invalid scalar, else 1 exactly when
`1 < y < p − 1` and `g^x mod p = y`; a power of the checked generator is in
its subgroup (`publicValid_power`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPrivate

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes argNum_comp)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv loadY_ok bytes_keep)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen xl : Nat}
  {args : Nat → BitVec 32}

/-- x, of `xl` bytes at synthetic argument 10, with its length at 11. -/
structure XGeo (args : Nat → BitVec 32) (base : Addr) (bytes len xl : Nat) (rd wr : List Region) : Prop where
  e11 : args 11 = BitVec.ofNat 32 xl
  pos : 0 < xl
  le : xl ≤ len
  fit : (args 10).toNat + xl ≤ 2 ^ 32
  rd : InRegions (rd ++ wr) (byteAddr (args 10)) xl
  apart : Region.Disjoint ⟨byteAddr (args 10), xl⟩ ⟨base, bytes⟩

theorem XGeo.keep {rd wr : List Region} (X : XGeo args base bytes len xl rd wr) {s t : State} {rs : List Reg}
    (e : s.rd = rd ∧ s.wr = wr) (K : Keeps rs s t) : XGeo args base bytes len xl t.rd t.wr := by
  rw [K.2.1, K.2.2, e.1, e.2]; exact X

/-- x's value. -/
abbrev xv (m : Mem) (args : Nat → BitVec 32) (xl : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 10)) xl)

/-- x into the wide slot 13. -/
theorem loadX_ok (h : In Ex base bytes len args s) (X : XGeo args base bytes len xl s.rd s.wr) :
    WP isa (load (.slot .wide 13) (one .wide) 10 11) s fun u =>
      sv u.mem base len .wide 13 = xv s.mem args xl ∧
      Outside base (lo len (.slot .wide 13)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have lb := len_le_bc len
  have := X.le
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := 13) (by decide)) (p := 10) (l := 11) (L := xl)
    (by decide) (by decide) X.e11 X.pos (by rw [cb1]; omega) X.fit X.rd X.apart)
    fun u ⟨V, O, K⟩ => ⟨by rw [cw1] at V; exact V, by rw [cb1] at O; exact O, K⟩

/-- A number of `L` bytes into the top of the wide context's slot `d`, kept by its context: the bytes'
value times `2^(8 (Bc − L))`. -/
theorem loadTopCtx_ok {M : Nat} (C : CtxOk Ex base bytes len args .wide M s) {d p l L : Nat} (hd1 : 1 ≤ d)
    (hd : d ≤ 8) (hp : p < 18) (hl : l < 18) (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLl : L ≤ len)
    (fit : (args p).toNat + L ≤ 2 ^ 32) (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (loadTop (.slot .wide d) (one .wide) p l) s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧
      sv u.mem base len .wide d =
        2 ^ (8 * (bc len .wide - L)) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
      Outside base (lo len (.slot .wide d)) (bc len .wide) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have h := C.inp
  have bl := h.bytes_lt
  have lb := len_le_bc len
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have d8 := Nat.mul_le_mul_right (st len .wide) hd
  have d1 := Nat.mul_le_mul_right (st len .wide) hd1
  refine WP.mono (loadTop_ok h (one_ok .wide) (slot_fit1 h (j := d) (by omega)) (p := p) (l := l) (L := L) hp hl hlen
    hL (by rw [cb1]; omega) fit rd apart) fun u ⟨V, O, K⟩ => ?_
  rw [cb1] at O V
  rw [cw1] at V
  exact ⟨C.keepF K (by decide) (by decide) (ws := [(lo len (.slot .wide d), bc len .wide)])
      (frameR_of_outside O (by omega) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega), V, O, K⟩

/-- The exponent's top `2 L` windows, of a number of `L` bytes at the top of `Bc`: the number. -/
theorem top_windows {E L B : Nat} (hL : L ≤ B) :
    2 ^ (8 * (B - L)) * E * 16 ^ (2 * L) / 2 ^ (8 * B) = E := by
  rw [show (16 : Nat) ^ (2 * L) = 2 ^ (8 * L) by rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega,
    Nat.mul_comm (2 ^ _) E, Nat.mul_assoc, ← Nat.pow_add, show 8 * (B - L) + 8 * L = 8 * B by omega]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

/-- The steps of `powTop` before its power. -/
abbrev topFront (b : Nat) : List (Prog isa) :=
  [Impl.Ffdh.X86.ctxP, copy (.slot .wide b) (.slot .wide 5) (one .wide), loadTop (.slot .wide 8) (one .wide) 10 11]

theorem powTop_eq (b : Nat) :
    Impl.Ffdh.X86.powTop b = Prog.chain (topFront b) (windowPowerWith .wide (lenCount 11)) := rfl

/-- p's context, the number in slot `b` in slot 5, and x at the top of slot 8. -/
theorem topFront_ok (h : In Ex base bytes len args s) (X : XGeo args base bytes len xl s.rd s.wr)
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) {P b : Nat} (hb9 : 9 ≤ b)
    (hb : b ≤ 19) (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa (Prog.chain (topFront b) (.block [])) s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P ∧
      sv u.mem base len .wide 5 = sv s.mem base len .wide b ∧
      sv u.mem base len .wide 8 = 2 ^ (8 * (bc len .wide - xl)) * xv s.mem args xl ∧
      Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e5 := lo_wide len 5
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  have xf := X.fit
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  refine WP.seq (WP.mono (ctxP_ok h hP) fun u₁ ⟨C₁, one₁, R₁, F₁, k₁, K₁⟩ => ?_)
  have h₁ := C₁.inp
  refine WP.seq (WP.mono (copyIn_ok h₁ (j := b) (d := 5) hb9 hb (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have C₂ : CtxOk Ex base bytes len args .wide P u₂ := by
    refine C₁.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) K₂ (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide)]) (frameR_of_outside O₂ (by omega) (by simp)) ?_ ?_
    · intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega
    · intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega
  have G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₁.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  have S₂ : Step Ex base bytes len args s u₂ := Step.ops h (F₁.trans G₂) (K₁.trans (K₂.mono (by decide)))
  have X₂ := X.keep ⟨rfl, rfl⟩ S₂.keeps
  refine WP.seq (WP.mono (loadTopCtx_ok C₂ (d := 8) (p := 10) (l := 11) (L := xl) (by decide) (by decide)
    (by decide) (by decide) X₂.e11 X₂.pos X₂.le X₂.fit X₂.rd X₂.apart) fun u₃ ⟨C₃, V₃, O₃, K₃⟩ => WP.block_nil ?_)
  rw [bytes_keep h X.apart (by omega) hx40 S₂.frame] at V₃
  have G₃ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₂.mem u₃.mem :=
    stR_of_outside h (by decide) O₃ ⟨_, by simp, slot_in h .wide (j := 8) (by decide)⟩
  refine ⟨C₃, ?_, ?_, ?_, V₃, (F₁.trans G₂).trans G₃,
    (k₁.trans (kept_ops h G₂ h.room)).trans (kept_ops h G₃ h.room), S₂.keeps.trans (K₃.mono (by decide))⟩
  · rw [slotKeep C₂.inp (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, one₁]
  · rw [slotKeep C₂.inp (by decide) (by decide) O₃, slotKeep h₁ (by decide) (by decide) O₂, R₁]
  · rw [slotKeep C₂.inp (by decide) (by decide) O₃, V₂, k₁.slots b hb9 hb (by simp)]

/-- The number in slot `b` to the power of x, raised over x's `xl` bytes from the top of slot 8. -/
theorem powTop_ok (h : In Ex base bytes len args s) (X : XGeo args base bytes len xl s.rd s.wr)
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) {P b : Nat} (hb9 : 9 ≤ b)
    (hb : b ≤ 19) (hP : safeM (sv s.mem base len .wide 9) = P) :
    WP isa (Impl.Ffdh.X86.powTop b) s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide b ^ xv s.mem args xl % P ∧
      sv u.mem base len .wide 3 = 1 ∧
      Frame (frameR base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have xp := X.pos
  have xle := X.le
  have lb := len_le_bc len
  have bw := bc_eq_cwc len .wide
  rw [powTop_eq]
  refine WP.chain_split (topFront_ok h X hx40 hb9 hb hP) fun u₃ ⟨C₃, one₃, R₃, B₃, V₃, F₃, k₃, K₃⟩ => ?_
  refine WP.mono (windowPowerWith_ok C₃ one₃ R₃ (N := 2 * xl) (by omega) (by omega) fun t Ct =>
    wp_movS (Ct.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ => WP.block_nil
      ⟨a₁.keeps.trans (a₂.keeps.mono (by decide)), by rw [a₂.mem, a₁.mem], by
        rw [a₂.gpr, a₁.gpr, X.e11, BitVec.ofNat_add_ofNat]; congr 1; omega⟩) fun u ⟨C, F, K, Y⟩ => ?_
  rw [V₃, show 32 * cwc len .wide = 8 * bc len .wide by omega, top_windows (by omega), B₃] at Y
  have sp₃ : u₃.gpr .esp = s.gpr .esp := K₃.1 _ (by decide)
  rw [sp₃] at F
  have G := stR_widen F (pwR_in C₃.inp .wide 0)
  refine ⟨C, Y, ?_, F₃.trans G, k₃.trans (kept_ops h G h.room), K₃.trans K⟩
  rw [pwR_sv3 C₃.inp F (by rw [← sp₃]; exact C₃.inp.room), one₃]

/-- A copy of the wide slot 15 into 16. -/
theorem copy1516_ok (h : In Ex base bytes len args s) :
    WP isa (copy (.slot .wide 15) (.slot .wide 16) (one .wide)) s fun u =>
      Outside base (lo len (.slot .wide 16)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide 16 = sv s.mem base len .wide 15 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e15 := lo_wide len 15
  have e16 := lo_wide len 16
  refine WP.mono (copy_ok h (x := .slot .wide 15) (d := .slot .wide 16) (one_ok .wide) (slot_fit1 h (by decide))
    (slot_fit1 h (by decide)) (by rw [cb1]; exact .inr (by omega))) fun u ⟨O, V, K⟩ => ⟨?_, ?_, K⟩
  · rw [cb1] at O; exact O
  · rw [cw1] at V; exact V

/-- The scalar's bound in slot 16, and in the accumulator word whether, without q, x is below p. -/
theorem bound_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    {A x p qv : Nat} (h15 : sv s.mem base len .wide 15 = A) (h13 : sv s.mem base len .wide 13 = x)
    (h9 : sv s.mem base len .wide 9 = p) (hq : ¬ dlen = 2 * len → comp s.mem args len 2 = qv) :
    WP isa Impl.Ffdh.X86.CheckPrivate.bound s fun v => Step Ex base bytes len args s v ∧
      sv v.mem base len .wide 16 = (if dlen = 2 * len then A else qv) ∧
      w32 v.mem base accOff = (cmask (if dlen = 2 * len then decide (x < p) else true)).toNat ∧
      Kept base len [16] [accOff] s.mem v.mem := by
  have dl := G.dl
  have lw := G.lower
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.CheckPrivate.bound
  refine WP.seq (WP.mono (qTest_ok h G.e3 G.e12 dl) fun u₁ ⟨z₁, m₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.regs h m₁ K₁
  refine WP.ite _ z₁ (fun hb => ?_) (fun hb => ?_)
  · have e2 : dlen = 2 * len := by simpa using hb
    refine WP.seq (WP.mono (copy1516_ok S₁.inp) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
    have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
    have k₂ := kept_slot S₁.inp (a := 16) O₂
    refine WP.seq (WP.mono (lessW_ok S₂.inp (a := 13) (b := 9) (by decide) (by decide)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
    have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp m₃ K₃
    rw [k₂.slot_eq, k₂.slot_eq, m₁, h13, h9] at e₃
    refine WP.mono (storeMask_ok S₃.inp (d := accOff) (by omega) e₃) fun v ⟨_, O₄, W₄, _, K₄⟩ => ?_
    have S₄ : Step Ex base bytes len args u₃ v := Step.word S₃.inp (by omega) O₄ K₄
    have k₄ := kept_word S₃.inp (d := accOff) (by omega) (by decide) O₄
    refine ⟨((S₁.trans S₂).trans S₃).trans S₄, ?_, ?_, ?_⟩
    · simp only [e2, ↓reduceIte]; rw [k₄.slot_eq, m₃, V₂, m₁, h15]
    · simp only [e2, ↓reduceIte]; exact W₄
    · refine ⟨fun j a b c => ?_, fun d a b e c => ?_⟩
      · rw [k₄.slots j a b (by simp), m₃, k₂.slots j a b c, m₁]
      · rw [k₄.words d a b e c, m₃, k₂.words d a b e (by simp), m₁]
  · have e3 : dlen = 3 * len := by
      have : ¬ dlen = 2 * len := by simpa using hb
      omega
    refine WP.seq (WP.mono (loadComp_ok S₁.inp (G.keep ⟨rfl, rfl⟩ S₁.keeps) (k := 2) (j := 16) (by decide)
      (by omega) (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
    have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
    have k₂ := kept_slot S₁.inp (a := 16) O₂
    refine wp_movS rfl fun u₃ U₃ _ => ?_
    have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp U₃.mem U₃.keeps
    refine WP.mono (storeMask_ok S₃.inp (d := accOff) (c := true) (by omega) (by rw [U₃.gpr]; rfl))
      fun v ⟨_, O₄, W₄, _, K₄⟩ => ?_
    have S₄ : Step Ex base bytes len args u₃ v := Step.word S₃.inp (by omega) O₄ K₄
    have k₄ := kept_word S₃.inp (d := accOff) (by omega) (by decide) O₄
    have n2 : ¬ dlen = 2 * len := by omega
    refine ⟨((S₁.trans S₂).trans S₃).trans S₄, ?_, ?_, ?_⟩
    · simp only [n2, ↓reduceIte]; rw [k₄.slot_eq, U₃.mem, V₂, m₁, hq n2]
    · simp only [n2, ↓reduceIte]; exact W₄
    · refine ⟨fun j a b c => ?_, fun d a b e c => ?_⟩
      · rw [k₄.slots j a b (by simp), U₃.mem, k₂.slots j a b c, m₁]
      · rw [k₄.words d a b e c, U₃.mem, k₂.words d a b e (by simp), m₁]

/-- The bound, the scalar's mask and ZF telling whether x is not below the bound and positive (and,
without q, below p). -/
theorem boundTest_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    {x p qv : Nat} (h15 : sv s.mem base len .wide 15 = pm1 len p) (h13 : sv s.mem base len .wide 13 = x)
    (h9 : sv s.mem base len .wide 9 = p) (hq : ¬ dlen = 2 * len → comp s.mem args len 2 = qv) :
    WP isa (Prog.chain [Impl.Ffdh.X86.CheckPrivate.bound, Impl.Ffdh.X86.CheckPrivate.scalarMask,
      Impl.Ffdh.X86.testMask] (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Kept base len [16, 17] [maskOff, accOff] s.mem u.mem ∧
      isa.eval .e u = some (!((decide (x < (if dlen = 2 * len then pm1 len p else qv)) && decide (0 < x)) &&
        (if dlen = 2 * len then decide (x < p) else true))) ∧
      sv u.mem base len .wide 16 = (if dlen = 2 * len then pm1 len p else qv) := by
  have mo : maskOff = 12 := rfl
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (bound_ok h G h15 h13 h9 hq) fun u₅ ⟨S₅, B₅, W₅, k₅⟩ => ?_)
  refine WP.seq ?_
  unfold Impl.Ffdh.X86.CheckPrivate.scalarMask
  refine WP.seq (WP.mono (zeroW_ok S₅.inp (a := 17) (by decide)) fun u₆ ⟨O₆, Z₆, K₆⟩ => ?_)
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.slot S₅.inp (by decide) O₆ K₆
  have k₆ := kept_slot S₅.inp (a := 17) O₆
  refine WP.seq (WP.mono (lessW_ok S₆.inp (a := 17) (b := 13) (by decide) (by decide)) fun u₇ ⟨m₇, e₇, K₇⟩ => ?_)
  rw [Z₆, k₆.slot_eq, k₅.slot_eq, h13] at e₇
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.regs S₆.inp m₇ K₇
  refine WP.seq (WP.mono (storeMask_ok S₇.inp (d := maskOff) (by omega) e₇) fun u₈ ⟨_, O₈, W₈, _, K₈⟩ => ?_)
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.word S₇.inp (by omega) O₈ K₈
  have k₈ := kept_word S₇.inp (d := maskOff) (by omega) (by decide) O₈
  refine WP.seq (WP.mono (lessW_ok S₈.inp (a := 13) (b := 16) (by decide) (by decide)) fun u₉ ⟨m₉, e₉, K₉⟩ => ?_)
  rw [k₈.slot_eq, k₈.slot_eq, m₇, k₆.slot_eq, k₆.slot_eq, B₅, k₅.slot_eq, h13] at e₉
  have S₉ : Step Ex base bytes len args u₈ u₉ := Step.regs S₈.inp m₉ K₉
  have Wacc : w32 u₉.mem base accOff = (cmask (if dlen = 2 * len then decide (x < p) else true)).toNat := by
    rw [m₉, k₈.word_eq, m₇, k₆.word_eq, W₅]
  refine (show WP isa (.block ([.alu .and .ecx (.mem (sc maskOff))] ++ [.alu .and .ecx (.mem (sc accOff))])) u₉ _
    from WP.block_append (WP.mono (andMask_ok S₉.inp (d := maskOff) (c' := decide (0 < x)) (by omega) e₉ (by rw [m₉]; exact W₈))
      fun u₁₀ ⟨e₁₀, m₁₀, K₁₀⟩ => WP.mono (andMask_ok (S₉.inp.regs K₁₀ m₁₀) (d := accOff)
        (c' := if dlen = 2 * len then decide (x < p) else true) (by omega) e₁₀
        (by rw [m₁₀]; exact Wacc)) fun u₁₁ ⟨e₁₁, m₁₁, K₁₁⟩ => ?_))
  have S₁₀ : Step Ex base bytes len args u₉ u₁₀ := Step.regs S₉.inp m₁₀ K₁₀
  have S₁₁ : Step Ex base bytes len args u₁₀ u₁₁ := Step.regs S₁₀.inp m₁₁ K₁₁
  refine WP.seq (WP.mono (testMask_ok e₁₁) fun u₁₂ ⟨z, m₁₂, K₁₂⟩ => WP.block_nil ?_)
  have S₁₂ : Step Ex base bytes len args u₁₁ u₁₂ := Step.regs S₁₁.inp m₁₂ K₁₂
  refine ⟨((((((S₅.trans S₆).trans S₇).trans S₈).trans S₉).trans S₁₀).trans S₁₁).trans S₁₂, ?_, z, ?_⟩
  · rw [m₁₂, m₁₁, m₁₀, m₉]
    exact ((k₅.mono).trans k₆.mono).trans (by rw [← m₇]; exact k₈.mono)
  · rw [m₁₂, m₁₁, m₁₀, m₉, k₈.slot_eq, m₇, k₆.slot_eq, B₅]

/-- The body up to its branch on the scalar. -/
abbrev privFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5, load (.slot .wide 12) (one .wide) 8 9,
    load (.slot .wide 13) (one .wide) 10 11, Impl.Ffdh.X86.CheckPrivate.bound, Impl.Ffdh.X86.CheckPrivate.scalarMask,
    Impl.Ffdh.X86.testMask]

theorem body_eq : Impl.Ffdh.X86.CheckPrivate.body =
    Prog.chain privFront (.ite .e (Impl.Ffdh.X86.ret 2) Impl.Ffdh.X86.CheckPrivate.pair) := rfl

/-- The parameters of the domain. -/
abbrev params (m : Mem) (args : Nat → BitVec 32) (len dlen : Nat) : Spec.Ffdh.Parameters :=
  Spec.Ffdh.domainOf len (domBytes m args dlen)

/-- The code's scalar test is `privateValid`'s, for any domain. -/
theorem scalar_iff {p q x : Nat} {a : Spec.Ffdh.Parameters} (hp : a.p = p) {dlen : Nat}
    (hq : a.q = if dlen = 2 * len then none else some q) :
    (!((decide (x < (if dlen = 2 * len then pm1 len p else q)) && decide (0 < x)) &&
      (if dlen = 2 * len then decide (x < p) else true))) = true ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateValid
  rw [hp, hq]
  by_cases e : dlen = 2 * len
  · simp only [e, ↓reduceIte, Option.getD_none]
    unfold pm1
    by_cases a1 : 0 < x <;> by_cases a2 : x < p - 1 <;> by_cases a3 : x < p <;> by_cases a4 : 0 < p <;>
      simp [a1, a2, a3, a4] <;> omega
  · simp only [e, ↓reduceIte, Option.getD_some, Bool.and_true]
    by_cases a1 : 0 < x <;> by_cases a2 : x < q <;> simp [a1, a2]

/-- p, g, y, x and one into slots 9, 10, 12, 13 and 14, `pm1 p` into 15, and ZF telling whether x is an
invalid scalar. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) :
    WP isa (Prog.chain privFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = false) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 10 = comp s.mem args len 1 ∧
      sv u.mem base len .wide 12 = yv s.mem args len ∧ sv u.mem base len .wide 13 = xv s.mem args xl ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have yf := Y.fit
  have xf := X.fit
  have xle := X.le
  have h2 : 2 * len ≤ dlen := by omega
  have hpa := comp_p s.mem args h2
  have hqa : (params s.mem args len dlen).q = if dlen = 2 * len then none else some (comp s.mem args len 2) := by
    rcases dl with e | e
    · simp only [e, ↓reduceIte]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega)
    · have : ¬ 3 * len = 2 * len := by omega
      simp only [e, this, ↓reduceIte]; exact comp_q s.mem args
  have mo : maskOff = 12 := rfl
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  generalize hP : comp s.mem args len 0 = p at hpa
  generalize hG : comp s.mem args len 1 = g
  generalize hY : yv s.mem args len = y
  generalize hX : xv s.mem args xl = x
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g, y and x.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  have S₁₂ := S₁.trans S₂
  refine WP.seq (WP.mono (loadY_ok S₂.inp (Y.keep ⟨rfl, rfl⟩ S₁₂.keeps)) fun u₃ ⟨V₃, O₃, K₃⟩ => ?_)
  rw [show yv u₂.mem args len = y by rw [yv, bytes_keep h Y.apart (by omega) hy40 S₁₂.frame]; exact hY] at V₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot S₂.inp (by decide) O₃ K₃
  have k₃ := kept_slot S₂.inp (a := 12) O₃
  have S₁₃ := S₁₂.trans S₃
  refine WP.seq (WP.mono (loadX_ok S₃.inp (X.keep ⟨rfl, rfl⟩ S₁₃.keeps)) fun u₄ ⟨V₄, O₄, K₄⟩ => ?_)
  rw [show xv u₃.mem args xl = x by rw [xv, bytes_keep h X.apart (by omega) hx40 S₁₃.frame]; exact hX] at V₄
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.slot S₃.inp (by decide) O₄ K₄
  have k₄ := kept_slot S₃.inp (a := 13) O₄
  have S₁₄ := S₁₃.trans S₄
  have k₁₄ : Kept base len [9, 10, 12, 13, 14, 15] [] s.mem u₄.mem :=
    ((k₁.mono).trans k₂.mono).trans (k₃.mono.trans k₄.mono)
  have v9 : sv u₄.mem base len .wide 9 = p := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V9]
  have v10 : sv u₄.mem base len .wide 10 = g := by rw [k₄.slot_eq, k₃.slot_eq, V₂]
  have v12 : sv u₄.mem base len .wide 12 = y := by rw [k₄.slot_eq, V₃]
  have v14 : sv u₄.mem base len .wide 14 = 1 := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V14]
  have v15 : sv u₄.mem base len .wide 15 = pm1 len p := by rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V15]
  -- The bound and the scalar's test.
  refine WP.mono (boundTest_ok S₄.inp (G.keep ⟨rfl, rfl⟩ S₁₄.keeps) v15 V₄ v9
    (fun n2 => comp_keep h G hb40 S₁₄.frame (by omega))) fun u₁₂ ⟨S₁₂, k₁₂, z, _⟩ => ?_
  have S := S₁₄.trans S₁₂
  have kk : ∀ {j}, 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [16, 17] →
      sv u₁₂.mem base len .wide j = sv u₄.mem base len .wide j := fun hj => k₁₂.slot_eq hj
  refine ⟨S, Gate.of_eval z (scalar_iff hpa.symm hqa), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kk (by decide), v9]
  · rw [kk (by decide), v10]
  · rw [kk (by decide), v12]
  · rw [kk (by decide), V₄]
  · rw [kk (by decide), v14]
  · rw [kk (by decide), v15]

/-- y in range and `g^x mod M = y`, as a status. -/
theorem pair_ok (h : In Ex base bytes len args s) {p g y x : Nat} (h9 : sv s.mem base len .wide 9 = p)
    (h10 : sv s.mem base len .wide 10 = g) (h12 : sv s.mem base len .wide 12 = y)
    (X : XGeo args base bytes len xl s.rd s.wr) (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96))
    (hx : xv s.mem args xl = x) (h14 : sv s.mem base len .wide 14 = 1)
    (h15 : sv s.mem base len .wide 15 = pm1 len p) :
    WP isa Impl.Ffdh.X86.CheckPrivate.pair s (Res base len s
      ((decide (g ^ x % safeM p = y) && (decide (y < pm1 len p) && decide (1 < y))).toNat)) := by
  have ao : accOff = 8 := rfl
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  unfold Impl.Ffdh.X86.CheckPrivate.pair
  refine WP.seq (WP.mono (rangeMask_ok h (a := 12) (by decide)) fun u₁ ⟨I₁, e₁, O₁, K₁⟩ => ?_)
  rw [h12, h15, h14] at e₁
  have S₁ : Step Ex base bytes len args s u₁ := Step.word h (by decide) O₁ K₁
  have k₁ := kept_word h (d := maskOff) (by decide) (by decide) O₁
  refine WP.seq (WP.mono (storeMask_ok I₁ (d := accOff) (by omega) e₁) fun u₂ ⟨_, O₂, W₂, _, K₂⟩ => ?_)
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.word I₁ (by omega) O₂ K₂
  have k₂ := kept_word I₁ (d := accOff) (by omega) (by decide) O₂
  have k₁₂ : Kept base len [] [maskOff, accOff] s.mem u₂.mem := k₁.mono.trans k₂.mono
  have S₁₂ := S₁.trans S₂
  have xf := X.fit
  refine WP.seq (WP.mono (powTop_ok S₂.inp (X.keep ⟨rfl, rfl⟩ S₁₂.keeps) (by rw [S₁₂.esp]; exact hx40)
    (P := safeM p) (b := 10) (by decide) (by decide) (by rw [k₁₂.slot_eq, h9]))
    fun u₃ ⟨C₃, Y₃, _, F₃, k₃, K₃⟩ => ?_)
  have xe : xv u₂.mem args xl = x := by rw [xv, bytes_keep h X.apart (by omega) hx40 S₁₂.frame]; exact hx
  rw [k₁₂.slot_eq, h10, xe] at Y₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.ops S₂.inp F₃ K₃
  refine WP.seq (WP.mono (eqW_ok C₃.inp (a := 6) (b := 12) (by decide) (by decide)) fun u₄ ⟨m₄, e₄, K₄⟩ => ?_)
  rw [Y₃, k₃.slot_eq, k₁₂.slot_eq, h12] at e₄
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.regs C₃.inp m₄ K₄
  refine WP.seq (WP.mono (andMask_ok S₄.inp (d := accOff)
    (c' := decide (y < pm1 len p) && decide (1 < y)) (by omega) e₄ (by rw [m₄, k₃.word_eq]; exact W₂))
    fun u₅ ⟨e₅, m₅, K₅⟩ => ?_)
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S₄.inp m₅ K₅
  refine WP.mono (retMask_ok e₅) fun t ⟨E, M, K⟩ => ((((S₁.trans S₂).trans S₃).trans S₄).trans S₅).res
    ⟨E, by rw [M]; exact Frame.refl _ _, K.mono (by decide)⟩

/-- The status the contract asks for, for a valid domain. -/
abbrev expected (len dlen xl : Nat) (m : Mem) (args : Nat → BitVec 32) : Nat :=
  Spec.Ffdh.privateStatus (params m args len dlen) (yv m args len) (xv m args xl)

/-- `vg_ffdh_check_private`'s body: a status, `expected` for a valid domain. -/
theorem body_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) :
    WP isa Impl.Ffdh.X86.CheckPrivate.body s fun t => ∃ r, Res base len s r t ∧
      (Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true → r = expected len dlen xl s.mem args) := by
  have dl := G.dl
  have h2 : 2 * len ≤ dlen := by omega
  have hpa := comp_p s.mem args h2
  have hga := comp_g s.mem args h2
  rw [body_eq]
  refine WP.chain_split (front_ok h G Y X hb40 hy40 hx40) fun u ⟨S, Gt, V9, V10, V12, _, V14, V15⟩ => ?_
  refine WP.gate Gt (fun inval => WP.mono (ret_res (base := base) (len := len)) fun t R => ⟨2, S.res R, ?_⟩)
    (fun val => WP.mono (pair_ok (x := xv s.mem args xl) S.inp V9 V10 V12 (X.keep ⟨rfl, rfl⟩ S.keeps) (by rw [S.esp]; exact hx40)
      (by have := X.fit; rw [xv, bytes_keep h X.apart (by omega) hx40 S.frame]) V14 V15) fun t R => ⟨_, S.res R, ?_⟩)
  · intro _
    simp only [expected, Spec.Ffdh.privateStatus, inval, Bool.not_false, ↓reduceIte]
  · intro v
    have pv : Spec.Ffdh.parametersValid (params s.mem args len dlen) = true := by
      have := v; unfold Spec.Ffdh.domainValid at this
      simp only [Bool.and_eq_true] at this
      exact this.1
    have mv := VG.Proof.Ffdh.domainValid_mod v
    rw [← comp_p s.mem args h2] at mv
    unfold Spec.Rsa.modulusValid at mv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
    have gt : 1 < comp s.mem args len 0 := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega
    have val : Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl) = true := by
      cases e : Spec.Ffdh.privateValid (params s.mem args len dlen) (xv s.mem args xl)
      · exact absurd e val
      · rfl
    rw [expected, VG.Proof.Ffdh.privateStatus_eq pv, val, ite_eq_right_iff.mpr (fun h' => by cases h')]
    rw [safeM_of gt mv.1.1.1, pm1_of (by omega)]
    rw [show (params s.mem args len dlen).p = comp s.mem args len 0 from hpa.symm,
      show (params s.mem args len dlen).g = comp s.mem args len 1 from hga.symm]
    generalize comp s.mem args len 0 = p at *
    generalize comp s.mem args len 1 = g at *
    generalize yv s.mem args len = y
    generalize xv s.mem args xl = x
    have key : (Spec.Ffdh.publicValid ⟨params s.mem args len dlen, y⟩ = true ∧ g ^ x % p = y) ↔
        ((1 < y ∧ y < p - 1) ∧ g ^ x % p = y) := by
      constructor
      · rintro ⟨pvy, e⟩
        have r := ((VG.Proof.Ffdh.publicValid_eq _ _).mp pvy).1
        rw [← hpa] at r
        exact ⟨r, e⟩
      · rintro ⟨r, e⟩
        refine ⟨?_, e⟩
        have pw := (VG.Proof.Ffdh.publicValid_power pv x).mpr
        rw [← hpa, ← hga, e] at pw
        exact pw r
    simp only [key]
    by_cases a1 : 1 < y <;> by_cases a2 : y < p - 1 <;> by_cases a3 : g ^ x % p = y <;>
      simp only [a1, a2, a3, and_self, and_true, and_false, ↓reduceIte, decide_true, decide_false,
        Bool.and_true, Bool.and_false, Bool.toNat_true, Bool.toNat_false]

end VG.Proof.Ffdh.X86.CheckPrivate

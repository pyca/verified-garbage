module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Framework.RelCTChain

/-!
# `vg_ffdh_exchange` on i686: the shared value

`body_ok`: `z = y^x mod p` (modulo `safeM p` for any domain), its range
`1 < z < p − 1` as the acceptance mask, and z, or zeros unless accepted,
written to the output; the status is the mask's.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Exchange

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes argNum_comp)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv bytes_keep)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen xl : Nat}
  {args : Nat → BitVec 32}

/-- The output, of `len` bytes at synthetic argument 0. -/
structure OutGeo (args : Nat → BitVec 32) (base : Addr) (bytes len : Nat) (wr : List Region) : Prop where
  fit : (args 0).toNat + len ≤ 2 ^ 32
  wr : InRegions wr (byteAddr (args 0)) len
  apart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩

/-- A number of `len` bytes into the wide context's slot `d`, kept by its context. -/
theorem loadCtx_ok {M : Nat} (C : CtxOk Ex base bytes len args .wide M s) {d p l L : Nat} (hd1 : 1 ≤ d)
    (hd : d ≤ 8) (hp : p < 18) (hl : l < 18) (hlen : args l = BitVec.ofNat 32 L) (hL : 0 < L) (hLl : L ≤ len)
    (fit : (args p).toNat + L ≤ 2 ^ 32) (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) L)
    (apart : Region.Disjoint ⟨byteAddr (args p), L⟩ ⟨base, bytes⟩) :
    WP isa (load (.slot .wide d) (one .wide) p l) s fun u =>
      CtxOk Ex base bytes len args .wide M u ∧
      sv u.mem base len .wide d = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) L) ∧
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
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := d) (by omega)) (p := p) (l := l) (L := L) hp hl hlen hL
    (by rw [cb1]; omega) fit rd apart) fun u ⟨V, O, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨C.keepF K (by decide) (by decide) (ws := [(lo len (.slot .wide d), bc len .wide)])
      (frameR_of_outside O (by omega) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega), V, O, K⟩

/-- The body up to the power. -/
abbrev exFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, Impl.Ffdh.X86.ctxP, load (.slot .wide 5) (one .wide) 8 9,
    load (.slot .wide 8) (one .wide) 10 11]

/-- The body after the power. -/
abbrev exTail : Prog isa :=
  Prog.chain [Impl.Ffdh.X86.rangeMask 6, .block [.store (sc accOff) .ecx],
    copy (.slot .wide 6) (.slot .wide 19) (one .wide)] exportResult

theorem body_eq : Impl.Ffdh.X86.Exchange.body = Prog.chain exFront (.seq (windowPower .wide) exTail) := rfl

/-- p's context, with y in slot 5 and x in 8. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 40))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40)) :
    WP isa (Prog.chain exFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      CtxOk Ex base bytes len args .wide (safeM (comp s.mem args len 0)) u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % safeM (comp s.mem args len 0) ∧
      sv u.mem base len .wide 5 = yv s.mem args len ∧ sv u.mem base len .wide 8 = xv s.mem args xl ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have yf := Y.fit
  have xf := X.fit
  have xle := X.le
  generalize hP : comp s.mem args len 0 = p
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- p's context.
  refine WP.seq (WP.mono (ctxP_ok I₁ (P := safeM p) (by rw [V9])) fun u₂ ⟨C₂, one₂, R₂, F₂, k₂, K₂⟩ => ?_)
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.ops I₁ F₂ K₂
  have S₁₂ := S₁.trans S₂
  -- y and x.
  have Y₂ := Y.keep ⟨rfl, rfl⟩ S₁₂.keeps
  refine WP.seq (WP.mono (loadCtx_ok C₂ (d := 5) (p := 8) (l := 9) (L := len) (by decide) (by decide) (by decide)
    (by decide) Y₂.e9 (by omega) (Nat.le_refl _) Y₂.fit Y₂.rd Y₂.apart) fun u₃ ⟨C₃, V₃, O₃, K₃⟩ => ?_)
  rw [bytes_keep h Y.apart (by omega) hy40 S₁₂.frame] at V₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot C₂.inp (by decide) O₃ K₃
  have S₁₃ := S₁₂.trans S₃
  have X₃ := X.keep ⟨rfl, rfl⟩ S₁₃.keeps
  refine WP.seq (WP.mono (loadCtx_ok C₃ (d := 8) (p := 10) (l := 11) (L := xl) (by decide) (by decide) (by decide)
    (by decide) X₃.e11 X₃.pos X₃.le X₃.fit X₃.rd X₃.apart) fun u₄ ⟨C₄, V₄, O₄, K₄⟩ => WP.block_nil ?_)
  rw [bytes_keep h X.apart (by omega) hx40 S₁₃.frame] at V₄
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.slot C₃.inp (by decide) O₄ K₄
  have k₃ := kept_slot C₂.inp (a := 5) O₃
  have k₄ := kept_slot C₃.inp (a := 8) O₄
  refine ⟨S₁₃.trans S₄, C₄, ?_, ?_, ?_, V₄, ?_, ?_⟩
  · rw [slotKeep C₃.inp (by decide) (by decide) O₄, slotKeep C₂.inp (by decide) (by decide) O₃, one₂]
  · rw [slotKeep C₃.inp (by decide) (by decide) O₄, slotKeep C₂.inp (by decide) (by decide) O₃, R₂]
  · rw [slotKeep C₃.inp (by decide) (by decide) O₄, V₃]
  · rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V14]
  · rw [k₄.slot_eq, k₃.slot_eq, k₂.slot_eq, V15]

theorem OutGeo.keep {wr : List Region} (O : OutGeo args base bytes len wr) {s t : State} {rs : List Reg}
    (e : s.wr = wr) (K : Keeps rs s t) : OutGeo args base bytes len t.wr := by
  rw [K.2.2, e]; exact O

/-- The shared value, modulo `safeM p`. -/
abbrev zv (m : Mem) (args : Nat → BitVec 32) (len xl : Nat) : Nat :=
  yv m args len ^ xv m args xl % safeM (comp m args len 0)

/-- Its acceptance: `1 < z < pm1 p`. -/
abbrev acc (m : Mem) (args : Nat → BitVec 32) (len xl : Nat) : Bool :=
  decide (zv m args len xl < pm1 len (comp m args len 0)) && decide (1 < zv m args len xl)

/-- `vg_ffdh_exchange`'s body: z, or zeros unless accepted, written to the output, and the acceptance. -/
theorem body_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (O : OutGeo args base bytes len s.wr)
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 40))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 40)) :
    WP isa Impl.Ffdh.X86.Exchange.body s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (acc s.mem args len xl).toNat ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len =
        Spec.Rsa.i2osp (if acc s.mem args len xl then zv s.mem args len xl else 0) len ∧
      Frame (⟨byteAddr (args 0), len⟩ :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lw := G.lower
  have bl := h.bytes_lt
  have ao : accOff = 8 := rfl
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e6 := lo_wide len 6
  have e19 := lo_wide len 19
  have f19 := h.slot_fit .wide (j := 19) (by decide)
  /- z fits in `len` bytes. -/
  have plt : comp s.mem args len 0 < 2 ^ (8 * len) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2) + BitVec.ofNat 64 (0 * len)) len)
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    rw [Nat.pow_mul] at *
    exact this
  have zlt : zv s.mem args len xl < 2 ^ (8 * len) := by
    have zm := Nat.mod_lt (yv s.mem args len ^ xv s.mem args xl)
      (Nat.lt_trans Nat.zero_lt_one (safeM_gt (comp s.mem args len 0)))
    have mlt : safeM (comp s.mem args len 0) < 2 ^ (8 * len) := by
      unfold safeM
      split
      · exact plt
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ 8 * len by omega)
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega
    exact Nat.lt_trans zm mlt
  generalize hz : zv s.mem args len xl = z at zlt
  generalize hc : acc s.mem args len xl = c
  rw [body_eq]
  refine WP.chain_split (front_ok h G Y X hy40 hx40) fun u ⟨S, C, one, R2, V5, V8, V14, V15⟩ => ?_
  -- z.
  refine WP.seq (WP.mono (windowPower_ok C one R2) fun u₅ ⟨C₅, F₅, K₅, Y₅⟩ => ?_)
  rw [V5, V8, show yv s.mem args len ^ xv s.mem args xl % safeM (comp s.mem args len 0) = z from hz] at Y₅
  have G₅ := stR_widen F₅ (pwR_in C.inp .wide 0)
  have S₅ : Step Ex base bytes len args u u₅ := Step.ops C.inp G₅ K₅
  have k₅ := kept_ops C.inp G₅ C.inp.room
  -- Its range as the acceptance mask.
  refine WP.seq (WP.mono (rangeMask_ok C₅.inp (a := 6) (by decide)) fun u₆ ⟨I₆, e₆, O₆, K₆⟩ => ?_)
  rw [Y₅, k₅.slot_eq, V15, k₅.slot_eq, V14] at e₆
  have e₆ : u₆.gpr .ecx = cmask c := by
    rw [e₆, ← hc, acc, hz]
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.word C₅.inp (by decide) O₆ K₆
  have k₆ := kept_word C₅.inp (d := maskOff) (by decide) (by decide) O₆
  refine WP.seq (WP.mono (storeMask_ok I₆ (d := accOff) (by omega) e₆) fun u₇ ⟨I₇, O₇, W₇, _, K₇⟩ => ?_)
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.word I₆ (by omega) O₇ K₇
  have k₇ := kept_word I₆ (d := accOff) (by omega) (by decide) O₇
  -- z into slot 19.
  refine WP.seq (WP.mono (copy_ok I₇ (x := .slot .wide 6) (d := .slot .wide 19) (one_ok .wide)
    (slot_fit1 I₇ (by decide)) (slot_fit1 I₇ (by decide)) (by rw [cb1]; exact .inr (by omega)))
    fun u₈ ⟨O₈, V₈, K₈⟩ => ?_)
  rw [cb1] at O₈
  rw [cw1] at V₈
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.slot I₇ (by decide) O₈ K₈
  have k₈ := kept_slot I₇ (a := 19) O₈
  have bw := bc_eq_cwc len .wide
  have f6 := slot_fit1 I₇ (j := 6) (by decide)
  rw [cb1] at f6
  have z₈ : val32 u₈.mem base (lo len (.slot .wide 19)) (cwc len .wide) = z := by
    rw [V₈, Outside.val32 O₇ (.inr (by omega)) (by omega), Outside.val32 O₆ (.inr (by omega)) (by omega)]
    exact Y₅
  have hm : u₈.mem.readW (off base accOff) 32 = cmask c :=
    BitVec.eq_of_toNat_eq ((k₈.word_eq (d := accOff)).trans W₇)
  -- The result cleared unless accepted, and written out.
  unfold exportResult
  refine maskResult_ok S₈.inp (c := c) hm fun u₉ O₉ V₉ K₉ => ?_
  have S₉ : Step Ex base bytes len args u₈ u₉ := Step.slot S₈.inp (by decide) O₉ K₉
  have Sall := ((((((S.trans S₅).trans S₆).trans S₇).trans S₈).trans S₉))
  refine WP.mono (writeResult_ok S₉.inp O.fit ((O.keep rfl Sall.keeps).wr) O.apart) fun t ⟨B, A, Ft, Kt⟩ =>
    ⟨?_, ?_, ?_, Sall.keeps.trans (Kt.mono (by decide))⟩
  · have a₉ : u₉.mem.readW (off base accOff) 32 = cmask c := by
      rw [show u₉.mem.readW (off base accOff) 32 = u₈.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₉.w32 (d := accOff) (.inl (by omega)) (by omega)), hm]
    rw [A, a₉, cmask_and_one]
  · rw [V₉, z₈] at B
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at B ⊢
      exact B (Nat.two_pow_pos _)
    · simp only [↓reduceIte] at B ⊢
      exact B zlt
  · refine (Sall.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (Ft.mono fun r hr => ?_)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..

end VG.Proof.Ffdh.X86.Exchange

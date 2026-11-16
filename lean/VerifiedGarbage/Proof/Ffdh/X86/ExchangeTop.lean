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
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86.Checks

/-! ### `Ffdh.X86.Exchange`, which only this module used -/

section

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
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv loadTopCtx_ok top_windows)

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
  obtain lb := len_le_bc len
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  obtain d8 := Nat.mul_le_mul_right (st len .wide) hd
  obtain d1 := Nat.mul_le_mul_right (st len .wide) hd1
  refine WP.mono (load_ok h (one_ok .wide) (slot_fit1 h (j := d) (by omega_arith)) (p := p) (l := l) (L := L) hp hl hlen hL
    (by rw [cb1]; omega_arith) fit rd apart) fun u ⟨V, O, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨C.keepF K (by decide) (by decide) (ws := [(lo len (.slot .wide d), bc len .wide)])
      (frameR_of_outside O (by omega_arith) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega_arith)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega_arith), V, O, K⟩

/-- The body up to the power. -/
abbrev exFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, Impl.Ffdh.X86.ctxP, load (.slot .wide 5) (one .wide) 8 9,
    loadTop (.slot .wide 8) (one .wide) 10 11]

/-- The body after the power. -/
abbrev exTail : Prog isa :=
  Prog.chain [Impl.Ffdh.X86.rangeMask 6, .block [.store (sc accOff) .ecx],
    copy (.slot .wide 6) (.slot .wide 19) (one .wide)] exportResult

theorem body_eq : Impl.Ffdh.X86.Exchange.body =
    Prog.chain exFront (.seq (windowPowerWith .wide (lenCount 11)) exTail) := rfl

/-- p's context, with y in slot 5 and x in 8. -/
theorem front_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (Y : YGeo args base bytes len s.rd s.wr) (X : XGeo args base bytes len xl s.rd s.wr)
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) :
    WP isa (Prog.chain exFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      CtxOk Ex base bytes len args .wide (safeM (comp s.mem args len 0)) u ∧ sv u.mem base len .wide 3 = 1 ∧
      sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % safeM (comp s.mem args len 0) ∧
      sv u.mem base len .wide 5 = yv s.mem args len ∧
      sv u.mem base len .wide 8 = 2 ^ (8 * (bc len .wide - xl)) * xv s.mem args xl ∧
      sv u.mem base len .wide 14 = 1 ∧ sv u.mem base len .wide 15 = pm1 len (comp s.mem args len 0) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have yf := Y.fit
  have xf := X.fit
  have xle := X.le
  generalize hP : comp s.mem args len 0 = p
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega_arith)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega_arith))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  obtain S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- p's context.
  refine WP.seq (WP.mono (ctxP_ok I₁ (P := safeM p) (by rw [V9])) fun u₂ ⟨C₂, one₂, R₂, F₂, k₂, K₂⟩ => ?_)
  obtain S₂ : Step Ex base bytes len args u₁ u₂ := Step.ops I₁ F₂ K₂
  obtain S₁₂ := S₁.trans S₂
  -- y and x.
  obtain Y₂ := Y.keep ⟨rfl, rfl⟩ S₁₂.keeps
  refine WP.seq (WP.mono (loadCtx_ok C₂ (d := 5) (p := 8) (l := 9) (L := len) (by decide) (by decide) (by decide)
    (by decide) Y₂.e9 (by omega_arith) (Nat.le_refl _) Y₂.fit Y₂.rd Y₂.apart) fun u₃ ⟨C₃, V₃, O₃, K₃⟩ => ?_)
  rw [bytes_keep h Y.apart (by omega_arith) hy40 S₁₂.frame] at V₃
  obtain S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot C₂.inp (by decide) O₃ K₃
  obtain S₁₃ := S₁₂.trans S₃
  obtain X₃ := X.keep ⟨rfl, rfl⟩ S₁₃.keeps
  refine WP.seq (WP.mono (loadTopCtx_ok C₃ (d := 8) (p := 10) (l := 11) (L := xl) (by decide) (by decide) (by decide)
    (by decide) X₃.e11 X₃.pos X₃.le X₃.fit X₃.rd X₃.apart) fun u₄ ⟨C₄, V₄, O₄, K₄⟩ => WP.block_nil ?_)
  rw [bytes_keep h X.apart (by omega_arith) hx40 S₁₃.frame] at V₄
  obtain S₄ : Step Ex base bytes len args u₃ u₄ := Step.slot C₃.inp (by decide) O₄ K₄
  obtain k₃ := kept_slot C₂.inp (a := 5) O₃
  obtain k₄ := kept_slot C₃.inp (a := 8) O₄
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
    (hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below (s.gpr .esp) 96))
    (hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below (s.gpr .esp) 96)) :
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
  obtain e6 := lo_wide len 6
  obtain e19 := lo_wide len 19
  obtain f19 := h.slot_fit .wide (j := 19) (by decide)
  /- z fits in `len` bytes. -/
  obtain plt : comp s.mem args len 0 < 2 ^ (8 * len) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2) + BitVec.ofNat 64 (0 * len)) len)
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    rw [Nat.pow_mul] at *
    exact this
  obtain zlt : zv s.mem args len xl < 2 ^ (8 * len) := by
    obtain zm := Nat.mod_lt (yv s.mem args len ^ xv s.mem args xl)
      (Nat.lt_trans Nat.zero_lt_one (safeM_gt (comp s.mem args len 0)))
    obtain mlt : safeM (comp s.mem args len 0) < 2 ^ (8 * len) := by
      unfold safeM
      split
      · exact plt
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ 8 * len by omega_arith)
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega_arith
    exact Nat.lt_trans zm mlt
  generalize hz : zv s.mem args len xl = z at zlt
  generalize hc : acc s.mem args len xl = c
  rw [body_eq]
  refine WP.chain_split (front_ok h G Y X hy40 hx40) fun u ⟨S, C, one, R2, V5, V8, V14, V15⟩ => ?_
  -- z.
  have xp := X.pos
  have xle := X.le
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  refine WP.seq (WP.mono (windowPowerWith_ok C one R2 (N := 2 * xl) (by omega_arith) (by omega_arith) fun t Ct =>
    wp_movS (Ct.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ => WP.block_nil
      ⟨a₁.keeps.trans (a₂.keeps.mono (by decide)), by rw [a₂.mem, a₁.mem], by
        rw [a₂.gpr, a₁.gpr, X.e11, BitVec.ofNat_add_ofNat]; congr 1; omega_arith⟩) fun u₅ ⟨C₅, F₅, K₅, Y₅⟩ => ?_)
  rw [V8, show 32 * cwc len .wide = 8 * bc len .wide by omega_arith, top_windows (by omega_arith)] at Y₅
  rw [V5, show yv s.mem args len ^ xv s.mem args xl % safeM (comp s.mem args len 0) = z from hz] at Y₅
  obtain G₅ := stR_widen F₅ (pwR_in C.inp .wide 0)
  obtain S₅ : Step Ex base bytes len args u u₅ := Step.ops C.inp G₅ K₅
  obtain k₅ := kept_ops C.inp G₅ C.inp.room
  -- Its range as the acceptance mask.
  refine WP.seq (WP.mono (rangeMask_ok C₅.inp (a := 6) (by decide)) fun u₆ ⟨I₆, e₆, O₆, K₆⟩ => ?_)
  rw [Y₅, k₅.slot_eq, V15, k₅.slot_eq, V14] at e₆
  obtain e₆ : u₆.gpr .ecx = cmask c := by
    rw [e₆, ← hc, acc, hz]
  obtain S₆ : Step Ex base bytes len args u₅ u₆ := Step.word C₅.inp (by decide) O₆ K₆
  obtain k₆ := kept_word C₅.inp (d := maskOff) (by decide) (by decide) O₆
  refine WP.seq (WP.mono (storeMask_ok I₆ (d := accOff) (by omega_arith) e₆) fun u₇ ⟨I₇, O₇, W₇, _, K₇⟩ => ?_)
  obtain S₇ : Step Ex base bytes len args u₆ u₇ := Step.word I₆ (by omega_arith) O₇ K₇
  obtain k₇ := kept_word I₆ (d := accOff) (by omega_arith) (by decide) O₇
  -- z into slot 19.
  refine WP.seq (WP.mono (copy_ok I₇ (x := .slot .wide 6) (d := .slot .wide 19) (one_ok .wide)
    (slot_fit1 I₇ (by decide)) (slot_fit1 I₇ (by decide)) (by rw [cb1]; exact .inr (by omega_arith)))
    fun u₈ ⟨O₈, V₈, K₈⟩ => ?_)
  rw [cb1] at O₈
  rw [cw1] at V₈
  obtain S₈ : Step Ex base bytes len args u₇ u₈ := Step.slot I₇ (by decide) O₈ K₈
  obtain k₈ := kept_slot I₇ (a := 19) O₈
  obtain bw := bc_eq_cwc len .wide
  obtain f6 := slot_fit1 I₇ (j := 6) (by decide)
  rw [cb1] at f6
  obtain z₈ : val32 u₈.mem base (lo len (.slot .wide 19)) (cwc len .wide) = z := by
    rw [V₈, Outside.val32 O₇ (.inr (by omega_arith)) (by omega_arith), Outside.val32 O₆ (.inr (by omega_arith)) (by omega_arith)]
    exact Y₅
  obtain hm : u₈.mem.readW (off base accOff) 32 = cmask c :=
    BitVec.eq_of_toNat_eq ((k₈.word_eq (d := accOff)).trans W₇)
  -- The result cleared unless accepted, and written out.
  unfold exportResult
  refine maskResult_ok S₈.inp (c := c) hm fun u₉ O₉ V₉ K₉ => ?_
  obtain S₉ : Step Ex base bytes len args u₈ u₉ := Step.slot S₈.inp (by decide) O₉ K₉
  obtain Sall := ((((((S.trans S₅).trans S₆).trans S₇).trans S₈).trans S₉))
  refine WP.mono (writeResult_ok S₉.inp O.fit ((O.keep rfl Sall.keeps).wr) O.apart) fun t ⟨B, A, Ft, Kt⟩ =>
    ⟨?_, ?_, ?_, Sall.keeps.trans (Kt.mono (by decide))⟩
  · have a₉ : u₉.mem.readW (off base accOff) 32 = cmask c := by
      rw [show u₉.mem.readW (off base accOff) 32 = u₈.mem.readW (off base accOff) 32 from
        BitVec.eq_of_toNat_eq (O₉.w32 (d := accOff) (.inl (by omega_arith)) (by omega_arith)), hm]
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

end

end


/-! # `vg_ffdh_exchange` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Exchange

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : ExchangeABI s) : WrapABI Impl.Ffdh.X86.Exchange.args 11 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h; decide),
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

/-- The domain's, x's and y's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat
abbrev entryX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat
abbrev entryY (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat

/-- The output. -/
abbrev outR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Exchange.args)) Impl.Ffdh.X86.Exchange.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain, x and y; and write: the output. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 7) (arg s 8).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat ∧ InRegions wr (argumentPointer s 0) (arg s 1).toNat

/-- The inputs and the output, as the synthetic arguments give them, apart from the 96 bytes below
the frame. -/
theorem frame_geo {s : State} (A : ExchangeABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) (arg s 3).toNat rd wr ∧
    YGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) rd wr ∧
    XGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) (arg s 6).toNat rd wr ∧
    OutGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.Exchange.args (arg s) 8),
      pLenOf Impl.Ffdh.X86.Exchange.args s⟩ (below sp 96) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.Exchange.args (arg s) 10), (arg s 6).toNat⟩
      (below sp 96) := by
  have fb : argsFrame = 76 := rfl
  obtain hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have yR : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.yLen
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.outLen
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, low, st'])
  obtain espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega_using [fb, low, st'])
  obtain ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain sub40 : Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [low, st']), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, ⟨(ofn _).symm, ?_, ?_, ?_⟩,
    ⟨(ofn _).symm, A.xPos, A.xLen, A.xBound, hrd.2.2.1, A.xScratch⟩, ⟨?_, ?_, ?_⟩, ?_,
    (A.belowX.sub_left sub40).symm⟩
  · show (arg s 7).toNat + _ ≤ _
    rw [← yR]; exact A.yBound
  · show InRegions _ (argumentPointer s 7) _
    rw [← yR]; exact hrd.2.1
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← yR]; exact A.yScratch
  · show (arg s 0).toNat + _ ≤ _
    rw [← oR]; exact A.outBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← oR]; exact hrd.2.2.2
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.outScratch.symm
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← yR]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : ExchangeABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  obtain hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  obtain FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- What the contract asks of the result. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Ffdh.domainValid (arg s 4).toNat (entryDom s) = true →
    Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s), Spec.Rsa.os2ip (entryY s)⟩ = true →
      Spec.Rsa.written m (argumentPointer s 0) (arg s 1).toNat r
        (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)) (Spec.Rsa.os2ip (entryX s))
          (Spec.Rsa.os2ip (entryY s)))

/-- The result for valid inputs: `exchangeOp`. -/
theorem result_eq {len : Nat} {D : List Byte} {x y : Nat} {c : Bool} {m : Mem} {out : Addr} {r : BitVec 32}
    (hl : 0 < len) (hD : D.length = 2 * len ∨ D.length = 3 * len)
    (hc : c = (decide (y ^ x % safeM (Spec.Ffdh.domainOf len D).p < pm1 len (Spec.Ffdh.domainOf len D).p) &&
      decide (1 < y ^ x % safeM (Spec.Ffdh.domainOf len D).p)))
    (hr : r = BitVec.ofNat 32 c.toNat)
    (hb : Spec.Rsa.bytesAt m out len =
      Spec.Rsa.i2osp (if c then y ^ x % safeM (Spec.Ffdh.domainOf len D).p else 0) len)
    (v : Spec.Ffdh.domainValid len D = true) (pv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len D, y⟩ = true) :
    Spec.Rsa.written m out len r (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf len D) x y) := by
  obtain mv := VG.Proof.Ffdh.domainValid_mod v
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  obtain gt : 1 < (Spec.Ffdh.domainOf len D).p := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega_using [mv]
  obtain lo : 256 ^ (len - 1) ≤ (Spec.Ffdh.domainOf len D).p := by
    have := v; unfold Spec.Ffdh.domainValid at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  obtain hi : (Spec.Ffdh.domainOf len D).p < 256 ^ len := by
    have := VG.Proof.Bignum.os2ip_lt (D.take len)
    rw [List.length_take, Nat.min_eq_left (by omega_using [hD])] at this
    exact this
  rw [VG.Proof.Ffdh.exchangeOp_eq pv (by omega_using [mv]) (VG.Proof.Ffdh.octets_bitLength hl lo hi)]
  rw [safeM_of gt mv.1.1.1, pm1_of (by omega_using [mv])] at hc
  rw [safeM_of gt mv.1.1.1] at hb
  generalize y ^ x % (Spec.Ffdh.domainOf len D).p = z at hc hb ⊢
  by_cases e : 1 < z ∧ z < (Spec.Ffdh.domainOf len D).p - 1
  · have : c = true := by rw [hc]; simp [e.1, e.2]
    subst this
    simp only [e, and_self, ↓reduceIte] at hb ⊢
    exact ⟨hr, hb⟩
  · have : c = false := by
      rw [hc]
      by_cases a : z < (Spec.Ffdh.domainOf len D).p - 1
      · have b : ¬ 1 < z := fun b => e ⟨b, a⟩
        simp only [a, b, decide_true, decide_false, Bool.and_false]
      · simp only [a, decide_false, Bool.false_and]
    subst this
    simp only [e, ↓reduceIte, Bool.false_eq_true] at hb ⊢
    exact ⟨hr, by rw [hb, VG.Proof.Bignum.i2osp_zero']⟩

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : ExchangeABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.Exchange.args s) (wsSize Impl.Ffdh.X86.Exchange.args s)
      (pLenOf Impl.Ffdh.X86.Exchange.args s) (synth Impl.Ffdh.X86.Exchange.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.Exchange.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([outR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.Exchange.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.Exchange.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, Y, X, O, hy40, hx40⟩ := frame_geo A espf I.extra
  have yR : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.yLen
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.outLen
  obtain D : domBytes f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (arg s 3).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  obtain Yv : yv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s) =
      Spec.Rsa.os2ip (entryY s) := by
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _) = _
    rw [← yR]
    exact congrArg _ (frame_keep A Ft A.yScratch A.belowY (by have := A.yBound; omega_using []))
  obtain Xv : xv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (arg s 6).toNat = Spec.Rsa.os2ip (entryX s) :=
    congrArg _ (frame_keep A Ft A.xScratch A.belowX (by have := A.xBound; omega_using []))
  obtain Pv : comp f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s) 0 =
      (Spec.Ffdh.domainOf (pLenOf Impl.Ffdh.X86.Exchange.args s) (entryDom s)).p := by
    rw [comp_p f.mem _ (dlen := (arg s 3).toNat) (by have := G.dl; omega_using [this])]
    exact congrArg (fun d => (Spec.Ffdh.domainOf _ d).p) D
  refine WP.mono (body_ok I G Y X O hy40 hx40) fun t ⟨E, B, F, K⟩ =>
    ⟨fun v pv => ?_, by rw [List.singleton_append, outR, oR]; exact F, K⟩
  obtain Z : zv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s)
      (arg s 6).toNat = Spec.Rsa.os2ip (entryY s) ^ Spec.Rsa.os2ip (entryX s) %
        safeM (Spec.Ffdh.domainOf (pLenOf Impl.Ffdh.X86.Exchange.args s) (entryDom s)).p := by
    rw [zv, Yv, Xv, Pv]
  show Spec.Rsa.written _ _ (arg s 1).toNat _ _
  rw [oR]
  refine result_eq (len := (arg s 4).toNat) (D := entryDom s) (x := Spec.Rsa.os2ip (entryX s))
    (y := Spec.Rsa.os2ip (entryY s))
    (c := acc f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s)
      (arg s 6).toNat) (by have := A.pLen.1; omega_using [this])
    (by have := A.dLen; simpa [Spec.Rsa.bytesAt, Spec.Ffdh.domainLenValid] using this) ?_ E ?_ v pv
  · rw [acc, Z, Pv]
    rfl
  · refine B.trans ?_
    rw [Z]
    rfl

theorem operation_ok {s : State} (A : ExchangeABI s) :
    WP isa Impl.Ffdh.X86.Exchange.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  obtain hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [outR s])
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retOut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.outScratch.symm)
    (P := fun m e => spec s m e) fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.Exchange

module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Rows
public import VerifiedGarbage.Proof.Ffdh.X86_64.Pow
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH's context on x86-64: the comb's table

In the inner workspace for `p`, with `R² mod p` in `aR2`: entry 0
(Montgomery one) and entry 1 (`g R mod p`), then for each tooth `d = 2^j` its
entry, `rows` squares of the last, and the entries `d + i` for `0 < i < d`,
products of entry `i` and entry `d` (`table_ok`). Every entry is written to
its row of the context, and read back from there. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

/-- The table stage's public data: the working space, the inner
workspace's offset, the context and the comb's parameters. -/
structure TabP where
  B : Addr
  Z : Nat
  o : Nat
  w : Nat
  mi : BitVec 64
  cp : Addr
  P : Nat
  G : Nat
  bits : Nat

abbrev TabP.R (T : TabP) : Nat := 2 ^ (64 * T.w)
abbrev TabP.rows (T : TabP) : Nat := Spec.Rsa.FixedBaseComb.rows T.bits
abbrev TabP.n (T : TabP) : Nat := 3 + 34 * T.w

/-- `g^E R mod p`, in Montgomery form. -/
def TabP.M (T : TabP) (E : Nat) : Nat := Spec.Rsa.powMod T.G E T.P * T.R % T.P

/-- Entry `a`. -/
def TabP.entry (T : TabP) (a : Nat) : Nat := T.M (Spec.Rsa.FixedBaseComb.exponent T.bits a)

/-- What every step keeps: the inner workspace for `p`, the context's
pointer and row count in its header, and the context. -/
structure Env (T : TabP) (s : State) : Prop where
  mc : ModCtx s T.B T.Z T.o T.w T.mi T.P
  ctx : word s.mem (off T.B T.o) (8 * iCtx) = T.cp
  rows : word s.mem (off T.B T.o) (8 * iRows) = BitVec.ofNat 64 T.rows
  reg : CtxRegion s T.B T.Z T.cp T.n

/-- Memory outside the working space and the context is unchanged. -/
def Only (T : TabP) (m m' : Mem) : Prop := ∀ x, T.Z ≤ ofs T.B x → 8 * T.n ≤ ofs T.cp x → m' x = m x

theorem Only.refl (T : TabP) (m : Mem) : Only T m m := fun _ _ _ => rfl

theorem Only.trans {T : TabP} {m₁ m₂ m₃ : Mem} (h₁ : Only T m₁ m₂) (h₂ : Only T m₂ m₃) : Only T m₁ m₃ :=
  fun x hx hc => (h₂ x hx hc).trans (h₁ x hx hc)

/-- The ranges a step may change in the inner workspace: the counters and the
arrays but `aN`, `aR2` and `aOne`. -/
def innerR (w : Nat) : List (Nat × Nat) :=
  [(8 * 17, 8 * 15), (slot w aX, 3 * (8 * (w + 2))), (slot w aXm, 2 * (8 * (w + 2)))]

theorem innerR_ok (w : Nat) : ∀ r ∈ innerR w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 ∧
    (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
    (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1) ∧
    (r.1 + r.2 ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ r.1) := by
  intro r hr
  simp only [innerR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes, aX, aXm, aN, aOne, aR2] <;> omega

/-- `ModCtx` after a change of only `innerR`. -/
theorem _root_.VG.Proof.Ffdh.X86_64.ModCtx.of_inner {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (h : ModCtx s B Z o w mi X) (hf : Frm (off B o) (innerR w) s.mem t.mem) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : ModCtx t B Z o w mi X := by
  have hGn := h.sub.good.scr.nowrap
  have sR := slot_le (w := w) (show aR2 < 8 by decide)
  have eR : wv t.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    hf.wv_eq (fun r hr => by have := (innerR_ok w r hr).2.2.2.2; omega) (by omega)
  exact ⟨h.sub.of_frm hf (fun r hr => ⟨(innerR_ok w r hr).1, (innerR_ok w r hr).2.1⟩) hwr hdi,
    h.xv.of_frmA hGn (by have := h.w2; omega) hf (fun r hr => ⟨(innerR_ok w r hr).2.2.1, (innerR_ok w r hr).2.2.2.1⟩),
    by rw [eR]; exact h.r2l, by rw [eR]; exact h.r2, h.odd, h.x1, h.wide, h.w2, h.w28⟩

/-- A frame of fewer bytes. -/
theorem Frm.cover {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := fun x hx =>
  h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hc r hr
    have := hx r' hr'
    omega

/-- `ModCtx` when the working space is unchanged. -/
theorem _root_.VG.Proof.Ffdh.X86_64.ModCtx.of_outScr {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (h : ModCtx s B Z o w mi X) (hm : OutScr B Z s.mem t.mem) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : ModCtx t B Z o w mi X := by
  have hn := h.sub.scr.nowrap
  have hi := h.sub.hi
  have sN := slot_le (w := w) (show aN < 8 by decide)
  have sO := slot_le (w := w) (show aOne < 8 by decide)
  have sR := slot_le (w := w) (show aR2 < 8 by decide)
  have eR : wv t.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    OutScr.wvAt hm (by omega) hn
  refine ⟨SubCtx.of_outScr h.sub hm hwr hdi, ⟨?_, ?_, ?_⟩, by rw [eR]; exact h.r2l, by rw [eR]; exact h.r2, h.odd, h.x1,
    h.wide, h.w2, h.w28⟩
  · rw [OutScr.wvAt hm (by omega) hn]; exact h.xv.n
  · rw [OutScr.wordAt hm (by have := h.w2; omega) hn]; exact h.xv.inv
  · rw [OutScr.wvAt hm (by omega) hn]; exact h.xv.one

theorem Env.of_outScr {T : TabP} {s t : State} (h : Env T s) (hm : OutScr T.B T.Z s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : Env T t := by
  have hn := h.mc.sub.scr.nowrap
  have hi := h.mc.sub.hi
  have h8 := hdr_lt_slot T.w 8 (show 31 < 32 by decide)
  exact ⟨h.mc.of_outScr hm hwr hdi, by rw [OutScr.wordAt hm (by unfold iCtx sFn; omega) hn]; exact h.ctx,
    by rw [OutScr.wordAt hm (by unfold iRows sFn; omega) hn]; exact h.rows, h.reg.congr hrd hwr⟩

/-- A change of only `innerR`, inside the working space. -/
theorem Env.of_inner {T : TabP} {s t : State} (h : Env T s) (hf : Frm (off T.B T.o) (innerR T.w) s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hc : word t.mem (off T.B T.o) (8 * iCtx) = word s.mem (off T.B T.o) (8 * iCtx))
    (hr : word t.mem (off T.B T.o) (8 * iRows) = word s.mem (off T.B T.o) (8 * iRows)) : Env T t :=
  ⟨h.mc.of_inner hf hwr hdi, by rw [hc]; exact h.ctx, by rw [hr]; exact h.rows, h.reg.congr hrd hwr⟩

/-- A change of the inner workspace (below `slot w 8`) is inside the working space. -/
theorem inScr_of_inner {T : TabP} {s t : State} (h : Env T s) {rs : List (Nat × Nat)}
    (hf : Frm (off T.B T.o) rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot T.w 8) :
    InScr T.B T.Z s.mem t.mem ∧ (∀ i < 32, word t.mem T.B (8 * i) = word s.mem T.B (8 * i)) := by
  obtain ⟨h1, h2⟩ := VG.Proof.Ffdh.X86_64.child_frm h.mc.sub h.mc.wide hf
    (fun r hr' => by have := hr r hr'; unfold tabBytes; omega)
  exact ⟨h2, h1⟩

/-- A row is unchanged by a change inside the working space. -/
theorem row_of_inScr {T : TabP} {s t : State} (h : Env T s) (hm : InScr T.B T.Z s.mem t.mem) {j : Nat}
    (hj : 3 + T.w * (j + 1) ≤ T.n) : row t.mem T.cp T.w j = row s.mem T.cp T.w j :=
  row_congr fun i hi => Mem.readW_congr fun b hb => hm _ (by
    have e : off T.cp (24 + 8 * T.w * j + 8 * i) + BitVec.ofNat 64 b = off T.cp (24 + 8 * T.w * j + 8 * i + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    have e8 : 8 * T.w * j = 8 * (T.w * j) := Nat.mul_assoc _ _ _
    exact h.reg.out (by rw [Nat.mul_add] at hj; omega))

/-- A word of the context is unchanged by a change inside the working space. -/
theorem ctxWord_of_inScr {T : TabP} {s t : State} (h : Env T s) (hm : InScr T.B T.Z s.mem t.mem) {i : Nat}
    (hi : i < T.n) : word t.mem T.cp (8 * i) = word s.mem T.cp (8 * i) :=
  Mem.readW_congr fun b hb => hm _ (by
    have e : off T.cp (8 * i) + BitVec.ofNat 64 b = off T.cp (8 * i + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    exact h.reg.out (by omega))

theorem Only.of_inScr {T : TabP} {m m' : Mem} (h : InScr T.B T.Z m m') : Only T m m' :=
  fun x hx _ => h x hx

theorem Only.of_outScr_outside {T : TabP} {s : State} {m' : Mem} {o n : Nat}
    (h : Outside T.cp o n s.mem m') (hn : o + n ≤ 8 * T.n) : Only T s.mem m' :=
  fun x _ hc => h x (Or.inr (by omega))

/-- The ranges of `mm`'s writes are in `innerR`. -/
theorem mm_cover (w : Nat) {out : Nat} (ho : out = aX ∨ out = aXm ∨ out = aY) :
    ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w out, 8 * (w + 2))],
      ∃ r' ∈ innerR w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aX, aAcc]; omega,
      by simp only [slot, aX, aAcc]; omega⟩
  · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aX, aTmp]; omega,
      by simp only [slot, aX, aTmp]; omega⟩
  · rcases ho with rfl | rfl | rfl
    · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot]; omega,
        by simp only [slot]; omega⟩
    · exact ⟨(slot w aXm, 2 * (8 * (w + 2))), by simp [innerR], by simp only [slot]; omega,
        by simp only [slot]; omega⟩
    · exact ⟨(slot w aXm, 2 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aXm, aY]; omega,
        by simp only [slot, aXm, aY]; omega⟩

/-- What a step keeps outside the inner workspace and the context. -/
structure Kept (T : TabP) (s t : State) : Prop where
  only : Only T s.mem t.mem
  outer : ∀ i < 32, word t.mem T.B (8 * i) = word s.mem T.B (8 * i)
  hdr : ∀ i < 3, word t.mem T.cp (8 * i) = word s.mem T.cp (8 * i)

theorem Kept.refl (T : TabP) (s : State) : Kept T s s :=
  ⟨Only.refl _ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Kept.trans {T : TabP} {s t u : State} (h₁ : Kept T s t) (h₂ : Kept T t u) : Kept T s u :=
  ⟨h₁.only.trans h₂.only, fun i hi => (h₂.outer i hi).trans (h₁.outer i hi),
    fun i hi => (h₂.hdr i hi).trans (h₁.hdr i hi)⟩

/-- Montgomery multiplication in the table's environment. -/
theorem mm_env (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {out a b : Nat}
    (ho : out = aX ∨ out = aXm ∨ out = aY) (ha : a < 8) (hb : b < 8) (ha₁ : a ≠ aAcc) (ha₂ : a ≠ aTmp)
    (hb₁ : b ≠ aAcc) (hb₂ : b ≠ aTmp)
    (hbl : wv s.mem (off T.B T.o) (slot T.w b) T.w < T.P) :
    WP isa (Mo.mm out a b) s fun t => Env T t ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w < T.P ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w * T.R % T.P =
        wv s.mem (off T.B T.o) (slot T.w a) T.w * wv s.mem (off T.B T.o) (slot T.w b) T.w % T.P ∧
      Arrays (off T.B T.o) T.w [aAcc, aTmp, out] s.mem t.mem ∧
      (∀ j, 3 + T.w * (j + 1) ≤ T.n → row t.mem T.cp T.w j = row s.mem T.cp T.w j) ∧
      (∀ i, 17 ≤ i → i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)) ∧
      Kept T s t ∧ Keep mmRegs s t := by
  have hc := he.mc
  have hw2 := hc.w2
  have hw28 := hc.w28
  have hGn := hc.sub.good.scr.nowrap
  have hout : out < 8 := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₁ : out ≠ aAcc := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₂ : out ≠ aTmp := by rcases ho with rfl | rfl | rfl <;> decide
  refine WP.mono (Mo.mm_ok hc.sub.good (Nat.le_refl _) (by omega) (by omega) hout ha hb ho₁ ho₂ ha₁ hb₁
    hc.xv.inv (by rw [hc.xv.n]; exact hbl) ha₂ hb₂) fun t ⟨_, hl, hv, ha', k⟩ => ?_
  rw [hc.xv.n] at hl hv
  have hf : Frm (off T.B T.o) [(slot T.w aAcc, 8 * (T.w + 2)), (slot T.w aTmp, 8 * (T.w + 2)),
      (slot T.w out, 8 * (T.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  have hrng : ∀ r ∈ [(slot T.w aAcc, 8 * (T.w + 2)), (slot T.w aTmp, 8 * (T.w + 2)),
      (slot T.w out, 8 * (T.w + 2))], r.1 + r.2 ≤ slot T.w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact slot_le hout
  obtain ⟨hin, hout'⟩ := inScr_of_inner he hf hrng
  have hd : ∀ i, 17 ≤ i → i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i) :=
    fun i _ h2 => hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (hdr_lt_slot T.w aAcc h2)
      · exact Or.inl (hdr_lt_slot T.w aTmp h2)
      · exact Or.inl (hdr_lt_slot T.w out h2))
      (by have := hdr_lt_slot T.w 8 (show i < 32 from h2); omega)
  refine ⟨he.of_inner (Frm.cover hf (mm_cover T.w ho)) k.2.1 k.2.2 (k.gpr (by decide))
      (hd _ (by decide) (by decide)) (hd _ (by decide) (by decide)), hl, hv, ha',
    fun j hj => row_of_inScr he hin hj, hd, ⟨Only.of_inScr hin, hout', fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega)⟩,
    k⟩

/-- A row of the context in its environment. -/
abbrev RowFits (T : TabP) (j : Nat) : Prop := 3 + T.w * (j + 1) ≤ T.n

/-- Array `a` to row `j` in the table's environment. -/
theorem store_env {T : TabP} {s : State} (he : Env T s) {j a : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (ha : a < 8) (hj : j < 34) :
    WP isa (storeRow a) s fun t => Env T t ∧
      row t.mem T.cp T.w j = Spec.Rsa.toWords (wv s.mem (off T.B T.o) (slot T.w a) T.w) T.w ∧
      (∀ j', j' ≠ j → RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      OutScr T.B T.Z s.mem t.mem ∧ Kept T s t ∧ Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hc := he.mc
  have hn := hc.sub.scr.nowrap
  have hcn := he.reg.nowrap
  have hfit : 3 + T.w * (j + 1) ≤ T.n := by
    unfold TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega); omega
  refine WP.mono (storeRow_ok hc.sub he.ctx hax ha he.reg hfit (by have := hc.w2; omega) hc.w28)
    fun t ⟨hrow, ho, hos, k⟩ => ?_
  have e8 : 8 * T.w * j = 8 * (T.w * j) := Nat.mul_assoc _ _ _
  refine ⟨he.of_outScr hos k.2.1 k.2.2 (k.gpr (by decide)), hrow, fun j' hne hj' => ?_, hos,
    ⟨Only.of_outScr_outside ho (by unfold TabP.n at hfit ⊢; rw [Nat.mul_add] at hfit; omega),
      fun i hi => OutScr.word_eq hos (by have := hdr_lt_slot T.w 8 hi; have := hc.sub.lo; have := hc.sub.hi; omega) hn,
      fun i hi => ho.word (by omega) (by omega)⟩, k⟩
  have e8' : 8 * T.w * j' = 8 * (T.w * j') := Nat.mul_assoc _ _ _
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : T.w * (j' + 1) ≤ T.w * j := Nat.mul_le_mul_left _ (by omega)
    exact row_outside ho (Or.inl (by rw [Nat.mul_add] at this; omega)) (by unfold RowFits TabP.n at hj'; unfold TabP.n at hcn; have : 8 * T.w * (j' + 1) = 8 * (T.w * (j' + 1)) := Nat.mul_assoc _ _ _; omega)
  · have : T.w * (j + 1) ≤ T.w * j' := Nat.mul_le_mul_left _ (by omega)
    exact row_outside ho (Or.inr (by rw [Nat.mul_add] at this; omega)) (by unfold RowFits TabP.n at hj'; unfold TabP.n at hcn; have : 8 * T.w * (j' + 1) = 8 * (T.w * (j' + 1)) := Nat.mul_assoc _ _ _; omega)

/-- Row `j`, of value `V`, to array `a` in the table's environment. -/
theorem load_env {T : TabP} {s : State} (he : Env T s) {j a V : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (ha : a = aX ∨ a = aXm ∨ a = aY) (hj : j < 34) (hrow : row s.mem T.cp T.w j = Spec.Rsa.toWords V T.w)
    (hV : V < 2 ^ (64 * T.w)) :
    WP isa (loadRow a) s fun t => Env T t ∧ wv t.mem (off T.B T.o) (slot T.w a) T.w = V ∧
      (∀ b < 8, b ≠ a → wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      (∀ i, i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)) ∧
      Kept T s t ∧ Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hc := he.mc
  have hn := hc.sub.scr.nowrap
  have hGn := hc.sub.good.scr.nowrap
  have ha8 : a < 8 := by rcases ha with rfl | rfl | rfl <;> decide
  have hsa := slot_le (w := T.w) ha8
  have hfit : 3 + T.w * (j + 1) ≤ T.n := by
    unfold TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega); omega
  refine WP.mono (loadRow_ok hc.sub he.ctx hax ha8 he.reg hfit (by have := hc.w2; omega) hc.w28 hrow hV)
    fun t ⟨hv, ho, k⟩ => ?_
  have hf : Frm (off T.B T.o) [(slot T.w a, 8 * (T.w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot T.w a) (n' := 8 * (T.w + 2)) (Nat.le_refl _) (by omega)) (by simp)
  obtain ⟨hin, hout⟩ := inScr_of_inner he hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsa)
  have hd : ∀ i, i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i) :=
    fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot T.w a hi))
      (by have := hdr_lt_slot T.w 8 hi; omega)
  have hcov : ∀ r ∈ [(slot T.w a, 8 * (T.w + 2))], ∃ r' ∈ innerR T.w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
    intro r hr
    rw [List.mem_singleton.mp hr]
    rcases ha with rfl | rfl | rfl
    · exact ⟨(slot T.w aX, 3 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot]; omega,
        by simp only [slot]; omega⟩
    · exact ⟨(slot T.w aXm, 2 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot]; omega,
        by simp only [slot]; omega⟩
    · exact ⟨(slot T.w aXm, 2 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot, aXm, aY]; omega,
        by simp only [slot, aXm, aY]; omega⟩
  refine ⟨he.of_inner (Frm.cover hf hcov) k.2.1 k.2.2 (k.gpr (by decide)) (hd _ (by decide)) (hd _ (by decide)),
    hv, fun b hb hne => hf.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := slot_sep (w := T.w) hne; simp only; omega)
      (by have := slot_le (w := T.w) hb; omega),
    fun j' hj' => row_of_inScr he hin hj', hd,
    ⟨Only.of_inScr hin, hout, fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega)⟩, k⟩

/-- A store to an inner counter slot (not the context's pointer or row count). -/
theorem slot_env {T : TabP} {s : State} (he : Env T s) {i : Nat} (hi : 19 ≤ i) (hi' : i < 32) {t : State}
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) v) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) :
    Env T t ∧ word t.mem (off T.B T.o) (8 * i) = v ∧
      (∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i')) ∧
      (∀ b < 8, wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t := by
  have hc := he.mc
  have hGn := hc.sub.good.scr.nowrap
  have ho := writeW_outside s.mem (off T.B T.o) (d := 8 * i) v (by omega)
  rw [← hm] at ho
  have hf : Frm (off T.B T.o) [(8 * i, 8)] s.mem t.mem := Frm.of_outside ho (by simp)
  obtain ⟨hin, hout⟩ := inScr_of_inner he hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := hdr_lt_slot T.w 0 hi'; simp only [slot] at this ⊢; omega)
  have hcov : ∀ r ∈ [(8 * i, 8)], ∃ r' ∈ innerR T.w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
    intro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨(8 * 17, 8 * 15), by simp [innerR], by simp only; omega, by simp only; omega⟩
  have hd : ∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i') :=
    fun i' h1 h2 => ho.word (by omega) (by have := hdr_lt_slot T.w 8 h1; omega)
  refine ⟨he.of_inner (Frm.cover hf hcov) hrd hwr hdi (hd _ (by decide) (by unfold iCtx sFn; omega))
      (hd _ (by decide) (by unfold iRows sFn; omega)), by rw [hm]; exact word_writeW_self _ _ _ _, hd,
    fun b hb => hf.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := hdr_lt_slot T.w b hi'; simp only; omega)
      (by have := slot_le (w := T.w) hb; omega),
    fun j' hj' => row_of_inScr he hin hj',
    ⟨Only.of_inScr hin, hout, fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega)⟩⟩

/-! ## The table's values -/

theorem TabP.M_lt (T : TabP) (hP : 0 < T.P) (E : Nat) : T.M E < T.P := Nat.mod_lt _ hP

theorem TabP.M_lt_R (T : TabP) (hP : 0 < T.P) (hPR : T.P ≤ T.R) (E : Nat) : T.M E < 2 ^ (64 * T.w) :=
  Nat.lt_of_lt_of_le (T.M_lt hP E) hPR

/-- A Montgomery product of two entries. -/
theorem TabP.M_mul (T : TabP) (hodd : T.P % 2 = 1) {E F c : Nat} (hc : c < T.P)
    (h : c * T.R % T.P = T.M E * T.M F % T.P) : c = T.M (E + F) :=
  VG.Proof.Rsa.FixedBaseComb.mont_product_encoded (coprime_pow2 hodd _) hc rfl rfl h

theorem TabP.entry_zero (T : TabP) (h1 : 1 < T.P) : T.entry 0 = T.R % T.P := by
  unfold TabP.entry TabP.M
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_zero, powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt h1, Nat.one_mul]

theorem TabP.entry_one (T : TabP) : T.entry 1 = T.G * T.R % T.P := by
  unfold TabP.entry TabP.M
  have := VG.Proof.Rsa.FixedBaseComb.exponent_tooth T.bits 0 (by decide)
  simp only [Nat.pow_zero, Nat.zero_mul] at this
  rw [this, powMod_eq, Nat.pow_one, Nat.mod_mul_mod]

/-- The tooth `2^(j+1)`'s entry, `rows` squares of the tooth `2^j`'s. -/
theorem TabP.entry_tooth (T : TabP) {j : Nat} (hj : j < 4) :
    T.entry (2 ^ (j + 1)) = T.M (Spec.Rsa.FixedBaseComb.exponent T.bits (2 ^ j) * 2 ^ T.rows) := by
  unfold TabP.entry
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega),
    VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega), ← Nat.pow_add, Nat.succ_mul]

theorem TabP.entry_add (T : TabP) {j i : Nat} (hj : j < 5) (hi : i < 2 ^ j) :
    T.entry (2 ^ j + i) = T.M (Spec.Rsa.FixedBaseComb.exponent T.bits i + Spec.Rsa.FixedBaseComb.exponent T.bits (2 ^ j)) := by
  unfold TabP.entry
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth _ _ _ hj hi, VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ hj]

end VG.Proof.Ffdh.X86_64.Cached

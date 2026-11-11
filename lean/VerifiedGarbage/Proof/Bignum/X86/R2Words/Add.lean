module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Sub
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `R2Words` on x86: `t := t + M` if `t` is negative

`addBack` adds `M`'s `W'` words to `t`'s `W' + 1` under the mask of `t`'s
top bit, the carry a mask in `esi` (`addBack_ok`): `t' + 2^(32 (W' + 1)) c =
t + M` if `t ≥ 2^(32 (W' + 1)) / 2`, and `t' = t` otherwise.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- The mask of a bit. -/
abbrev bmask (b : Bool) : BitVec 32 := BitVec.ofNat 32 (if b then 2 ^ 32 - 1 else 0)

theorem bmask_add (b : Bool) : decide (2 ^ 32 ≤ (bmask b).toNat + (bmask b).toNat) = b := by
  cases b <;> rfl

theorem sbb_bmask (x : BitVec 32) (c : Bool) : x - x - (BitVec.ofBool c).setWidth 32 = bmask c := by
  rw [BitVec.sub_self]; cases c <;> rfl

theorem and_bmask (x : BitVec 32) (m : Bool) : (x &&& bmask m).toNat = if m then x.toNat else 0 := by
  exact and_mask x (m = true)

/-- A word of `addBack`, with `ebx` at `Mᵢ` (`a`), `ebp` at `tᵢ` (`tt`), the
mask `m` in `ecx` and the carry `c` in `esi`. -/
theorem addBody_ok {t : State} {base : Addr} {bytes a tt : Nat} {m c : Bool} (ws : Ws t base bytes)
    (pb : PtrAt t base .ebx a) (pp : PtrAt t base .ebp tt) (ha : a + 4 ≤ bytes) (ht : tt + 4 ≤ bytes)
    (hcx : t.gpr .ecx = bmask m) (hsi : t.gpr .esi = bmask c) :
    WP isa (.block addBody) t fun t' => ∃ c' : Bool, t'.gpr .esi = bmask c' ∧
      w32 t'.mem base tt + 2 ^ 32 * c'.toNat = (if m then w32 t.mem base a else 0) + w32 t.mem base tt + c.toNat ∧
      t'.mem = t.mem.writeW (off base tt) (BitVec.ofNat 32 (w32 t'.mem base tt)) ∧
      PtrAt t' base .ebx (a + 4) ∧ PtrAt t' base .ebp (tt + 4) ∧ t'.gpr .edi = t.gpr .edi - 4 ∧
      t'.zf = some (t.gpr .edi - 4 == 0) ∧ Keeps [.eax, .ebx, .esi, .ebp, .edi] t t' := by
  have nw := ws.nowrap
  simp only [addBody]
  refine wp_movS (readSrc_ptr ws pb (d := 0) (by omega)) fun t₁ U₁ _ => wp_logicS (Or.inl rfl) rfl fun t₂ U₂ => ?_
  refine wp_addS rfl fun t₃ U₃ c₃ => ?_
  have ws₃ := ws.of_wr (U₃.wr.trans (U₂.wr.trans U₁.wr))
  have pp₃ : PtrAt t₃ base .ebp tt := by
    rw [PtrAt, U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]; exact pp
  have si₂ : t₂.gpr .esi = bmask c := by rw [U₂.other _ (by decide), U₁.other _ (by decide), hsi]
  refine wp_adcS (readSrc_ptr ws₃ pp₃ (d := 0) (by omega)) (by rw [c₃, si₂, bmask_add]) fun t₄ U₄ c₄ => ?_
  have ws₄ := ws₃.of_wr U₄.wr
  have pp₄ : PtrAt t₄ base .ebp tt := by rw [PtrAt, U₄.other _ (by decide)]; exact pp₃
  refine wp_storeS (ea_ptr ws₄ pp₄ (d := 0) (by omega)) (ws_write ws₄ (by omega)) fun t₅ M₅ => ?_
  refine wp_sbbS rfl (by rw [M₅.cf]; exact c₄) fun t₆ U₆ _ => ?_
  refine wp_addS rfl fun t₇ U₇ _ => wp_addS rfl fun t₈ U₈ _ => wp_subZ rfl fun t₉ U₉ z₉ => WP.block_nil ?_
  have hA : (t₂.gpr .eax).toNat = if m then w32 t.mem base a else 0 := by
    rw [U₂.gpr, ite_eq_left rfl, U₁.gpr, U₁.other _ (by decide), hcx, and_bmask,
      Nat.add_zero]
  have m₃ : t₃.mem = t.mem := by rw [U₃.mem, U₂.mem, U₁.mem]
  have hv : (t₄.gpr .eax).toNat = ((if m then w32 t.mem base a else 0) + w32 t.mem base tt + c.toNat) % 2 ^ 32 := by
    rw [U₄.gpr, add3_toNat, U₃.other _ (by decide), hA, m₃, Nat.add_zero]
  have hm : t₉.mem = t.mem.writeW (off base tt) (t₄.gpr .eax) := by
    rw [U₉.mem, U₈.mem, U₇.mem, U₆.mem, M₅.mem, U₄.mem, m₃, Nat.add_zero]
  have hw : w32 t₉.mem base tt = (t₄.gpr .eax).toNat := by rw [hm, w32_write_self]
  have hA' : (if m then w32 t.mem base a else 0) < 2 ^ 32 := by
    split
    · exact (t.mem.readW _ 32).isLt
    · omega
  have ht' : w32 t.mem base tt < 2 ^ 32 := (t.mem.readW _ 32).isLt
  have hc : c.toNat < 2 := by cases c <;> decide
  refine ⟨decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t.mem.readW (off base (tt + 0)) 32).toNat + c.toNat), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.gpr, M₅.gpr, sbb_bmask]
    congr 2; rw [U₃.other _ (by decide), m₃]
  · rw [hw, hv, hA]
    simp only [Nat.add_zero]
    change _ = (if m then w32 t.mem base a else 0) + w32 t.mem base tt + c.toNat
    cases h : decide (2 ^ 32 ≤ (if m then w32 t.mem base a else 0) + w32 t.mem base tt + c.toNat) <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h <;> simp only [Bool.toNat_false, Bool.toNat_true] <;>
      omega
  · rw [hw, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]
  · have pb₆ : PtrAt t₆ base .ebx a := by
      rw [PtrAt, U₆.other _ (by decide), M₅.gpr, U₄.other _ (by decide), U₃.other _ (by decide),
        U₂.other _ (by decide), U₁.other _ (by decide)]; exact pb
    rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide), U₇.gpr, ptr_add pb₆]; rfl
  · have pp₆ : PtrAt t₆ base .ebp tt := by rw [PtrAt, U₆.other _ (by decide), M₅.gpr]; exact pp₄
    rw [PtrAt, U₉.other _ (by decide), U₈.gpr, U₇.other _ (by decide), ptr_add pp₆]; rfl
  · rw [U₉.gpr, U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr,
      U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  · rw [z₉, U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide), M₅.gpr,
      U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  · exact ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))).trans
      (((M₅.keeps _).trans (U₆.keeps.mono (by decide))).trans
      ((U₇.keeps.mono (by decide)).trans (U₈.keeps.mono (by decide))))).trans (U₉.keeps.mono (by decide))

theorem sub_bmask (x : BitVec 32) (c : Bool) : (x - bmask c).toNat = (x.toNat + c.toNat) % 2 ^ 32 := by
  have := x.isLt
  cases c <;> simp only [bmask, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> simp <;> omega

/-- `addBack`'s pointers, `ebx` at `M` and `ebp` at `t`, `edi = 4 W'`, the
mask of `t`'s top bit in `ecx` and no carry in `esi`. -/
theorem addHead_ok {s : State} {is : List Instr} {Q : State → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} (h : PcIn base bytes len args s)
    (kk : ∀ u, PtrAt u base .ebx (numAt len 0) → PtrAt u base .ebp (numAt len 5) →
      u.gpr .edi = BitVec.ofNat 32 (4 * wp len) →
      u.gpr .ecx = bmask (decide (2 ^ 31 ≤ w32 s.mem base (numAt len 5 + 4 * wp len))) → u.gpr .esi = bmask false →
      u.mem = s.mem → Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u → WP isa (.block is) u Q) :
    WP isa (.block (addHead ++ is)) s Q := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  simp only [addHead, List.append_assoc, List.cons_append, List.nil_append]
  refine slotPtr_ok (r := .ebx) (j := 0) (t := .edx) (by decide) (by decide) h.edi h.width h.upper
    (by decide) fun u₁ K₁ m₁ p₁ _ => ?_
  refine slotPtr_ok (r := .ebp) (j := 5) (t := .edx) (by decide) (by decide) (by rw [K₁.1 _ (by decide)]; exact h.edi)
      ((h.stack 1 (by decide)).keep K₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) |>.readSrc |>.trans
        (by rw [h.wLen])) h.upper (by decide) fun u₂ K₂ m₂ p₂ _ => ?_
  have K₁₂ : Keeps [.ebx, .edx, .ebp] s u₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  refine width4_ok ((h.stack 1 (by decide)).keep K₁₂ (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _)
    |>.readSrc |>.trans (by rw [h.wLen])) h.upper fun u₃ K₃ m₃ e₃ => ?_
  refine wp_movS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  have K₁₅ : Keeps [.eax, .ebx, .edx, .ebp, .edi] s u₅ :=
    ((K₁₂.mono (by decide)).trans (K₃.mono (by decide))).trans ((U₄.keeps.mono (by decide)).trans
      (U₅.keeps.mono (by decide)))
  have ws₅ : Ws u₅ base bytes := h.ws.of_wr K₁₅.2.2
  have pp₃ : PtrAt u₃ base .ebp (numAt len 5) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  have pa₅ : PtrAt u₅ base .eax (numAt len 5 + 4 * wp len) := by
    rw [PtrAt, U₅.gpr, U₄.gpr, U₄.other _ (by decide), BitVec.toNat_add, pp₃, e₃, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * wp len) (by omega)]
    omega
  refine wp_movS (readSrc_ptr ws₅ pa₅ (d := 0) (by omega)) fun u₆ U₆ _ => wp_addS rfl fun u₇ U₇ c₇ => ?_
  refine wp_sbbS rfl c₇ fun u₈ U₈ _ => wp_movS rfl fun u₉ U₉ _ => ?_
  have m₉ : u₉.mem = s.mem := by rw [U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, m₃, m₂, m₁]
  refine kk u₉ ?_ ?_ ?_ ?_ ?_ m₉ ?_
  · rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide),
      U₅.other _ (by decide), U₄.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  · rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide),
      U₅.other _ (by decide), U₄.other _ (by decide)]; exact pp₃
  · rw [U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide),
      U₅.other _ (by decide), U₄.other _ (by decide), e₃]
  · rw [U₉.other _ (by decide), U₈.gpr, sbb_bmask]
    congr 2
    rw [U₆.gpr, Nat.add_zero, U₅.mem, U₄.mem, m₃, m₂, m₁]
    exact propext ⟨fun h => by simp only [w32] at *; omega, fun h => by simp only [w32] at *; omega⟩
  · rw [U₉.gpr]; rfl
  · exact (K₁₅.mono (by decide)).trans ((((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))).trans
      ((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide)))))

/-- After words `0, …, j - 1` of `addBack` from `s` under the mask `m`, the
carry `c` in `esi`: `T'_j + 2^(32 j) c = T_j + m M_j`. -/
structure AddI (s : State) (base : Addr) (len : Nat) (m : Bool) (j : Nat) (u : State) : Prop where
  bx : PtrAt u base .ebx (numAt len 0 + 4 * j)
  bp : PtrAt u base .ebp (numAt len 5 + 4 * j)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (wp len - j))
  cx : u.gpr .ecx = bmask m
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u
  out : Outside base (numAt len 5) (4 * j) s.mem u.mem
  val : ∃ c : Bool, u.gpr .esi = bmask c ∧
    val32 u.mem base (numAt len 5) j + 2 ^ (32 * j) * c.toNat =
      val32 s.mem base (numAt len 5) j + if m then val32 s.mem base (numAt len 0) j else 0

theorem addStep_val {Tu c Ts Ms G w' c' A t : Nat} {m : Bool}
    (hI : Tu + G * c = Ts + if m then Ms else 0)
    (hv : w' + 2 ^ 32 * c' = (if m then A else 0) + t + c) :
    Tu + G * w' + G * 2 ^ 32 * c' = Ts + G * t + if m then Ms + G * A else 0 := by
  have e := congrArg (G * ·) hv
  simp only [Nat.mul_add] at e
  cases m <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hI hv e ⊢ <;> grind

/-- A word of `addBack`'s loop. -/
theorem addStep_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m : Bool} {j : Nat}
    (h : PcIn base bytes len args s) (hj : j < wp len) (I : AddI s base len m j u) :
    WP isa (.block addBody) u fun u' => u'.zf = some (decide (j + 1 = wp len)) ∧ AddI s base len m (j + 1) u' := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  have ws : Ws u base bytes := h.ws.of_wr I.keep.2.2
  obtain ⟨c, hsi, hval⟩ := I.val
  refine WP.mono (addBody_ok ws I.bx I.bp (by omega) (by omega) I.cx hsi)
    fun u' ⟨c', si', hv, hm, pb', pp', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := wp len) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have O' := writeW32_outside u.mem base (d := numAt len 5 + 4 * j) (BitVec.ofNat 32 (w32 u'.mem base
    (numAt len 5 + 4 * j))) (by omega)
  rw [← hm] at O'
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, by rw [K'.1 _ (by decide)]; exact I.cx, I.keep.trans (K'.mono (by decide)),
    ?_, c', si', ?_⟩⟩
  · rw [show numAt len 0 + 4 * (j + 1) = numAt len 0 + 4 * j + 4 by omega]; exact pb'
  · rw [show numAt len 5 + 4 * (j + 1) = numAt len 5 + 4 * j + 4 by omega]; exact pp'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · have hA : w32 u.mem base (numAt len 0 + 4 * j) = w32 s.mem base (numAt len 0 + 4 * j) :=
      I.out.w32 (.inl (by omega)) (by omega)
    have hT : w32 u.mem base (numAt len 5 + 4 * j) = w32 s.mem base (numAt len 5 + 4 * j) :=
      I.out.w32 (.inr (by omega)) (by omega)
    have hT' : val32 u'.mem base (numAt len 5) j = val32 u.mem base (numAt len 5) j :=
      O'.val32 (.inl (by omega)) (by omega)
    rw [hA, hT] at hv
    rw [val32_succ, val32_succ, val32_succ, hT', show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
    exact addStep_val hval hv

/-- `addBack`'s loop: words `0, …, W' - 1`. -/
theorem addLoop_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {m : Bool}
    (h : PcIn base bytes len args s) (I : AddI s base len m 0 u) :
    WP isa (.loop (.block addBody) .ne) u fun u' => AddI s base len m (wp len) u' := by
  have hl := h.lower
  have hw : 1 ≤ wp len := by simp only [wp]; omega
  refine WP.loop (M := isa) (fun n u => ∃ j, n = wp len - j ∧ j < wp len ∧ AddI s base len m j u) ?_ _ u
    ⟨0, rfl, by omega, I⟩
  rintro n u ⟨j, rfl, hj, I⟩
  refine WP.mono (addStep_ok h hj I) fun u' ⟨z, I'⟩ => ?_
  by_cases e : j + 1 = wp len
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wp len - (j + 1),
      by omega, j + 1, rfl, by omega, I'⟩

/-- `addBack`: `t' + 2^(32 (W' + 1)) c = t + M` if `t`'s top bit is set, `t`
otherwise, over `M`'s `W'` words. -/
theorem addBack_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa addBack s fun t => ∃ c, c < 2 ∧
      val32 t.mem base (numAt len 5) (wp len + 1) + 2 ^ (32 * (wp len + 1)) * c =
        val32 s.mem base (numAt len 5) (wp len + 1) +
          (if 2 ^ 31 ≤ w32 s.mem base (numAt len 5 + 4 * wp len) then val32 s.mem base (numAt len 0) (wp len) else 0) ∧
      Outside base (numAt len 5) (4 * (wp len + 1)) s.mem t.mem ∧ Keeps k6 s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  unfold addBack
  simp only [seqs]
  rw [← List.append_nil addHead]
  refine WP.seq (addHead_ok h fun u pb pp di cx si mu K => WP.block_nil ?_)
  refine WP.seq (WP.mono (addLoop_ok h (u := u) ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact pb,
    by rw [Nat.mul_zero, Nat.add_zero]; exact pp, by rw [Nat.sub_zero]; exact di, cx, K,
    by rw [mu]; exact Outside.refl _ _ _ _, false, si, by simp [val32]⟩) fun u' I => ?_)
  obtain ⟨c, hsi, hval⟩ := I.val
  have ws : Ws u' base bytes := h.ws.of_wr I.keep.2.2
  have ca := (h.stack 4 (by decide)).keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  simp only [addTop]
  refine wp_movS (readSrc_ptr ws I.bp (d := 0) (by omega)) fun t₁ U₁ _ => wp_subS rfl fun t₂ U₂ _ => ?_
  have ws₂ := ws.of_wr (U₂.wr.trans U₁.wr)
  have pp₂ : PtrAt t₂ base .ebp (numAt len 5 + 4 * wp len) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact I.bp
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 0) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  have K₃ : Keeps [.eax] u' t₃ := ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (M₃.keeps _)
  have m₃ : t₃.mem = u'.mem.writeW (off base (numAt len 5 + 4 * wp len)) (t₂.gpr .eax) := by
    rw [M₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  have O₃ := writeW32_outside u'.mem base (d := numAt len 5 + 4 * wp len) (t₂.gpr .eax) (by omega)
  rw [← m₃] at O₃
  refine wp_movS (ca.keep K₃ (by decide) (O₃.mono (by omega) (by omega))).readSrc fun t₄ U₄ _ => WP.block_nil ?_
  have hx : (t₂.gpr .eax).toNat = (w32 s.mem base (numAt len 5 + 4 * wp len) + c.toNat) % 2 ^ 32 := by
    rw [U₂.gpr, U₁.other .esi (by decide), hsi, sub_bmask, U₁.gpr, Nat.add_zero]
    congr 2
    exact I.out.w32 (.inr (by omega)) (by omega)
  have hc : c.toNat < 2 := by cases c <;> decide
  have htw : w32 s.mem base (numAt len 5 + 4 * wp len) < 2 ^ 32 := (s.mem.readW _ 32).isLt
  refine ⟨(w32 s.mem base (numAt len 5 + 4 * wp len) + c.toNat) / 2 ^ 32, by omega, ?_, ?_, ?_⟩
  · have hT : val32 t₄.mem base (numAt len 5) (wp len) = val32 u'.mem base (numAt len 5) (wp len) := by
      rw [U₄.mem]; exact O₃.val32 (.inl (by omega)) (by omega)
    rw [val32_succ, hT, U₄.mem, m₃, w32_write_self, hx, val32_succ s.mem, show 32 * (wp len + 1) = 32 * wp len + 32 by omega,
      Nat.pow_add]
    simp only [decide_eq_true_eq] at hval
    generalize (if 2 ^ 31 ≤ w32 s.mem base (numAt len 5 + 4 * wp len) then val32 s.mem base (numAt len 0) (wp len)
      else 0) = Z at *
    generalize 2 ^ (32 * wp len) = G at *
    have e := Nat.mod_add_div (w32 s.mem base (numAt len 5 + 4 * wp len) + c.toNat) (2 ^ 32)
    have e2 := congrArg (G * ·) e
    simp only [Nat.mul_add] at e2
    grind
  · rw [U₄.mem]
    exact (I.out.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega))
  · refine ⟨fun r hr => ?_, by rw [U₄.rd, K₃.2.1, I.keep.2.1], by rw [U₄.wr, K₃.2.2, I.keep.2.2]⟩
    by_cases e : r = .edi
    · subst e; rw [U₄.gpr, h.edi_eq]
    · have e' : r = .esp := by revert hr e; cases r <;> decide
      subst e'; rw [U₄.other _ (by decide), K₃.1 _ (by decide), I.keep.1 _ (by decide)]

/-! ## `copyBack` -/

/-- After words `0, …, j - 1` of `copyBack` from `s`. -/
structure CopyI (s : State) (base : Addr) (len j : Nat) (u : State) : Prop where
  si : PtrAt u base .esi (numAt len 5 + 4 * j)
  bp : PtrAt u base .ebp (numAt len 4 + 4 * j)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (wp len - j))
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u
  out : Outside base (numAt len 4) (4 * j) s.mem u.mem
  val : val32 u.mem base (numAt len 4) j = val32 s.mem base (numAt len 5) j

theorem copyStep_ok {s u : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {j : Nat}
    (h : PcIn base bytes len args s) (hj : j < wp len) (I : CopyI s base len j u) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) u fun u' =>
      u'.zf = some (decide (j + 1 = wp len)) ∧ CopyI s base len (j + 1) u' := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have f5 := (h.fits (j := 5) (by decide)).2
  have hwp := wp_le_nw (len := len)
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  have ws : Ws u base bytes := h.ws.of_wr I.keep.2.2
  refine wp_movS (readSrc_ptr ws I.si (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  have ws₁ := ws.of_wr U₁.wr
  have pp₁ : PtrAt u₁ base .ebp (numAt len 4 + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.bp
  refine wp_storeS (ea_ptr ws₁ pp₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subZ rfl fun u₅ U₅ z₅ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := wp len) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have di₄ : u₄.gpr .edi = u.gpr .edi := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₅ : u₅.mem = u.mem.writeW (off base (numAt len 4 + 4 * j)) (u.mem.readW (off base (numAt len 5 + 4 * j)) 32) := by
    rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero, Nat.add_zero]
  have O := writeW32_outside u.mem base (d := numAt len 4 + 4 * j) (u.mem.readW (off base (numAt len 5 + 4 * j)) 32)
    (by omega)
  rw [← m₅] at O
  refine ⟨by rw [z₅, di₄, hc.2], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := numAt len 5 + 4 * j)
      (by rw [PtrAt, M₂.gpr, U₁.other _ (by decide)]; exact I.si)]
    congr 2
  · rw [PtrAt, U₅.other _ (by decide), U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := numAt len 4 + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact pp₁)]
    congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, di₄, hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact I.keep.trans (((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))))
  · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
  · rw [val32_succ, val32_succ, O.val32 (.inl (by omega)) (by omega), I.val, m₅, w32_write_self]
    congr 2
    exact I.out.w32 (.inr (by omega)) (by omega)

/-- `copyBack`: `t`'s `W'` words into `x`. -/
theorem copyBack_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) :
    WP isa copyBack s fun t => val32 t.mem base (numAt len 4) (wp len) = val32 s.mem base (numAt len 5) (wp len) ∧
      Outside base (numAt len 4) (4 * wp len) s.mem t.mem ∧ Keeps k6 s t := by
  have nw := h.scratch.nowrap
  have dims := h.dimensions
  have hl := h.lower
  have hw : 1 ≤ wp len := by simp only [wp]; omega
  have hwp := wp_le_nw (len := len)
  have f5 := (h.fits (j := 5) (by decide)).2
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp [numAt, numOff]
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp [numAt, numOff]
  unfold copyBack
  simp only [seqs, List.append_assoc]
  refine WP.seq (slotPtr_ok (r := .esi) (j := 5) (t := .edx) (by decide) (by decide) h.edi h.width h.upper
    (by decide) fun u₁ K₁ m₁ p₁ _ => ?_)
  refine slotPtr_ok (r := .ebp) (j := 4) (t := .edx) (by decide) (by decide) (by rw [K₁.1 _ (by decide)]; exact h.edi)
      ((h.stack 1 (by decide)).keep K₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _) |>.readSrc |>.trans
        (by rw [h.wLen])) h.upper (by decide) fun u₂ K₂ m₂ p₂ _ => ?_
  have K₁₂ : Keeps [.edx, .esi, .ebp] s u₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  rw [← List.append_nil (width4 .edi)]
  refine width4_ok ((h.stack 1 (by decide)).keep K₁₂ (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _)
    |>.readSrc |>.trans (by rw [h.wLen])) h.upper fun u₃ K₃ m₃ e₃ => WP.block_nil ?_
  have I₀ : CopyI s base len 0 u₃ :=
    ⟨(by rw [Nat.mul_zero, Nat.add_zero, PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁),
    (by rw [Nat.mul_zero, Nat.add_zero, PtrAt, K₃.1 _ (by decide)]; exact p₂),
    by rw [Nat.sub_zero, e₃], (K₁₂.mono (by decide)).trans (K₃.mono (by decide)),
    by rw [m₃, m₂, m₁]; exact Outside.refl _ _ _ _, by simp [val32]⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun u => CopyI s base len (wp len) u)
    (fun n u => ∃ j, n = wp len - j ∧ j < wp len ∧ CopyI s base len j u) ?_ _ u₃ ⟨0, rfl, by omega, I₀⟩)
    fun u I => ?_)
  · rintro n u ⟨j, rfl, hj, I⟩
    refine WP.mono (copyStep_ok h hj I) fun u' ⟨z, I'⟩ => ?_
    by_cases e : j + 1 = wp len
    · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
    · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wp len - (j + 1),
        by omega, j + 1, rfl, by omega, I'⟩
  have ca := (h.stack 4 (by decide)).keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  refine wp_movS ca.readSrc fun t U _ => WP.block_nil ⟨by rw [U.mem]; exact I.val, by rw [U.mem]; exact I.out, ?_⟩
  refine ⟨fun r hr => ?_, by rw [U.rd, I.keep.2.1], by rw [U.wr, I.keep.2.2]⟩
  by_cases e : r = .edi
  · subst e; rw [U.gpr, h.edi_eq]
  · have e' : r = .esp := by revert hr e; cases r <;> decide
    subst e'; rw [U.other _ (by decide), I.keep.1 _ (by decide)]

end VG.Proof.Bignum.X86.R2Words

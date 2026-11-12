module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Sub
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the word steps' proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # `WordModRt` on i686: `t := t + m` if negative, and `t` back

`addBack` (`addBack_ok`): the mask of `t`'s top bit, `R2Words`' `addBody`
over `m`'s `W'` words and the carry into word `W'`; `copyBack`
(`copyBack_ok`): `t`'s `W'` words into `r`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Proof.Bignum.X86.R2Words (bmask sbb_bmask sub_bmask addStep_val)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `addBack`'s pointers, `ebx` at `m` and `ebp` at `t`, `edi = 4 W'`, the mask of `t`'s top bit
in `ecx` and no carry in `esi`. -/
theorem addHead_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N) {ml a m t : Nat}
    (hm : MLen s B Z ml a) (hmN : m < N) (ht : t < N) (hw : wq a + 1 ≤ kw len + 2)
    (kk : ∀ u, PtrAt u B .ebx (arr (kw len) m) → PtrAt u B .ebp (arr (kw len) t) →
      u.gpr .edi = BitVec.ofNat 32 (4 * wq a) →
      u.gpr .ecx = bmask (decide (2 ^ 31 ≤ w32 s.mem B (arr (kw len) t + 4 * wq a))) → u.gpr .esi = bmask false →
      u.mem = s.mem → Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u → WP isa (.block is) u Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.addHead L ml m t ++ is)) s Q := by
  have nw := h.ws.workspace.nowrap
  have fm := h.ws.arr_fit hmN
  have ft := h.ws.arr_fit ht
  simp only [S] at fm ft
  simp only [VG.Impl.Rsa.X86.WordModRt.addHead, List.append_assoc, List.cons_append, List.nil_append]
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := m) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok ((lenSrc h).keep K₁ (by decide) m₁) h.lenLe edi₁ (r := .ebp) (t := .edx) (j := t) (by decide)
    (by decide) (by omega) fun u₂ K₂ m₂ p₂ _ => ?_
  have K₁₂ : Keeps [.ebx, .edx, .ebp] s u₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  refine width4_ok (hm.keep K₁₂ (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _)) fun u₃ K₃ m₃ e₃ => ?_
  refine wp_movS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  have K₁₅ : Keeps [.eax, .ebx, .edx, .ebp, .edi] s u₅ :=
    ((K₁₂.mono (by decide)).trans (K₃.mono (by decide))).trans ((U₄.keeps.mono (by decide)).trans
      (U₅.keeps.mono (by decide)))
  have ws₅ : Ws u₅ B Z := h.rt.of_wr K₁₅.2.2
  have pp₃ : PtrAt u₃ B .ebp (arr (kw len) t) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  have pa₅ : PtrAt u₅ B .eax (arr (kw len) t + 4 * wq a) := by
    rw [PtrAt, U₅.gpr, U₄.gpr, U₄.other _ (by decide), BitVec.toNat_add, pp₃, e₃, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * wq a) (by have := hm.le; omega)]
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

/-- After words `0, …, j - 1` of `addBack` from `s` under the mask `c`, the carry `c'` in `esi`:
`T'_j + 2^(32 j) c' = T_j + c M_j`, for `m` at `mo` and `t` at `to`. -/
structure AddI (s : State) (B : Addr) (mo to W : Nat) (c : Bool) (j : Nat) (u : State) : Prop where
  bx : PtrAt u B .ebx (mo + 4 * j)
  bp : PtrAt u B .ebp (to + 4 * j)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (W - j))
  cx : u.gpr .ecx = bmask c
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u
  out : Outside B to (4 * j) s.mem u.mem
  val : ∃ c' : Bool, u.gpr .esi = bmask c' ∧
    val32 u.mem B to j + 2 ^ (32 * j) * c'.toNat = val32 s.mem B to j + if c then val32 s.mem B mo j else 0

/-- A word of `addBack`'s loop. -/
theorem addStep_ok {s u : State} {bytes mo to W : Nat} {c : Bool} {j : Nat} (ws : Ws s B bytes)
    (g : SubGeo B bytes mo mo to W) (hj : j < W) (I : AddI s B mo to W c j u) :
    WP isa (.block VG.Impl.Bignum.X86.R2Words.addBody) u fun u' => u'.zf = some (decide (j + 1 = W)) ∧
      AddI s B mo to W c (j + 1) u' := by
  have nw := g.nw
  have gm := g.m; have gt := g.t; have gmt := g.mt
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  obtain ⟨c₀, hsi, hval⟩ := I.val
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.addBody_ok wsu I.bx I.bp (by omega) (by omega) I.cx hsi)
    fun u' ⟨c', si', hv, hm, pb', pp', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := W) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have O' := writeW32_outside u.mem B (d := to + 4 * j) (BitVec.ofNat 32 (w32 u'.mem B (to + 4 * j))) (by omega)
  rw [← hm] at O'
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, by rw [K'.1 _ (by decide)]; exact I.cx, I.keep.trans (K'.mono (by decide)),
    ?_, c', si', ?_⟩⟩
  · rw [show mo + 4 * (j + 1) = mo + 4 * j + 4 by omega]; exact pb'
  · rw [show to + 4 * (j + 1) = to + 4 * j + 4 by omega]; exact pp'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · have hA : w32 u.mem B (mo + 4 * j) = w32 s.mem B (mo + 4 * j) := I.out.w32 (by omega) (by omega)
    have hT : w32 u.mem B (to + 4 * j) = w32 s.mem B (to + 4 * j) := I.out.w32 (.inr (by omega)) (by omega)
    have hT' : val32 u'.mem B to j = val32 u.mem B to j := O'.val32 (.inl (by omega)) (by omega)
    rw [hA, hT] at hv
    rw [val32_succ, val32_succ, val32_succ, hT', show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
    exact addStep_val hval hv

/-- `addBack`'s loop: words `0, …, W' - 1`. -/
theorem addLoop_ok {s u : State} {bytes mo to W : Nat} {c : Bool} (ws : Ws s B bytes)
    (g : SubGeo B bytes mo mo to W) (I : AddI s B mo to W c 0 u) :
    WP isa (.loop (.block VG.Impl.Bignum.X86.R2Words.addBody) .ne) u fun u' => AddI s B mo to W c W u' := by
  have hw := g.w2
  refine WP.loop (M := isa) (fun n u => ∃ j, n = W - j ∧ j < W ∧ AddI s B mo to W c j u) ?_ _ u
    ⟨0, rfl, by omega, I⟩
  rintro n u ⟨j, rfl, hj, I⟩
  refine WP.mono (addStep_ok ws g hj I) fun u' ⟨z, I'⟩ => ?_
  by_cases e : j + 1 = W
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], W - (j + 1),
      by omega, j + 1, rfl, by omega, I'⟩

/-- `addBack ml m t`: `t' + 2^(32 (W' + 1)) c = t + m` if `t`'s top bit is set, `t` otherwise,
over `m`'s `W'` words. -/
theorem addBack_ok {s : State} (h : RtWs L s B Z len N) {ml a m t : Nat} (hm : MLen s B Z ml a)
    (hmN : m < N) (ht : t < N) (hmt : m ≠ t) (h2 : 2 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.addBack L ml m t) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [t] [] s.mem v.mem ∧
      (∃ c, c < 2 ∧
        val32 v.mem B (arr (kw len) t) (wq a + 1) + 2 ^ (32 * (wq a + 1)) * c =
          val32 s.mem B (arr (kw len) t) (wq a + 1) +
            (if 2 ^ 31 ≤ w32 s.mem B (arr (kw len) t + 4 * wq a) then val32 s.mem B (arr (kw len) m) (wq a) else 0)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fm := h.ws.arr_fit hmN
  have ft := h.ws.arr_fit ht
  simp only [S] at fm ft
  have ws := h.rt
  have g : SubGeo B Z (arr (kw len) m) (arr (kw len) m) (arr (kw len) t) (wq a) :=
    ⟨nw, by omega, by omega, by omega,
      by have := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hmt; simp only [S] at this; omega,
      by have := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hmt; simp only [S] at this; omega, h2⟩
  unfold VG.Impl.Rsa.X86.WordModRt.addBack
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  rw [← List.append_nil (VG.Impl.Rsa.X86.WordModRt.addHead L ml m t)]
  refine WP.seq (addHead_ok h hm hmN ht (by omega) fun u pb pp di cx si mu K => WP.block_nil ?_)
  refine WP.seq (WP.mono (addLoop_ok ws g (u := u) ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact pb,
    by rw [Nat.mul_zero, Nat.add_zero]; exact pp, by rw [Nat.sub_zero]; exact di, cx, K,
    by rw [mu]; exact Outside.refl _ _ _ _, false, si, by simp [val32]⟩) fun u' I => ?_)
  obtain ⟨c, hsi, hval⟩ := I.val
  have wsu : Ws u' B Z := ws.of_wr I.keep.2.2
  have ca := h.wsArg.keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  simp only [VG.Impl.Rsa.X86.WordModRt.addTop, restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr wsu I.bp (d := 0) (by omega)) fun t₁ U₁ _ => wp_subS rfl fun t₂ U₂ _ => ?_
  have ws₂ := wsu.of_wr (U₂.wr.trans U₁.wr)
  have pp₂ : PtrAt t₂ B .ebp (arr (kw len) t + 4 * wq a) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact I.bp
  refine wp_storeS (ea_ptr ws₂ pp₂ (d := 0) (by omega)) (ws_write ws₂ (by omega)) fun t₃ M₃ => ?_
  have K₃ : Keeps [.eax] u' t₃ := ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (M₃.keeps _)
  have m₃ : t₃.mem = u'.mem.writeW (off B (arr (kw len) t + 4 * wq a)) (t₂.gpr .eax) := by
    rw [M₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  have O₃ := writeW32_outside u'.mem B (d := arr (kw len) t + 4 * wq a) (t₂.gpr .eax) (by omega)
  rw [← m₃] at O₃
  refine wp_movS (ca.keep K₃ (by decide) (O₃.mono (by omega) (by omega))).readSrc fun t₄ U₄ _ => WP.block_nil ?_
  have hx : (t₂.gpr .eax).toNat = (w32 s.mem B (arr (kw len) t + 4 * wq a) + c.toNat) % 2 ^ 32 := by
    rw [U₂.gpr, U₁.other .esi (by decide), hsi, sub_bmask, U₁.gpr, Nat.add_zero]
    congr 2
    exact I.out.w32 (.inr (by omega)) (by omega)
  have hc : c.toNat < 2 := by cases c <;> decide
  have htw : w32 s.mem B (arr (kw len) t + 4 * wq a) < 2 ^ 32 := (s.mem.readW _ 32).isLt
  have Ot : Outside B (arr (kw len) t) (4 * (wq a + 1)) s.mem t₄.mem := by
    rw [U₄.mem]; exact (I.out.mono (by omega) (by omega)).trans (O₃.mono (by omega) (by omega))
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t₄ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((I.keep.trans ((K₃.mono (by decide)).trans (U₄.keeps.mono (by decide)))).mono (by decide))
      (U₄.gpr.trans h.edi_eq.symm)
  refine ⟨h.keep Kall (by decide) (by decide) (Ot.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr (d := 0) (by simpa using Ot) (by simp only [S]; omega) (by simp),
    ⟨(w32 s.mem B (arr (kw len) t + 4 * wq a) + c.toNat) / 2 ^ 32, by omega, ?_⟩, Kall⟩
  have hT : val32 t₄.mem B (arr (kw len) t) (wq a) = val32 u'.mem B (arr (kw len) t) (wq a) := by
    rw [U₄.mem]; exact O₃.val32 (.inl (by omega)) (by omega)
  rw [val32_succ, hT, U₄.mem, m₃, w32_write_self, hx, val32_succ s.mem,
    show 32 * (wq a + 1) = 32 * wq a + 32 by omega, Nat.pow_add]
  simp only [decide_eq_true_eq] at hval
  generalize (if 2 ^ 31 ≤ w32 s.mem B (arr (kw len) t + 4 * wq a) then val32 s.mem B (arr (kw len) m) (wq a)
    else 0) = Z' at *
  generalize 2 ^ (32 * wq a) = G at *
  have e := Nat.mod_add_div (w32 s.mem B (arr (kw len) t + 4 * wq a) + c.toNat) (2 ^ 32)
  have e2 := congrArg (G * ·) e
  simp only [Nat.mul_add] at e2
  grind

/-! ## `copyBack` -/

/-- After words `0, …, j - 1` of `copyBack` from `s`, `t` at `to` into `r` at `xo`. -/
structure CopyI (s : State) (B : Addr) (xo to W j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (to + 4 * j)
  bp : PtrAt u B .ebp (xo + 4 * j)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (W - j))
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp, .edi] s u
  out : Outside B xo (4 * j) s.mem u.mem
  val : val32 u.mem B xo j = val32 s.mem B to j

theorem copyStep_ok {s u : State} {bytes mo xo to W j : Nat} (ws : Ws s B bytes) (g : SubGeo B bytes mo xo to W)
    (hj : j < W) (I : CopyI s B xo to W j u) :
    WP isa (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) u fun u' =>
      u'.zf = some (decide (j + 1 = W)) ∧ CopyI s B xo to W (j + 1) u' := by
  have nw := g.nw
  have gx := g.x; have gt := g.t; have gxt := g.xt
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  refine wp_movS (readSrc_ptr wsu I.si (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  have ws₁ := wsu.of_wr U₁.wr
  have pp₁ : PtrAt u₁ B .ebp (xo + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.bp
  refine wp_storeS (ea_ptr ws₁ pp₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subZ rfl fun u₅ U₅ z₅ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := W) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have di₄ : u₄.gpr .edi = u.gpr .edi := by
    rw [U₄.other _ (by decide), U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₅ : u₅.mem = u.mem.writeW (off B (xo + 4 * j)) (u.mem.readW (off B (to + 4 * j)) 32) := by
    rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero, Nat.add_zero]
  have O := writeW32_outside u.mem B (d := xo + 4 * j) (u.mem.readW (off B (to + 4 * j)) 32) (by omega)
  rw [← m₅] at O
  refine ⟨by rw [z₅, di₄, hc.2], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ptr_add (s := u₂) (x := to + 4 * j)
      (by rw [PtrAt, M₂.gpr, U₁.other _ (by decide)]; exact I.si)]
    congr 2
  · rw [PtrAt, U₅.other _ (by decide), U₄.gpr, U₃.other _ (by decide), ptr_add (s := u₂) (x := xo + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact pp₁)]
    congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [U₅.gpr, di₄, hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact I.keep.trans (((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      (((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))))
  · exact (I.out.mono (by omega) (by omega)).trans (O.mono (by omega) (by omega))
  · rw [val32_succ, val32_succ, O.val32 (.inl (by omega)) (by omega), I.val, m₅, w32_write_self]
    congr 2
    exact I.out.w32 (by omega) (by omega)

/-- `copyBack ml r t`: `t`'s `W'` words into `r`. -/
theorem copyBack_ok {s : State} (h : RtWs L s B Z len N) {ml a r t : Nat} (hm : MLen s B Z ml a)
    (hr : r < N) (ht : t < N) (hrt : r ≠ t) (h2 : 2 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.copyBack L ml r t) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [r] [] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) r) (wq a) = val32 s.mem B (arr (kw len) t) (wq a) ∧
      Outside B (arr (kw len) r) (4 * wq a) s.mem v.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fr := h.ws.arr_fit hr
  have ft := h.ws.arr_fit ht
  simp only [S] at fr ft
  have ws := h.rt
  have g : SubGeo B Z (arr (kw len) r) (arr (kw len) r) (arr (kw len) t) (wq a) :=
    ⟨nw, by omega, by omega, by omega,
      by have := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hrt; simp only [S] at this; omega,
      by have := VG.Proof.Rsa.X86.Keys.arr_disj (w := kw len) hrt; simp only [S] at this; omega, h2⟩
  unfold VG.Impl.Rsa.X86.WordModRt.copyBack
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs, List.append_assoc]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .esi) (t := .edx) (j := t) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok ((lenSrc h).keep K₁ (by decide) m₁) h.lenLe edi₁ (r := .ebp) (t := .edx) (j := r) (by decide)
    (by decide) (by omega) fun u₂ K₂ m₂ p₂ _ => ?_
  have K₁₂ : Keeps [.edx, .esi, .ebp] s u₂ := (K₁.mono (by decide)).trans (K₂.mono (by decide))
  rw [← List.append_nil (VG.Impl.Rsa.X86.WordModRt.width4 ml .edi)]
  refine width4_ok (hm.keep K₁₂ (by decide) (by rw [m₂, m₁]; exact Outside.refl _ _ _ _)) fun u₃ K₃ m₃ e₃ =>
    WP.block_nil ?_
  have I₀ : CopyI s B (arr (kw len) r) (arr (kw len) t) (wq a) 0 u₃ :=
    ⟨(by rw [Nat.mul_zero, Nat.add_zero, PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁),
    (by rw [Nat.mul_zero, Nat.add_zero, PtrAt, K₃.1 _ (by decide)]; exact p₂),
    by rw [Nat.sub_zero, e₃], (K₁₂.mono (by decide)).trans (K₃.mono (by decide)),
    by rw [m₃, m₂, m₁]; exact Outside.refl _ _ _ _, by simp [val32]⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun u => CopyI s B (arr (kw len) r) (arr (kw len) t) (wq a) (wq a) u)
    (fun n u => ∃ j, n = wq a - j ∧ j < wq a ∧ CopyI s B (arr (kw len) r) (arr (kw len) t) (wq a) j u) ?_ _ u₃
      ⟨0, rfl, by omega, I₀⟩) fun u I => ?_)
  · rintro n u ⟨j, rfl, hj, I⟩
    refine WP.mono (copyStep_ok ws g hj I) fun u' ⟨z, I'⟩ => ?_
    by_cases e : j + 1 = wq a
    · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
    · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], wq a - (j + 1),
        by omega, j + 1, rfl, by omega, I'⟩
  have ca := h.wsArg.keep I.keep (by decide) (I.out.mono (by omega) (by omega))
  unfold restoreEdi
  refine wp_movS ca.readSrc fun v U _ => WP.block_nil ?_
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .esi, .ebp])
      ((I.keep.trans (U.keeps.mono (by decide))).mono (by decide)) (U.gpr.trans h.edi_eq.symm)
  have Ov : Outside B (arr (kw len) r) (4 * wq a) s.mem v.mem := by rw [U.mem]; exact I.out
  exact ⟨h.keep Kall (by decide) (by decide) (Ov.mono (Nat.zero_le _) (by omega)),
    Keep.of_arr (d := 0) (by simpa using Ov) (by simp only [S]; omega) (by simp), by rw [U.mem]; exact I.val, Ov, Kall⟩

end VG.Proof.Rsa.X86.WordRt

module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.Omega

/-! # `WordModRt` on i686: products

A word of a row (`mulBody_ok`): `[o] := [o] + aᵢ b_j + c`, its high word the
next carry; a row (`mulRow_ok`): `[o]` from word `j` on, `w + 1` words, plus
`a b_j`; `mulWide_ok`: the product of two numbers over `2 w` words; and
`mulShort_ok`: a number times the low two words of another.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The block of a row's word. -/
abbrev mulBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0), .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
    .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

/-- A word of a row, with `esi` at `aᵢ` (`xa`), `ebp` at `oᵢ` (`xo`), `b_j` in `ecx` and the carry
in `ebx`: `o'ᵢ + 2^32 c' = aᵢ b_j + c + oᵢ`. -/
theorem mulBody_ok {t : State} {bytes xa xo : Nat} (ws : Ws t B bytes) (pa : PtrAt t B .esi xa)
    (po : PtrAt t B .ebp xo) (ha : xa + 4 ≤ bytes) (ho : xo + 4 ≤ bytes) :
    WP isa (.block mulBody) t fun t' =>
      w32 t'.mem B xo + 2 ^ 32 * (t'.gpr .ebx).toNat =
        w32 t.mem B xa * (t.gpr .ecx).toNat + (t.gpr .ebx).toNat + w32 t.mem B xo ∧
      t'.mem = t.mem.writeW (off B xo) (BitVec.ofNat 32 (w32 t'.mem B xo)) ∧
      PtrAt t' B .esi (xa + 4) ∧ PtrAt t' B .ebp (xo + 4) ∧ t'.gpr .edi = t.gpr .edi - 4 ∧
      t'.zf = some (t.gpr .edi - 4 == 0) ∧ Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t' := by
  have nw := ws.nowrap
  simp only [mulBody]
  refine wp_movS (readSrc_ptr ws pa (d := 0) (by omega)) fun t₁ U₁ _ => wp_mul fun t₂ U₂ => ?_
  refine wp_addS rfl fun t₃ U₃ c₃ => wp_adcS rfl c₃ fun t₄ U₄ _ => ?_
  have ws₄ := ws.of_wr (U₄.wr.trans (U₃.wr.trans (U₂.wr.trans U₁.wr)))
  have po₄ : PtrAt t₄ B .ebp xo := by
    rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide) (by decide),
      U₁.other _ (by decide)]; exact po
  refine wp_addS (readSrc_ptr ws₄ po₄ (d := 0) (by omega)) fun t₅ U₅ c₅ => wp_adcS rfl c₅ fun t₆ U₆ _ => ?_
  have ws₆ := ws₄.of_wr (U₆.wr.trans U₅.wr)
  have po₆ : PtrAt t₆ B .ebp xo := by rw [PtrAt, U₆.other _ (by decide), U₅.other _ (by decide)]; exact po₄
  refine wp_storeS (ea_ptr ws₆ po₆ (d := 0) (by omega)) (ws_write ws₆ (by omega)) fun t₇ M₇ => ?_
  refine wp_movS rfl fun t₈ U₈ _ => wp_addS rfl fun t₉ U₉ _ => wp_addS rfl fun t₁₀ U₁₀ _ =>
    wp_subZ rfl fun t₁₁ U₁₁ z₁₁ => WP.block_nil ?_
  -- The values.
  have hA : (t₁.gpr .eax).toNat = w32 t.mem B xa := by rw [U₁.gpr, Nat.add_zero]
  have hq : t₁.gpr .ecx = t.gpr .ecx := U₁.other _ (by decide)
  have hc : t₂.gpr .ebx = t.gpr .ebx := by rw [U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]
  have hb : w32 t.mem B xa * (t.gpr .ecx).toNat / 2 ^ 32 < 2 ^ 32 - 1 :=
    (mul_words (t.mem.readW (off B xa) 32) (t.gpr .ecx)).2
  have lo₂ : (t₂.gpr .eax).toNat = w32 t.mem B xa * (t.gpr .ecx).toNat % 2 ^ 32 := by
    rw [U₂.eax, hA, hq, BitVec.toNat_ofNat]
  have hi₂ : (t₂.gpr .edx).toNat = w32 t.mem B xa * (t.gpr .ecx).toNat / 2 ^ 32 := by
    rw [U₂.edx, hA, hq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have m₆ : t₆.mem = t.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have hO : (t₄.mem.readW (off B (xo + 0)) 32).toNat = w32 t.mem B xo := by
    rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  -- `lo₃ + 2^32 c₃ = lo₂ + c`, `hi₄ = hi₂ + c₃`, `lo₅ + 2^32 c₅ = lo₃ + o`, `hi₆ = hi₄ + c₅`.
  have e₃ := VG.Proof.Bignum.X86.R2Words.add32_toNat (t₂.gpr .eax) (t₂.gpr .ebx)
  have e₅ := VG.Proof.Bignum.X86.R2Words.add32_toNat (t₄.gpr .eax) (t₄.mem.readW (off B (xo + 0)) 32)
  have hc32 := (t.gpr .ebx).isLt
  have ho32 : w32 t.mem B xo < 2 ^ 32 := (t.mem.readW _ 32).isLt
  have hca : (t₃.gpr .eax).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat =
      (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat := by rw [U₃.gpr]; exact e₃
  have h₄ : (t₄.gpr .edx).toNat = (t₂.gpr .edx).toNat +
      (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat := by
    rw [U₄.gpr, add3_toNat, U₃.other .edx (by decide), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
    apply Nat.mod_eq_of_lt
    have := Bool.toNat_le (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat))
    rw [hi₂]; omega
  have ea₄ : t₄.gpr .eax = t₃.gpr .eax := U₄.other _ (by decide)
  rw [ea₄] at e₅
  have hcb : (t₅.gpr .eax).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ (t₃.gpr .eax).toNat + w32 t.mem B xo)).toNat =
      (t₃.gpr .eax).toNat + w32 t.mem B xo := by rw [U₅.gpr, ea₄, ← hO]; exact e₅
  have hdiv := Nat.div_add_mod (w32 t.mem B xa * (t.gpr .ecx).toNat) (2 ^ 32)
  have hP : w32 t.mem B xa * (t.gpr .ecx).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by have := (t.mem.readW (off B xa) 32).isLt; simp only [w32]; omega) (by omega)
  rw [hc, lo₂] at hca
  have hl3 := (t₃.gpr .eax).isLt
  have hl5 := (t₅.gpr .eax).isLt
  generalize hc1 : (decide (2 ^ 32 ≤ w32 t.mem B xa * (t.gpr .ecx).toNat % 2 ^ 32 + (t.gpr .ebx).toNat)).toNat = c1
    at hca h₄
  generalize hc2 : (decide (2 ^ 32 ≤ (t₃.gpr .eax).toNat + w32 t.mem B xo)).toNat = c2 at hcb
  have c1b : c1 ≤ 1 := hc1 ▸ Bool.toNat_le _
  have c2b : c2 ≤ 1 := hc2 ▸ Bool.toNat_le _
  obtain ⟨P, hPe⟩ : ∃ P, P = w32 t.mem B xa * (t.gpr .ecx).toNat := ⟨_, rfl⟩
  rw [← hPe] at hdiv hP hca hi₂
  have hsum : 2 ^ 32 * (P / 2 ^ 32 + c1 + c2) + (t₅.gpr .eax).toNat = P + (t.gpr .ebx).toNat + w32 t.mem B xo := by
    omega
  have hX : P / 2 ^ 32 + c1 + c2 < 2 ^ 32 := by
    by_contra hcon
    have h1 := Nat.mul_le_mul_left (2 ^ 32) (Nat.le_of_not_lt hcon)
    have h2 : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
    omega
  have e1 : (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat = c1 := by
    rw [lo₂, hc, ← hc1]
  have e4 : (t₄.gpr .edx).toNat = P / 2 ^ 32 + c1 := by rw [h₄, hi₂, e1]
  have h₆ : (t₆.gpr .edx).toNat = (t₄.gpr .edx).toNat + c2 := by
    rw [U₆.gpr, add3_toNat, U₅.other .edx (by decide), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, ea₄,
      hO, hc2]
    apply Nat.mod_eq_of_lt
    rw [e4]; exact hX
  have m₇ : t₇.mem = t.mem.writeW (off B xo) (t₆.gpr .eax) := by rw [M₇.mem, m₆, Nat.add_zero]
  have m₁₁ : t₁₁.mem = t₇.mem := by rw [U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem]
  have bx : t₁₁.gpr .ebx = t₆.gpr .edx := by
    rw [U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.gpr, M₇.gpr]
  have K : Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t₁₁ := by
    refine ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))).trans
      (((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))).trans (M₇.keeps _))).trans
      (((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide))).trans
      ((U₁₀.keeps.mono (by decide)).trans (U₁₁.keeps.mono (by decide))))
  have pa₇ : PtrAt t₇ B .esi xa := by
    rw [PtrAt, M₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pa
  have po₇ : PtrAt t₇ B .ebp xo := by rw [PtrAt, M₇.gpr]; exact po₆
  have di₇ : t₇.gpr .edi = t.gpr .edi := by
    rw [M₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, K⟩
  · rw [m₁₁, m₇, w32_write_self, bx, U₆.other .eax (by decide), h₆, e4, ← hPe]
    omega
  · rw [m₁₁, m₇, w32_write_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [PtrAt, U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.gpr, U₈.other _ (by decide), ptr_add pa₇]; rfl
  · rw [PtrAt, U₁₁.other _ (by decide), U₁₀.gpr, U₉.other _ (by decide), U₈.other _ (by decide), ptr_add po₇]; rfl
  · rw [U₁₁.gpr, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), di₇]
  · rw [z₁₁, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), di₇]

/-- After words `0, …, i - 1` of a row from `s`, for `a` at `xa` and the row of `o` at `xo`:
`O'_i + 2^(32 i) c = A_i b + O_i`, the carry `c` in `ebx`. -/
structure RowI (s : State) (B : Addr) (xa xo W : Nat) (i : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (xa + 4 * i)
  bp : PtrAt u B .ebp (xo + 4 * i)
  di : u.gpr .edi = BitVec.ofNat 32 (4 * (W - i))
  cx : u.gpr .ecx = s.gpr .ecx
  keep : Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] s u
  out : Outside B xo (4 * i) s.mem u.mem
  val : val32 u.mem B xo i + 2 ^ (32 * i) * (u.gpr .ebx).toNat =
    val32 s.mem B xa i * (s.gpr .ecx).toNat + val32 s.mem B xo i

theorem rowStep_val {T C A b O G w c' a o : Nat}
    (hI : T + G * C = A * b + O) (hv : w + 2 ^ 32 * c' = a * b + C + o) :
    T + G * w + G * 2 ^ 32 * c' = (A + G * a) * b + (O + G * o) := by
  have e := congrArg (G * ·) hv
  simp only [Nat.mul_add] at e
  grind

/-- A word of a row. -/
theorem rowStep_ok {s u : State} {bytes xa xo W i : Nat} (ws : Ws s B bytes)
    (gw : B.toNat + bytes ≤ 2 ^ 32) (ga : xa + 4 * W ≤ bytes) (go : xo + 4 * (W + 1) ≤ bytes)
    (gsep : xa + 4 * W ≤ xo ∨ xo + 4 * (W + 1) ≤ xa) (hW : W < 2 ^ 30)
    (hi : i < W) (I : RowI s B xa xo W i u) :
    WP isa (.block mulBody) u fun u' => u'.zf = some (decide (i + 1 = W)) ∧ RowI s B xa xo W (i + 1) u' := by
  have wsu : Ws u B bytes := ws.of_wr I.keep.2.2
  refine WP.mono (mulBody_ok wsu I.si I.bp (by omega) (by omega))
    fun u' ⟨hv, hm, pa', po', di', z', K'⟩ => ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := W) (x := u.gpr .edi)
    (by rw [I.di, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hi
  have O' := writeW32_outside u.mem B (d := xo + 4 * i) (BitVec.ofNat 32 (w32 u'.mem B (xo + 4 * i))) (by omega)
  rw [← hm] at O'
  refine ⟨by rw [z', hc.2], ⟨?_, ?_, ?_, by rw [K'.1 _ (by decide)]; exact I.cx, I.keep.trans K', ?_, ?_⟩⟩
  · rw [show xa + 4 * (i + 1) = xa + 4 * i + 4 by omega]; exact pa'
  · rw [show xo + 4 * (i + 1) = xo + 4 * i + 4 by omega]; exact po'
  · apply BitVec.eq_of_toNat_eq
    rw [di', hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact (I.out.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))
  · have hA : w32 u.mem B (xa + 4 * i) = w32 s.mem B (xa + 4 * i) := I.out.w32 (by omega) (by omega)
    have hO : w32 u.mem B (xo + 4 * i) = w32 s.mem B (xo + 4 * i) := I.out.w32 (.inr (by omega)) (by omega)
    have hT : val32 u'.mem B xo i = val32 u.mem B xo i := O'.val32 (.inl (by omega)) (by omega)
    rw [hA, hO, I.cx] at hv
    rw [val32_succ, val32_succ, val32_succ, hT, show 32 * (i + 1) = 32 * i + 32 by omega, Nat.pow_add]
    exact rowStep_val I.val hv

/-- A row's loop: words `0, …, W - 1`. -/
theorem rowLoop_ok {s u : State} {bytes xa xo W : Nat} (ws : Ws s B bytes)
    (gw : B.toNat + bytes ≤ 2 ^ 32) (ga : xa + 4 * W ≤ bytes) (go : xo + 4 * (W + 1) ≤ bytes)
    (gsep : xa + 4 * W ≤ xo ∨ xo + 4 * (W + 1) ≤ xa) (hW : W < 2 ^ 30) (hW1 : 1 ≤ W)
    (I : RowI s B xa xo W 0 u) :
    WP isa (.loop (.block mulBody) .ne) u fun u' => RowI s B xa xo W W u' := by
  refine WP.loop (M := isa) (fun n u => ∃ i, n = W - i ∧ i < W ∧ RowI s B xa xo W i u) ?_ _ u ⟨0, rfl, by omega, I⟩
  rintro n u ⟨i, rfl, hi, I⟩
  refine WP.mono (rowStep_ok ws gw ga go gsep hW hi I) fun u' ⟨z, I'⟩ => ?_
  by_cases e : i + 1 = W
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], W - (i + 1),
      by omega, i + 1, rfl, by omega, I'⟩

open VG.Impl.Rsa.X86.WordModRt (oJ) in
theorem oJ_val : oJ = 96 := rfl

open VG.Impl.Rsa.X86.WordModRt (oJ)

/-- The rows' count a row compares with. -/
abbrev rowsN (len : Nat) : Option Nat → Nat
  | none => kw len
  | some k => k

/-- What changed only inside arrays `o` and `o + 1` is a `Keep` of them. -/
theorem keep_of_two {w : Nat} {js ds : List Nat} {m m' : Mem} {o e n : Nat} (h : Outside B e n m m')
    (h1 : arr w o ≤ e) (h2 : e + n ≤ arr w o + 2 * S w) (ho : o ∈ js) (ho1 : o + 1 ∈ js) :
    Keep B w js ds m m' := by
  intro x hx
  have mem : ∀ j ∈ js, (arr w j, S w) ∈ VG.Proof.Rsa.X86.Keys.ranges w js ds := fun j hj => by
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map]; exact .inl ⟨j, hj, rfl⟩
  have a0 := hx _ (mem _ ho); have a1 := hx _ (mem _ ho1)
  rw [VG.Proof.Rsa.X86.Keys.arr_succ] at a1
  exact h x (by simp only at a0 a1; omega)

/-- Row `j` (at `oJ`): `[o]` from word `j`, `w + 1` words, becomes `[o]`'s words `j, …, j + w - 1`
plus `a b_j`, across arrays `o` and `o + 1`; the count `j + 1`, compared with `rowsN`. -/
theorem mulRow_ok {s : State} (h : RtWs L s B Z len N) {o a b j : Nat} {rows : Option Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1)
    (hj : slot s.mem B oJ = j) (hjw : j < kw len) (hR : ∀ k, rows = some k → k < 2 ^ 32) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) o + 4 * j) (kw len + 1) =
        num s.mem B (kw len) a * w32 s.mem B (arr (kw len) b + 4 * j) +
          val32 s.mem B (arr (kw len) o + 4 * j) (kw len) ∧
      (∀ i, (i < j ∨ j + kw len + 1 ≤ i) → i < 2 * (kw len + 2) →
        w32 v.mem B (arr (kw len) o + 4 * i) = w32 s.mem B (arr (kw len) o + 4 * i)) ∧
      slot v.mem B oJ = j + 1 ∧ v.zf = some (decide (j + 1 = rowsN len rows)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have nw := h.ws.workspace.nowrap
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hdr := h.ws.hdr_le
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  have wpos := h.kw_pos
  simp only [S] at fo fa fb
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  have eo1 : arr (kw len) (o + 1) = arr (kw len) o + 4 * (kw len + 2) := by
    rw [VG.Proof.Rsa.X86.Keys.arr_succ]
  have gsep : arr (kw len) a + 4 * kw len ≤ arr (kw len) o + 4 * j ∨
      arr (kw len) o + 4 * j + 4 * (kw len + 1) ≤ arr (kw len) a := by
    rcases Nat.lt_or_gt_of_ne hao with hlt | hgt
    · have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) hlt; simp only [S] at this; omega
    · have h2 : o + 1 < a := by omega
      have := VG.Proof.Rsa.X86.Keys.arr_end (w := kw len) h2; simp only [S] at this; omega
  have ws := h.rt
  unfold VG.Impl.Rsa.X86.WordModRt.mulRow
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebx) (t := .edx) (j := b) (by decide) (by decide)
    (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₁.ws.workspace (d := oJ) (by rw [oJ_val]; omega)) fun u₂ U₂ _ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  have e₄ : (u₄.gpr .eax).toNat = 4 * j := by
    rw [U₄.gpr, BitVec.toNat_add, U₃.gpr, BitVec.toNat_add, U₂.gpr, m₁]
    change (((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32 + ((w32 s.mem B oJ) + w32 s.mem B oJ) % 2 ^ 32) % 2 ^ 32 = _
    rw [show w32 s.mem B oJ = j from hj]; omega
  have p₅ : PtrAt u₅ B .ebx (arr (kw len) b + 4 * j) := by
    rw [PtrAt, U₅.gpr, BitVec.toNat_add, U₄.other .ebx (by decide), U₃.other .ebx (by decide),
      U₂.other .ebx (by decide), p₁, e₄]
    have := B.isLt; omega
  have K₅ : Keeps [.eax, .ebx, .edx] s u₅ := (K₁.mono (by decide)).trans
    (((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans
      ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  refine wp_movS (readSrc_ptr (ws.of_keeps K₅) p₅ (d := 0) (by omega)) fun u₆ U₆ _ => ?_
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx] s u₆ := (K₅.mono (by decide)).trans (U₆.keeps.mono (by decide))
  have h₆ := h.keep K₆ (by decide) (by decide) (by rw [U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₆) h₆.lenLe h₆.edi (r := .ebp) (t := .edx) (j := o) (by decide) (by decide)
    (by omega) fun u₇ K₇ m₇ p₇ _ => wp_addS rfl fun u₈ U₈ _ => ?_
  have p₈ : PtrAt u₈ B .ebp (arr (kw len) o + 4 * j) := by
    rw [PtrAt, U₈.gpr, BitVec.toNat_add, p₇, K₇.1 .eax (by decide), U₆.other .eax (by decide), U₅.other .eax (by decide), e₄]
    have := B.isLt; omega
  have K₈ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₈ := (K₆.mono (by decide)).trans
    ((K₇.mono (by decide)).trans (U₈.keeps.mono (by decide)))
  have h₈ := h.keep K₈ (by decide) (by decide) (by rw [U₈.mem, m₇, U₆.mem, m₅]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h₈) h₈.lenLe h₈.edi (r := .esi) (t := .edx) (j := a) (by decide) (by decide)
    (by omega) fun u₉ K₉ m₉ p₉ _ => bytesB_ok ((lenSrc h₈).keep K₉ (by decide) m₉) h.lenLe fun u₁₀ K₁₀ m₁₀ e₁₀ =>
      wp_movS rfl fun u₁₁ U₁₁ _ => WP.block_nil ?_
  have m₁₁ : u₁₁.mem = s.mem := by rw [U₁₁.mem, m₁₀, m₉, U₈.mem, m₇, U₆.mem, m₅]
  have bj : (u₁₁.gpr .ecx).toNat = w32 s.mem B (arr (kw len) b + 4 * j) := by
    rw [U₁₁.other _ (by decide), K₁₀.1 _ (by decide), K₉.1 _ (by decide), U₈.other _ (by decide),
      K₇.1 _ (by decide), U₆.gpr, m₅, Nat.add_zero]
  have K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s u₁₁ := (K₈.mono (by decide)).trans
    (((K₉.mono (by decide)).trans (K₁₀.mono (by decide))).trans (U₁₁.keeps.mono (by decide)))
  have I₀ : RowI u₁₁ B (arr (kw len) a) (arr (kw len) o + 4 * j) (kw len) 0 u₁₁ :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide)]; exact p₉,
      by rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₁₁.other _ (by decide), K₁₀.1 _ (by decide),
        K₉.1 _ (by decide)]; exact p₈,
      by apply BitVec.eq_of_toNat_eq
         rw [U₁₁.other _ (by decide), e₁₀, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      rfl, Keeps.refl _ _, Outside.refl _ _ _ _, by rw [U₁₁.gpr]; simp [val32]⟩
  refine WP.seq (WP.mono (rowLoop_ok (ws.of_keeps K₁₁) nw (by omega) (by omega) gsep (by omega) wpos I₀)
    fun u I => ?_)
  -- The carry, `edi`, and the count.
  have wsu : Ws u B Z := (ws.of_keeps K₁₁).of_wr I.keep.2.2
  refine wp_storeS (ea_ptr wsu I.bp (d := 0) (by omega)) (ws_write wsu (by omega)) fun t₁ M₁ => ?_
  have O₁ := writeW32_outside u.mem B (d := arr (kw len) o + 4 * j + 4 * kw len + 0) (u.gpr .ebx) (by omega)
  rw [← M₁.mem] at O₁
  have Orow : Outside B (arr (kw len) o + 4 * j) (4 * (kw len + 1)) s.mem t₁.mem := by
    rw [← m₁₁]; exact (I.out.mono (by omega) (by omega)).trans (O₁.mono (by omega) (by omega))
  have K₁ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t₁ :=
    K₁₁.trans ((I.keep.mono (by decide)).trans (M₁.keeps _))
  have ca := h.wsArg.keep K₁ₜ (by decide) (Orow.mono (Nat.zero_le _) (by omega))
  simp only [restoreEdi, List.cons_append, List.nil_append]
  refine wp_movS ca.readSrc fun t₂ T₂ _ => ?_
  have K₂ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₂ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp, .esi])
      ((K₁ₜ.trans (T₂.keeps.mono (by decide))).mono (by decide)) (T₂.gpr.trans h.edi_eq.symm)
  have Z₂ : Outside B 0 Z s.mem t₂.mem := by rw [T₂.mem]; exact Orow.mono (Nat.zero_le _) (by omega)
  have h₂ : RtWs L t₂ B Z len N := h.keep K₂ₜ (by decide) (by decide) Z₂
  have hoJ : oJ + 4 ≤ arr (kw len) o + 4 * j := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have oj₂ : slot t₂.mem B oJ = j := by
    rw [slot, T₂.mem, Orow.w32 (.inl hoJ) (by rw [oJ_val]; omega)]; exact hj
  refine wp_movS (readSrc_sc h₂.ws.workspace (d := oJ) (by rw [oJ_val]; omega)) fun t₃ T₃ _ =>
    wp_addS rfl fun t₄ T₄ _ => ?_
  have e₄' : (t₄.gpr .eax).toNat = j + 1 := by
    rw [T₄.gpr, BitVec.toNat_add, T₃.gpr]
    change (w32 t₂.mem B oJ + 1) % 2 ^ 32 = _
    rw [show w32 t₂.mem B oJ = j from oj₂]; omega
  have K₄ₜ : Keeps [.eax] t₂ t₄ := (T₃.keeps.mono (by decide)).trans (T₄.keeps.mono (by decide))
  have h₄ := h₂.keep K₄ₜ (by decide) (by decide) (by rw [T₄.mem, T₃.mem]; exact Outside.refl _ _ _ _)
  refine wp_storeS (h₄.ws.workspace.ea (by rw [oJ_val]; omega)) (h₄.ws.workspace.write (by rw [oJ_val]; omega))
    fun t₅ M₅ => ?_
  have O₅ := writeW32_outside t₄.mem B (d := oJ) (t₄.gpr .eax) (by rw [oJ_val]; omega)
  rw [← M₅.mem] at O₅
  have h₅ : RtWs L t₅ B Z len N := h₄.keep (M₅.keeps []) (by decide) (by decide) (O₅.mono (Nat.zero_le _) (by rw [oJ_val]; omega))
  have K₅ₜ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₅ := K₂ₜ.trans ((K₄ₜ.mono (by decide)).trans (M₅.keeps _))
  have m₄₂ : t₄.mem = t₂.mem := by rw [T₄.mem, T₃.mem]
  -- What holds whatever the compare.
  have post : ∀ v : State, Keeps [.ecx] t₅ v → v.mem = t₅.mem → v.zf = some (decide (j + 1 = rowsN len rows)) →
      RtWs L v B Z len N ∧ Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) o + 4 * j) (kw len + 1) =
        num s.mem B (kw len) a * w32 s.mem B (arr (kw len) b + 4 * j) +
          val32 s.mem B (arr (kw len) o + 4 * j) (kw len) ∧
      (∀ i, (i < j ∨ j + kw len + 1 ≤ i) → i < 2 * (kw len + 2) →
        w32 v.mem B (arr (kw len) o + 4 * i) = w32 s.mem B (arr (kw len) o + 4 * i)) ∧
      slot v.mem B oJ = j + 1 ∧ v.zf = some (decide (j + 1 = rowsN len rows)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := fun v F mv zf => by
    have m₁ : t₁.mem = u.mem.writeW (off B (arr (kw len) o + 4 * j + 4 * kw len)) (u.gpr .ebx) := by
      rw [M₁.mem, Nat.add_zero]
    have m₁₄ : t₁.mem = t₄.mem := by rw [m₄₂, T₂.mem]
    have kk : Keep B (kw len) [o, o + 1] [oJ] s.mem t₁.mem :=
      keep_of_two (w := kw len) (o := o) Orow (by omega) (by simp only [S]; omega) (by simp) (by simp)
    refine ⟨h₅.keep F (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_, zf,
      (K₅ₜ.trans (F.mono (by decide))).mono (by decide)⟩
    · rw [mv]; refine kk.trans ?_; rw [m₁₄]; exact Keep.of_slot O₅ (by simp)
    · have hv : val32 v.mem B (arr (kw len) o + 4 * j) (kw len + 1) =
          val32 u.mem B (arr (kw len) o + 4 * j) (kw len) + 2 ^ (32 * kw len) * (u.gpr .ebx).toNat := by
        rw [mv, O₅.val32 (.inr hoJ) (by omega), ← m₁₄, val32_succ, m₁, w32_write_self,
          (writeW32_outside u.mem B (d := arr (kw len) o + 4 * j + 4 * kw len) (u.gpr .ebx) (by omega)).val32
            (.inl (by omega)) (by omega)]
      rw [hv, I.val, bj, m₁₁]
    · intro i hi1 hi2
      have hoJ0 : oJ + 4 ≤ arr (kw len) o := by rw [oJ_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
      rw [mv, O₅.w32 (.inr (by omega)) (by omega), ← m₁₄]
      exact Orow.w32 (by omega) (by omega)
    · rw [slot, mv, M₅.mem, w32_write_self, e₄']
  have ax₅ : (t₅.gpr .eax).toNat = j + 1 := by rw [M₅.gpr]; exact e₄'
  have hj1 : j + 1 < 2 ^ 32 := by omega
  cases rows with
  | none =>
    refine bytesB_ok (lenSrc h₅) h.lenLe fun t₆ K₆ m₆ e₆ =>
      VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₇ U₇ => wp_cmp fun v F _ z => WP.block_nil ?_
    have Fk : Keeps [] t₇ v := ⟨fun r _ => by rw [F.gpr], F.rd, F.wr⟩
    refine post v ((K₆.trans (U₇.keeps.mono (by decide))).trans (Fk.mono (by simp)))
      (by rw [F.mem, U₇.mem, m₆]) ?_
    rw [z]
    have ecx : (t₇.gpr .ecx).toNat = kw len := by
      rw [U₇.gpr, BitVec.toNat_ushiftRight, e₆, Nat.shiftRight_eq_div_pow]; omega
    have eax : (t₇.gpr .eax).toNat = j + 1 := by rw [U₇.other _ (by decide), K₆.1 _ (by decide)]; exact ax₅
    congr 1
    by_cases e : j + 1 = kw len
    · rw [decide_eq_true e, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, eax, ecx, e, show BitVec.toNat (0 : BitVec 32) = 0 from rfl]; omega
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_sub, eax, ecx] at this; simp at this; omega
  | some k =>
    have hk := hR k rfl
    refine wp_cmpi fun v F _ z => WP.block_nil ?_
    refine post v ⟨fun r _ => by rw [F.gpr], F.rd, F.wr⟩ F.mem ?_
    rw [z]
    congr 1
    by_cases e : j + 1 = k
    · rw [decide_eq_true e, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, ax₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, e, show BitVec.toNat (0 : BitVec 32) = 0 from rfl]; omega
    · rw [decide_eq_false e, beq_eq_false_iff_ne]
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_sub, ax₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; simp at this; omega

/-- The rows' state after rows `0, …, j - 1` from `s`: `[o]`'s first `j + w` words are
`A (B mod 2^(32 j))`. -/
structure RowsI (L : Lay) (s : State) (B : Addr) (Z len N o a b j : Nat) (u : State) : Prop where
  ws : RtWs L u B Z len N
  keep : Keep B (kw len) [o, o + 1] [oJ] s.mem u.mem
  rest : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u
  cnt : slot u.mem B oJ = j
  val : val32 u.mem B (arr (kw len) o) (j + kw len) = num s.mem B (kw len) a * val32 s.mem B (arr (kw len) b) j

/-- `zeroWide o`, `zeroWide (o + 1)` and the count zero: `RowsI` of no rows. -/
theorem rowsInit_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o + 1 < N) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.seqs [zeroWide L o, zeroWide L (o + 1),
      .block [.mov .eax (.imm 0), .store (sc oJ) .eax]]) s (RowsI L s B Z len N o a b 0) := by
  have hdr := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h (j := o) (by omega)) fun u₁ ⟨h₁, k₁, z₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h₁ (j := o + 1) ho) fun u₂ ⟨h₂, k₂, z₂, K₂⟩ => ?_)
  refine wp_movS rfl fun u₃ U₃ _ => ?_
  have h₃ := h₂.keep U₃.keeps (by decide) (by decide) (by rw [U₃.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlotZ_ok h₃ (d := oJ) (by decide) .eax) fun u₄ ⟨h₄, k₄, e₄, K₄, _⟩ => ?_
  have k₀₄ : Keep B (kw len) [o, o + 1] [oJ] s.mem u₄.mem :=
    ((k₁.mono (by simp) (by simp)).trans (k₂.mono (by simp) (by simp))).trans
      (by rw [U₃.mem] at k₄; exact k₄.mono (by simp) (by simp))
  have K₀₄ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u₄ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans ((U₃.keeps.mono (by decide)).trans (K₄.mono (by simp)))
  have z₀ : val32 u₄.mem B (arr (kw len) o) (kw len) = 0 := by
    have e1 : val32 u₄.mem B (arr (kw len) o) (kw len) = val32 u₁.mem B (arr (kw len) o) (kw len) := by
      rw [U₃.mem] at k₄
      exact val32_congr fun i hi => ((k₂.mono (js' := [o + 1]) (ds' := [oJ]) (by simp) (by simp)).trans
        (k₄.mono (by simp) (by simp))).word (j := o) (i := i) (by simp only [S]; omega) (by simp) (by decide)
        (h.ws.fit64 (by omega))
    rw [e1]
    have := val32_append u₁.mem B (arr (kw len) o) (kw len) 1
    rw [z₁] at this; omega
  exact ⟨h₄, k₀₄, K₀₄, by rw [e₄, U₃.gpr]; rfl, by rw [Nat.zero_add, z₀]; simp [val32]⟩

/-- A row: `RowsI` of one more row, and whether it was the last. -/
theorem rowsStep_ok {s u : State} (h : RtWs L s B Z len N) {o a b j : Nat} {rows : Option Nat}
    (hRk : ∀ k, rows = some k → k < 2 ^ 32) (hRw : rowsN len rows ≤ kw len)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) (hj : j < rowsN len rows) (I : RowsI L s B Z len N o a b j u) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows) u fun v =>
      v.zf = some (decide (j + 1 = rowsN len rows)) ∧ RowsI L s B Z len N o a b (j + 1) v := by
  have fitb := h.ws.fit64 hb
  have fita := h.ws.fit64 ha
  have fo := h.ws.arr_fit ho
  simp only [S] at fo
  refine WP.mono (mulRow_ok I.ws (rows := rows) ho ha hb hao hao1 I.cnt (by omega) hRk)
    fun v ⟨hv, kv, ev, wv, cv, zv, Kv⟩ => ⟨zv, ?_⟩
  have Ia : num u.mem B (kw len) a = num s.mem B (kw len) a :=
    I.keep.num (by simp; omega) (by decide) fita
  have Ib : val32 u.mem B (arr (kw len) b) (j + 1) = val32 s.mem B (arr (kw len) b) (j + 1) :=
    val32_congr fun i hi => I.keep.word (j := b) (i := i) (by simp only [S]; omega) (by simp; omega) (by decide) fitb
  refine ⟨hv, I.keep.trans kv, I.rest.trans Kv, cv, ?_⟩
  -- The low `j` words kept, and the row.
  have hlow : val32 v.mem B (arr (kw len) o) j = val32 u.mem B (arr (kw len) o) j :=
    val32_congr fun i hi => wv i (.inl hi) (by omega)
  rw [show j + 1 + kw len = j + (kw len + 1) by omega, val32_append, hlow, ev, Ia,
    show w32 u.mem B (arr (kw len) b + 4 * j) = w32 s.mem B (arr (kw len) b + 4 * j) by
      have := Ib; rw [val32_succ, val32_succ] at this
      exact I.keep.word (j := b) (i := j) (by simp only [S]; omega) (by simp; omega) (by decide) fitb]
  have e := I.val
  rw [val32_append] at e
  rw [val32_succ s.mem B (arr (kw len) b) j]
  have e2 : val32 u.mem B (arr (kw len) o) j + 2 ^ (32 * j) * val32 u.mem B (arr (kw len) o + 4 * j) (kw len) =
      num s.mem B (kw len) a * val32 s.mem B (arr (kw len) b) j := e
  generalize num s.mem B (kw len) a = A at *
  grind

/-- `zeroWide o`, `zeroWide (o + 1)`, the count zero, and rows up to `rowsN`: `[o]`'s first
`R + w` words are `A (B mod 2^(32 R))`, across arrays `o` and `o + 1`. -/
theorem mulRows_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} {rows : Option Nat}
    (hR1 : 1 ≤ rowsN len rows) (hRw : rowsN len rows ≤ kw len) (hRk : ∀ k, rows = some k → k < 2 ^ 32)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.seqs [zeroWide L o, zeroWide L (o + 1),
      .block [.mov .eax (.imm 0), .store (sc oJ) .eax], .loop (VG.Impl.Rsa.X86.WordModRt.mulRow L o a b rows) .ne]) s
      fun v => RtWs L v B Z len N ∧ Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
        val32 v.mem B (arr (kw len) o) (rowsN len rows + kw len) =
          num s.mem B (kw len) a * val32 s.mem B (arr (kw len) b) (rowsN len rows) ∧
        Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have init := rowsInit_ok h (a := a) (b := b) ho
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs] at init ⊢
  rw [WP.seq_iff] at init
  refine WP.seq (WP.mono init fun u₁ w₁ => ?_)
  rw [WP.seq_iff] at w₁
  refine WP.seq (WP.mono w₁ fun u₂ w₂ => ?_)
  refine WP.seq (WP.mono w₂ fun u₄ I₀ => ?_)
  refine WP.loop (M := isa) (fun n u => ∃ j, n = rowsN len rows - j ∧ j < rowsN len rows ∧ RowsI L s B Z len N o a b j u)
    ?_ _ u₄ ⟨0, rfl, by omega, I₀⟩
  rintro n u ⟨j, rfl, hj, I⟩
  refine WP.mono (rowsStep_ok h hRk hRw ho ha hb hao hao1 hbo hbo1 hj I) fun v ⟨zv, I'⟩ => ?_
  by_cases e : j + 1 = rowsN len rows
  · refine .inl ⟨by simp only [eval, zv, e, decide_true, Option.map_some, Bool.not_true], I'.ws, I'.keep, ?_, I'.rest⟩
    rw [← e]; exact I'.val
  · exact .inr ⟨by simp only [eval, zv, e, decide_false, Option.map_some, Bool.not_false], rowsN len rows - (j + 1),
      by omega, j + 1, rfl, by omega, I'⟩

/-- `mulWide o a b`: `[o] = [a] [b]` over `2 w` words, across arrays `o` and `o + 1`. -/
theorem mulWide_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat}
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide L o a b) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) o) (2 * kw len) = num s.mem B (kw len) a * num s.mem B (kw len) b ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have := mulRows_ok h (rows := none) (by simp only [rowsN]; exact h.kw_pos) (by simp only [rowsN]; omega)
    (by simp) ho ha hb hao hao1 hbo hbo1
  simp only [rowsN] at this
  rw [show 2 * kw len = kw len + kw len by omega]
  exact this

/-- `mulShort o a b`: `[o] = [a] (b mod 2^64)`, the low two words of `[b]`, over `w + 2` words. -/
theorem mulShort_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (hw2 : 2 ≤ kw len)
    (ho : o + 1 < N) (ha : a < N) (hb : b < N) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort L o a b) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [o, o + 1] [oJ] s.mem v.mem ∧
      val32 v.mem B (arr (kw len) o) (kw len + 2) = num s.mem B (kw len) a * val32 s.mem B (arr (kw len) b) 2 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s v := by
  have := mulRows_ok h (rows := some 2) (by simp only [rowsN]; omega) (by simp only [rowsN]; omega)
    (fun k hk => by cases hk; decide) ho ha hb hao hao1 hbo hbo1
  simp only [rowsN] at this
  rw [Nat.add_comm (kw len) 2]
  exact this

end VG.Proof.Rsa.X86.WordRt

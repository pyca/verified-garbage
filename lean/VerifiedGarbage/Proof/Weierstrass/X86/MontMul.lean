import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Mont.X86.Loop

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the rows of the product

Row `i` of `mulFn` (`rowF`), the working space at `ebp`, `[a]` at `edi` and
`[b]` at `esi`: `ecx = a_i`, the window of the accumulator at `own + 4i`
`+= a_i B` (row 0 writes it: `rowZ`), then `+= q m` for the `q` that makes its
low word zero (`redDigit`, `redRowI`), so that the accumulator's words from
`i + 1` hold `(T + a_i B + q m) / 2³²`, below `2m` again (`rowF_ok`). After
the `N` rows, the words from `N` hold `T < 2m` with `R T ≡ A B` (`rowsF_ok`).
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- What the functions need of the modulus `m` of `k` words: `m` odd (its
inverse), below `R = 2^(64 k)`, and the reduction's certificate. -/
structure MulOk (k m : Nat) : Prop where
  k0 : 0 < k
  m_lt : m < 2 ^ (64 * k)
  inv : (m * (minv m) + 1) % 2 ^ 64 = 0

theorem MulOk.m_pos {k m : Nat} (h : MulOk k m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · have := h.inv; simp at this
  · exact h'

theorem mod_ok (k m : Nat) : (mod k m).ok m = true := by
  simp only [Mod.ok, mod, Bool.not_false, Bool.true_or, Bool.and_true]
  exact p256RedChoice_ok k m

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := by unfold minv; exact Nat.mod_lt _ (by decide)

theorem minv32_mod {k m : Nat} (h : MulOk k m) : (m * (minv32 (mod k m)).toNat + 1) % 2 ^ 32 = 0 := by
  apply minv32_inv
  have e : (mod k m).minv.toNat = minv m := by
    show (BitVec.ofNat 64 (minv m)).toNat = minv m
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minv_lt m)]
  rw [e]; exact h.inv

theorem words_mod (k m : Nat) : words (mod k m) = 2 * k := rfl

variable {s : State} {base : Addr} {size : Nat}

/-- The reduction digit `q = t₀ m' mod 2³²`, from the window's low word. -/
theorem redDigitB_ok {M : Mod} (hb : Bx s base size) {acc : Nat} (ha : acc + 4 ≤ size) :
    WP isa (.block (redDigit M acc)) s fun t =>
      (t.gpr .ecx).toNat = (s.mem.readW (off base acc) 32).toNat * (minv32 M).toNat % 2^32 ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold redDigit
  split
  next h =>
    refine wp_movS (readSrc_bp hb ha) fun _t u _ => WP.block_nil ⟨?_, u.keeps.mono (by decide), u.mem⟩
    rw [u.gpr, h]
    change _ = _ * 1 % 2^32
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base acc) 32).isLt]
  next _ =>
    refine wp_movS (readSrc_bp hb ha) fun _s₁ u₁ _ => ?_
    refine wp_movS rfl fun _s₂ u₂ _ => ?_
    refine wp_mul fun _s₃ m₃ => ?_
    refine wp_movS rfl fun _s₄ u₄ _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₄.gpr, m₃.eax, u₂.other .eax (by decide), u₁.gpr, u₂.gpr, BitVec.toNat_ofNat]
    · exact ((u₁.keeps.mono (by decide) |>.widen u₂.keeps).widen m₃.keeps).widen u₄.keeps
    · rw [u₄.mem, m₃.mem, u₂.mem, u₁.mem]

/-- The words of `m`. -/
theorem yVal_mw (m : Nat) : ∀ k, yVal (mw m) k = m % 2 ^ (32 * k)
  | 0 => by simp [yVal, Nat.mod_one]
  | k + 1 => by
    rw [yVal, yVal_mw m k, mw, BitVec.toNat_ofNat, pow32_add, show 32 * 1 = 32 from rfl, Nat.mod_mul,
      Nat.shiftRight_eq_div_pow]

theorem ysOk_m (m : Nat) {base : Addr} {acc len N : Nat} {s : State} :
    YsOk (mWord m) (mw m) base acc len N s := fun _ _ _ _ => rfl

/-- The words of `[b]`, at `esi`, apart from the window. -/
theorem ysOk_b (hb : Bx s base size) {pb : Nat} (hp : Ptr s .esi pb) {acc len N : Nat}
    (hfit : pb + 4 * N ≤ size) (hsep : pb + 4 * N ≤ acc ∨ acc + len ≤ pb) :
    YsOk bWord (fun j => s.mem.readW (off base (pb + 4 * j)) 32) base acc len N s := by
  intro j hj t K
  have hn := hb.nowrap
  have hbt : Bx t base size := ⟨by rw [K.ebp]; exact hb.ebp, K.wr ▸ hb.wr, hb.nowrap⟩
  have hpt : Ptr t .esi pb := by
    change t.gpr .esi = t.gpr .ebp + _
    rw [K.esi, K.ebp]; exact hp
  rw [bWord, readSrc_ptr hbt hpt (by omega)]
  exact congrArg some (BitVec.eq_of_toNat_eq (K.out.w32 (by omega) (by omega)))

/-- The window `+= q m`, `q` in `ecx`, for `q = t₀ m'` (which P-256's sparse
reduction needs). -/
theorem redRowI_ok (hb : Bx s base size) {k m acc : Nat} (hM : MulOk k m)
    (hacc : acc + 4 * (2 * k) + 8 ≤ size)
    (hq : minv32 (mod k m) = 1 → (s.gpr .ecx).toNat = w32 s.mem base acc)
    (hlt : val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m < 2 ^ (32 * (2 * k + 2))) :
    WP isa (.block (redRowI (mod k m) m acc)) s fun u =>
      Outside base acc (4 * (2 * k) + 8) s.mem u.mem ∧
      val32 u.mem base acc (2 * k + 2) = val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hk := hM.k0
  have hm2 : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  unfold redRowI
  split
  next he =>
    obtain ⟨hn, hm', hi⟩ := p256RedEnabled_ok (mod_ok k m) he
    have hk4 : k = 4 := hn
    subst hk4
    rw [hm'] at hlt ⊢
    simp only [Nat.reduceMul, Nat.reduceAdd] at hlt hacc ⊢
    unfold p256Prime at hlt ⊢
    exact WP.mono (p256RedB_ok hb rfl hacc (hq hi) hlt) fun u ⟨O, V, K⟩ => ⟨O, V, K.mono (by decide)⟩
  next _ =>
    rw [words_mod]
    refine WP.mono (rowG_ok hb (by omega) (ysOk_m m) hacc ?_) fun u ⟨O, V, K⟩ => ⟨O, ?_, K⟩
    · rw [yVal_mw, Nat.mod_eq_of_lt hm2]; exact hlt
    · rw [V, yVal_mw, Nat.mod_eq_of_lt hm2]

/-- The reduction of a row: `q = t₀ m' mod 2³²`, then the window `+= q m`,
whose low word becomes zero. -/
theorem rowTail_ok (hb : Bx s base size) {k m w : Nat} (hM : MulOk k m) (hacc : w + 4 * (2 * k) + 8 ≤ size)
    (hlt : val32 s.mem base w (2 * k + 2) + (2 ^ 32 - 1) * m < 2 ^ (32 * (2 * k + 2))) :
    WP isa (.block (redDigit (mod k m) w ++ redRowI (mod k m) m w)) s fun u =>
      Outside base w (4 * (2 * k) + 8) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      ∃ q, q < 2 ^ 32 ∧ val32 u.mem base w (2 * k + 2) = val32 s.mem base w (2 * k + 2) + q * m ∧
        w32 u.mem base w = 0 := by
  have hn := hb.nowrap
  refine WP.block_append (WP.mono (redDigitB_ok (M := mod k m) hb (acc := w) (by omega))
    fun s₁ ⟨q₁, K₁, mem₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hq := (s₁.gpr .ecx).isLt
  refine WP.mono (redRowI_ok hb₁ hM (by omega) (fun h1 => ?_) ?_) fun u ⟨O, V, K⟩ =>
    ⟨by rw [mem₁] at O; exact O, (K₁.mono (rs' := [.eax, .ebx, .ecx, .edx]) (by decide)).widen K (by decide),
      ⟨_, hq, by rw [V, mem₁], ?_⟩⟩
  · rw [q₁, h1, mem₁]
    change _ * 1 % _ = _
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base w) 32).isLt]
  · rw [mem₁]
    have : (s₁.gpr .ecx).toNat * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hv : ∀ mem : Mem, val32 mem base w (2 * k + 2) = w32 mem base w + 2 ^ 32 * val32 mem base (w + 4) (2 * k + 1) :=
      fun _ => rfl
    have h0 : (val32 u.mem base w (2 * k + 2)) % 2 ^ 32 = w32 u.mem base w := by
      rw [hv]; have := (u.mem.readW (off base w) 32).isLt; simp only [w32] at *; omega
    rw [← h0, V, mem₁, hv, q₁]
    have := mont_low32 (w32 s.mem base w) (minv32 (mod k m)).toNat m (minv32_mod hM)
    rw [Nat.add_assoc, Nat.add_comm (2 ^ 32 * _), ← Nat.add_assoc, Nat.add_mul_mod_self_left]
    exact this

/-- Where the product's numbers are: `[a]` and `[b]` (`N = 2k` words) below
the accumulator (`2N + 1` words at `A`), in the working space. -/
structure MulLayB (k size pa pb A : Nat) : Prop where
  pa : pa + 4 * (2 * k) ≤ A
  pb : pb + 4 * (2 * k) ≤ A
  acc : A + 4 * (2 * (2 * k) + 1) ≤ size

/-- Row `i` of the product. -/
theorem rowF_ok (hb : Bx s base size) {k m pa pb i : Nat} (hM : MulOk k m)
    (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb) (hL : MulLayB k size pa pb (own k)) (hi : i < 2 * k)
    (hB : val32 s.mem base pb (2 * k) < m)
    (hT : 0 < i → val32 s.mem base (own k + 4 * i) (2 * k + 1) < 2 * m) :
    WP isa (.block (rowF k m i)) s fun u =>
      Outside base (own k) (4 * (2 * (2 * k) + 1)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (own k + 4 * (i + 1)) (2 * k + 1) =
        (if i = 0 then 0 else val32 s.mem base (own k + 4 * i) (2 * k + 1)) +
          w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) + q * m) ∧
      val32 u.mem base (own k + 4 * (i + 1)) (2 * k + 1) < 2 * m := by
  have hn := hb.nowrap
  have := hL.pa; have := hL.pb; have := hL.acc
  have hk := hM.k0
  have hmP : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  have hP : 0 < 2 ^ (32 * (2 * k)) := Nat.two_pow_pos _
  obtain ⟨w, hw⟩ : ∃ w, own k + 4 * i = w := ⟨_, rfl⟩
  -- The product row, into a state `s₂` whose window holds `T₀ + a_i B`.
  have prod : WP isa (.block ([.mov .ecx (.mem (at_ .edi (4 * i)))] ++
      (if i = 0 then rowZ (own k) (2 * k)
        else rowG bWord (own k + 4 * i) (2 * k) (carryUp1 (own k + 4 * i) (2 * k))))) s fun s₂ =>
      Outside base w (4 * (2 * k) + 8) s.mem s₂.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s s₂ ∧
      val32 s₂.mem base w (2 * k + 2) = (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) +
        w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) := by
    refine wp_movS (readSrc_ptr hb hpa (d := 4 * i) (by omega)) fun s₁ u₁ _ => ?_
    have k₁ : Keeps [.eax, .ebx, .ecx, .edx] s s₁ := u₁.keeps.mono (by decide)
    have hb₁ := hb.of_keeps k₁ (by decide)
    have hpb₁ : Ptr s₁ .esi pb := hpb.of_keeps k₁ (by decide) (by decide)
    have ecx₁ : (s₁.gpr .ecx).toNat = w32 s.mem base (pa + 4 * i) := by rw [u₁.gpr]
    have mem₁ : s₁.mem = s.mem := u₁.mem
    have hY := ysOk_b hb₁ hpb₁ (acc := w) (len := 4 * (2 * k) + 8) (N := 2 * k) (by omega) (by omega)
    have hYv : yVal (fun j => s₁.mem.readW (off base (pb + 4 * j)) 32) (2 * k) = val32 s.mem base pb (2 * k) := by
      rw [yVal_val32, mem₁]
    by_cases h0 : i = 0
    · subst h0
      have hw0 : w = own k := by omega
      subst hw0
      simp only [ite_true]
      refine WP.mono (rowZ_ok hb₁ (by omega) hY (by omega)) fun u ⟨O, V, K⟩ =>
        ⟨by rw [mem₁] at O; exact O, k₁.widen K (by decide), ?_⟩
      rw [V, hYv, ecx₁, Nat.zero_add]
    · simp only [h0, ite_false]
      rw [hw]
      refine WP.mono (rowG1_ok hb₁ (by omega) hY (by omega)) fun u ⟨O, V, K⟩ =>
        ⟨by rw [mem₁] at O; exact O, k₁.widen K (by decide), ?_⟩
      rw [V, hYv, ecx₁, mem₁]
  simp only [rowF, List.append_assoc]
  rw [← List.append_assoc]
  refine WP.block_append (WP.mono prod fun s₂ ⟨O₂, K₂, V₂⟩ => ?_)
  have hb₂ := hb.of_keeps K₂ (by decide)
  have hA := (s.mem.readW (off base (pa + 4 * i)) 32).isLt
  have hT0 : (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) < 2 * m := by
    split
    · exact Nat.mul_pos (by decide) hM.m_pos
    · rename_i h; rw [← hw]; exact hT (by omega)
  have hlt := row_lt (T := if i = 0 then 0 else val32 s.mem base w (2 * k + 1))
    (a := w32 s.mem base (pa + 4 * i)) (B := val32 s.mem base pb (2 * k)) (m := m) (q := 2 ^ 32 - 1)
    hT0 hA hB (by decide)
  have hpow : 2 ^ (32 * (2 * k + 2)) = 2 ^ (32 * (2 * k)) * 2 ^ 64 := by rw [pow32_add]
  rw [hw]
  refine WP.mono (rowTail_ok hb₂ hM (w := w) (by omega) ?_) fun u ⟨O, K, q, hq, V, z⟩ => ?_
  · rw [V₂, hpow]
    have : m * 2 ^ 64 < 2 ^ (32 * (2 * k)) * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega
  have hlt' := row_lt (T := if i = 0 then 0 else val32 s.mem base w (2 * k + 1))
    (a := w32 s.mem base (pa + 4 * i)) (B := val32 s.mem base pb (2 * k)) (m := m) (q := q) hT0 hA hB hq
  have hv : val32 u.mem base w (2 * k + 2) = w32 u.mem base w + 2 ^ 32 * val32 u.mem base (w + 4) (2 * k + 1) :=
    rfl
  rw [z, Nat.zero_add] at hv
  have ew : own k + 4 * (i + 1) = w + 4 := by omega
  have e : (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) +
      w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) + q * m =
      2 ^ 32 * val32 u.mem base (w + 4) (2 * k + 1) := by rw [← V₂, ← V, hv]
  refine ⟨(O₂.trans O).mono (by omega) (by omega), K₂.trans K, ⟨q, ?_⟩, ?_⟩
  · rw [ew, ← e]
  · rw [ew]
    rw [e] at hlt'
    omega

/-- The rows `0 … r - 1` of the product: the accumulator's words from `r`
hold `T < 2m` with `2^(32 r) T ≡ A_r B`, `A_r` the low `r` words of `[a]`. -/
theorem rowsF_ok (hb : Bx s base size) {k m pa pb : Nat} (hM : MulOk k m)
    (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb) (hL : MulLayB k size pa pb (own k))
    (hB : val32 s.mem base pb (2 * k) < m) :
    ∀ r, 1 ≤ r → r ≤ 2 * k →
    WP isa (.block (rowsF k m r)) s fun u =>
      Outside base (own k) (4 * (2 * (2 * k) + 1)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base (own k + 4 * r) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * r) * val32 u.mem base (own k + 4 * r) (2 * k + 1) =
        val32 s.mem base pa r * val32 s.mem base pb (2 * k) + U * m
  | 0, h, _ => absurd h (by decide)
  | 1, _, hr => by
    simp only [rowsF, List.nil_append]
    refine WP.mono (rowF_ok hb hM hpa hpb hL (i := 0) (by omega) hB (fun h => absurd h (by decide)))
      fun u ⟨O, K, ⟨q, hq⟩, hT⟩ => ⟨O, K, hT, ⟨q, ?_⟩⟩
    rw [show 32 * 1 = 32 from rfl, hq, val32_one]
    simp
  | r + 2, _, hr => by
    have hn := hb.nowrap
    have := hL.pa; have := hL.pb; have := hL.acc
    rw [rowsF]
    refine WP.block_append (WP.mono (rowsF_ok hb hM hpa hpb hL hB (r + 1) (by omega) (by omega))
      fun s₁ ⟨O₁, K₁, T₁, ⟨U, hU⟩⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hpa₁ : Ptr s₁ .edi pa := hpa.of_keeps K₁ (by decide) (by decide)
    have hpb₁ : Ptr s₁ .esi pb := hpb.of_keeps K₁ (by decide) (by decide)
    have hb' : val32 s₁.mem base pb (2 * k) = val32 s.mem base pb (2 * k) := O₁.val32 (by omega) (by omega)
    have ha' : w32 s₁.mem base (pa + 4 * (r + 1)) = w32 s.mem base (pa + 4 * (r + 1)) :=
      O₁.w32 (by omega) (by omega)
    refine WP.mono (rowF_ok hb₁ hM hpa₁ hpb₁ hL (i := r + 1) (by omega) (hb' ▸ hB) (fun _ => T₁))
      fun u ⟨O, K, ⟨q, hq⟩, hT⟩ => ⟨O₁.trans O, K₁.trans K, hT, ?_⟩
    simp only [Nat.add_one_ne_zero, ite_false] at hq
    rw [hb', ha'] at hq
    refine ⟨U + 2 ^ (32 * (r + 1)) * q, ?_⟩
    rw [show r + 1 + 1 = r + 2 from rfl] at hq
    rw [show 2 ^ (32 * (r + 2)) = 2 ^ (32 * (r + 1)) * 2 ^ 32 by rw [pow32_succ (r + 1), Nat.mul_comm],
      Nat.mul_assoc, hq, val32_succ s.mem base pa (r + 1)]
    generalize 2 ^ (32 * (r + 1)) = P at *
    grind

end VG.Proof.Weierstrass.X86.Mont

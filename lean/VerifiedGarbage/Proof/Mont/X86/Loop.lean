import VerifiedGarbage.Proof.Mont.X86.Row

/-!
# Montgomery arithmetic on x86 (32-bit): the loop of the multiplication

An iteration of `mul`'s loop (`row`), at `ebp = edi + 4i`, adds `a_i [b]`
and then `q m` to the window at `acc + 4i`, which holds `T`, the number
below `2m` in the accumulator's words from `i` up (`row_ok`): `q` makes the
sum's low word zero, so the accumulator's words from `i + 1` up hold
`(T + a_i B + q m) / 2³²`, below `2m` again; `ZF` is whether `i + 1 = N`.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- The inverse-one specialization has the same reduction digit and frame. -/
theorem redDigit_ok {M : Mod} {s : State} {base : Addr} {size i acc : Nat}
    (hs : Scr s base size) (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : 4 * i + acc + 4 ≤ size) :
    WP isa (.block (redDigit M acc)) s fun t =>
      (t.gpr .ecx).toNat = (s.mem.readW (off base (4 * i + acc)) 32).toNat * (minv32 M).toNat % 2^32 ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold redDigit
  split
  next h =>
    refine wp_movS (readSrc_at hs hp ha) fun _t u _ => WP.block_nil ⟨?_, u.keeps.mono (by decide), u.mem⟩
    rw [u.gpr, h]
    change _ = _ * 1 % 2^32
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base (4 * i + acc)) 32).isLt]
  next _ =>
    refine wp_movS (readSrc_at hs hp ha) fun _s₁ u₁ _ => ?_
    refine wp_movS rfl fun _s₂ u₂ _ => ?_
    refine wp_mul fun _s₃ m₃ => ?_
    refine wp_movS rfl fun _s₄ u₄ _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₄.gpr, m₃.eax, u₂.other .eax (by decide), u₁.gpr, u₂.gpr, BitVec.toNat_ofNat]
    · exact ((u₁.keeps.mono (by decide) |>.widen u₂.keeps).widen m₃.keeps).widen u₄.keeps
    · rw [u₄.mem, m₃.mem, u₂.mem, u₁.mem]

/-- `t₀ + (t₀ m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low32 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 + t0 * minv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega,
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`. -/
theorem minv32_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0 := by
  rw [minv32, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T a B q m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32) (hB : B < m) (hq : q < 2 ^ 32) :
    T + a * B + q * m < 2 ^ 32 * (2 * m) := by
  have h1 : a * B ≤ (2 ^ 32 - 1) * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : q * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`N`
words) in the working space and apart from the accumulator (`2N + 1` words
at `acc`). -/
structure MulLay (N size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (2 * N + 1) ≤ size
  a_le : a + 4 * N ≤ size
  b_le : b + 4 * N ≤ size
  mo_le : mo + 4 * N ≤ size
  sa : a + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ a
  sb : b + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ b
  smo : mo + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ mo

/-- `ZF` after the loop's comparison: whether `ebp` reached `edi + 4N`. -/
theorem row_zf (e : BitVec 32) {i N : Nat} (hi : i < N) (hN : 4 * N < 2 ^ 32) :
    (e + BitVec.ofNat 32 (4 * i) + 4 - (e + BitVec.ofNat 32 (4 * N)) == 0) = decide (i + 1 = N) := by
  by_cases h : i + 1 = N
  · subst h; simp only [decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem row_ebp (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega

/-- An iteration of the loop. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N acc a b i m : Nat}
    (hNw : words M = N) (hL : MulLay N size acc a b M.mo) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : val32 s.mem base M.mo N = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m)
    (hT : val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m) :
    WP isa (.block (row M acc a b)) s fun u =>
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outside base acc (4 * (2 * N + 1)) s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) + w32 s.mem base (a + 4 * i) * val32 s.mem base b N +
          q * m) ∧
      val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps clob s u := by
  have hn := hs.nowrap
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hL.sa
  have := hL.sb
  have := hL.smo
  have hmP : m < 2 ^ (32 * N) := hm ▸ val32_lt _ _ _ _
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hpow : 2 ^ (32 * (N + 2)) = 2 ^ (32 * N) * 2 ^ 64 := by rw [pow32_add]
  have hpow1 : 2 ^ (32 * (N + 1)) = 2 ^ (32 * N) * 2 ^ 32 := by rw [pow32_add]
  -- The window: the accumulator's words from `i`, of which only the low
  -- `N + 2` may be nonzero.
  obtain ⟨w, hw⟩ : ∃ w, 4 * i + acc = w := ⟨_, rfl⟩
  have ew : acc + 4 * i = w := by omega
  rw [ew] at hT
  have hsplit : ∀ mem : Mem, val32 mem base w (2 * N + 1 - i) =
      val32 mem base w (N + 2) + 2 ^ (32 * (N + 2)) * val32 mem base (w + 4 * (N + 2)) (N - 1 - i) := by
    intro mem
    rw [show 2 * N + 1 - i = (N + 2) + (N - 1 - i) by omega, val32_append]
  have habove : val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hsplit] at hT
    rcases Nat.eq_zero_or_pos (val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i)) with h | h
    · exact h
    · have : 2 ^ (32 * (N + 2)) * 1 ≤ 2 ^ (32 * (N + 2)) * val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) :=
        Nat.mul_le_mul_left _ h
      have : 2 * 2 ^ (32 * N) ≤ 2 ^ (32 * (N + 2)) := by rw [hpow]; omega
      omega
  have hTw : val32 s.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) := by
    rw [hsplit s.mem, habove]; omega
  simp only [row]
  rw [hNw]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `ecx = a_i`.
  refine wp_movS (readSrc_at hs hp (d := a) (by omega)) fun s₁ u₁ _ => ?_
  have k₁ : Keeps clob s s₁ := u₁.keeps.mono (by decide)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  have ecx₁ : (s₁.gpr .ecx).toNat = w32 s.mem base (a + 4 * i) := by rw [u₁.gpr, Nat.add_comm a]
  have mem₁ : s₁.mem = s.mem := u₁.mem
  -- The window `+= a_i B`.
  have hlt₁ : val32 s₁.mem base w (N + 2) + (s₁.gpr .ecx).toNat * val32 s₁.mem base b N < 2 ^ (32 * (N + 2)) := by
    rw [mem₁, hTw, ecx₁, hpow]
    have := (s.mem.readW (off base (a + 4 * i)) 32).isLt
    have : w32 s.mem base (a + 4 * i) * val32 s.mem base b N ≤ (2 ^ 32 - 1) * val32 s.mem base b N :=
      Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega
  refine WP.block_append (WP.mono (mulRow_ok hs₁ hp₁ hw hL.b_le (by omega) (by omega) hlt₁)
    fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have k₂ : Keeps clob s s₂ := k₁.widen K₂
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp₁
  rw [mem₁, hTw, ecx₁] at V₂
  rw [mem₁] at O₂
  -- `ecx = q`, from the window's low word.
  refine WP.block_append (WP.mono (redDigit_ok (M := M) hs₂ hp₂ (by omega)) fun s₆ ⟨q₆, K₆, mem₆⟩ => ?_)
  have k₆ : Keeps clob s s₆ := k₂.widen K₆
  have hs₆ := hs.of_keeps k₆ (by decide)
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.1 _ (by decide), K₆.1 _ (by decide)]; exact hp₂
  have t0 : (s₂.mem.readW (off base (4 * i + acc)) 32).toNat = val32 s₂.mem base w (N + 2) % 2 ^ 32 := by
    rw [hw, val32]
    have := (s₂.mem.readW (off base w) 32).isLt
    simp only [w32]
    omega
  have ecx₆ : (s₆.gpr .ecx).toNat = val32 s₂.mem base w (N + 2) % 2 ^ 32 * (minv32 M).toNat % 2 ^ 32 := by
    rw [q₆, t0]
  -- The window `+= q m`.
  have hmo₂ : val32 s₂.mem base M.mo N = m := by rw [O₂.val32 (by omega) (by omega), hm]
  have hq : (s₆.gpr .ecx).toNat < 2 ^ 32 := (s₆.gpr .ecx).isLt
  have hW1 := row_lt (q := 0) (a := w32 s.mem base (a + 4 * i)) hT (s.mem.readW (off base (a + 4 * i)) 32).isLt hB (by decide)
  have hlt₆ : val32 s₆.mem base w (N + 2) + (s₆.gpr .ecx).toNat * val32 s₆.mem base M.mo N < 2 ^ (32 * (N + 2)) := by
    rw [mem₆, V₂, hmo₂, hpow]
    have : (s₆.gpr .ecx).toNat * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega
  refine WP.block_append (WP.mono (mulRow_ok hs₆ hp₆ hw hL.mo_le (by omega) (by omega) hlt₆)
    fun s₇ ⟨O₇, V₇, K₇⟩ => ?_)
  have k₇ : Keeps clob s s₇ := k₆.widen K₇
  have hp₇ : s₇.gpr .ebp = s₇.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₇.1 _ (by decide), K₇.1 _ (by decide)]; exact hp₆
  rw [mem₆, V₂, hmo₂] at V₇
  rw [mem₆] at O₇
  -- `ebp += 4`, and the comparison.
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_movS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_cmpS rfl fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have k₁₁ : Keeps clob s s₁₁ :=
    (((k₇.widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen (f₁₁.keeps clob)
  have mem₁₁ : s₁₁.mem = s₇.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
  have edi₁₁ : s₁₁.gpr .edi = s₇.gpr .edi := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)]
  have ebp₁₁ : s₁₁.gpr .ebp = s₇.gpr .ebp + 4 := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  have edx₁₀ : s₁₀.gpr .edx = s₇.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ (by decide)]
  have hN32 : 4 * N < 2 ^ 32 := by omega
  -- The new window.
  have hO : Outside base w (4 * N + 8) s.mem s₁₁.mem := by
    rw [mem₁₁]; exact O₂.trans O₇
  have habove' : val32 s₁₁.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hO.val32 (by omega) (by omega), habove]
  have hW2 : val32 s₁₁.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) +
      w32 s.mem base (a + 4 * i) * val32 s.mem base b N + (s₆.gpr .ecx).toNat * m := by
    rw [mem₁₁, V₇]
  have hlow : val32 s₁₁.mem base w (N + 2) % 2 ^ 32 = 0 := by
    rw [hW2, ← V₂, ecx₆, ← Nat.mod_add_mod]; exact mont_low32 _ _ _ hinv
  have hT' : val32 s₁₁.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
      val32 s₁₁.mem base (w + 4) (N + 1) := by
    rw [show acc + 4 * (i + 1) = w + 4 by omega, show 2 * N + 1 - (i + 1) = (N + 1) + (N - 1 - i) by omega,
      val32_append, show w + 4 + 4 * (N + 1) = w + 4 * (N + 2) by omega, habove', Nat.mul_zero, Nat.add_zero]
  have hsh : val32 s₁₁.mem base w (N + 2) = w32 s₁₁.mem base w + 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) :=
    rfl
  have h32 : w32 s₁₁.mem base w < 2 ^ 32 := (s₁₁.mem.readW (off base w) 32).isLt
  have hW : 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) = val32 s₁₁.mem base w (N + 2) := by omega
  have hlt := row_lt (a := w32 s.mem base (a + 4 * i)) hT (s.mem.readW (off base (a + 4 * i)) 32).isLt hB hq
  refine ⟨?_, ?_, hO.mono (by omega) (by omega), ⟨(s₆.gpr .ecx).toNat, ?_⟩, ?_, k₁₁⟩
  · rw [ebp₁₁, edi₁₁, hp₇, row_ebp]
  · have ebp₁₀ : s₁₀.gpr .ebp = s₇.gpr .ebp + 4 := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
    rw [z₁₁, ebp₁₀, edx₁₀, hp₇, row_zf _ hi hN32]
  · rw [hT', hW, hW2, ew]
  · rw [hT']
    rw [← hW2, ← hW] at hlt
    omega

/-- The invariant of the loop, before iteration `i`: the accumulator's
words from `i` up hold `T < 2m` with `2^(32 i) T ≡ A_i B`, for the low `i`
words `A_i` of `[a]`. -/
structure LoopInv (base : Addr) (N acc a b m i : Nat) (s t : State) : Prop where
  ebp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * i)
  out : Outside base acc (4 * (2 * N + 1)) s.mem t.mem
  keeps : Keeps clob s t
  lt : val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m
  cong : ∃ U, 2 ^ (32 * i) * val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) =
    val32 s.mem base a i * val32 s.mem base b N + U * m

/-- The loop of `mul`: from the invariant at 0 to the invariant at `N`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N acc a b m : Nat}
    (hNw : words M = N) (hL : MulLay N size acc a b M.mo) (hN : 0 < N)
    (hm : val32 s.mem base M.mo N = m) (hinv : (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m) {t : State} (h0 : LoopInv base N acc a b m 0 s t) :
    WP isa (.loop (.block (row M acc a b)) .ne) t fun u => LoopInv base N acc a b m N s u := by
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hL.sa
  have := hL.sb
  have := hL.smo
  have hn := hs.nowrap
  refine WP.loop (M := isa)
    (fun n t' => ∃ i, n = N - i ∧ i < N ∧ LoopInv base N acc a b m i s t') ?_ N t ⟨0, rfl, hN, h0⟩
  rintro n t' ⟨i, rfl, hi, I⟩
  have ht := hs.of_keeps I.keeps (by decide)
  have hm' : val32 t'.mem base M.mo N = m := by rw [I.out.val32 (by omega) (by omega), hm]
  have hb' : val32 t'.mem base b N = val32 s.mem base b N := I.out.val32 (by omega) (by omega)
  have ha' : w32 t'.mem base (a + 4 * i) = w32 s.mem base (a + 4 * i) := I.out.w32 (by omega) (by omega)
  refine WP.mono (row_ok ht hNw hL hi I.ebp hm' hinv (hb' ▸ hB) I.lt)
    fun u ⟨hp, hz, O, ⟨q, hq⟩, hT, K⟩ => ?_
  rw [hb', ha'] at hq
  have I' : LoopInv base N acc a b m (i + 1) s u := by
    refine ⟨hp, I.out.trans (O.mono (Nat.le_refl _) (Nat.le_refl _)), I.keeps.trans K, hT, ?_⟩
    obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + 2 ^ (32 * i) * q, ?_⟩
    rw [pow32_succ, val32_succ, Nat.mul_assoc, Nat.mul_left_comm, hq]
    generalize 2 ^ (32 * i) = P at *
    grind
  by_cases hNi : i + 1 = N
  · refine .inl ⟨by simp only [eval, hz, hNi, decide_true, Option.map_some, Bool.not_true], hNi ▸ I'⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hNi, Option.map_some, Bool.not_false],
      N - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.X86

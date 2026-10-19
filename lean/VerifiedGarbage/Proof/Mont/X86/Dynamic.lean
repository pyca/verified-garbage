module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Mont.X86.RowW

/-! # Runtime-modulus Montgomery rows on 32-bit x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The runtime reduction digit, to the multiplier word `[mult]`. -/
theorem redDigit_ok {s : State} {base : Addr} {size i acc inv mult : Nat}
    (hs : Scr s base size) (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (ha : 4 * i + acc + 4 ≤ size) (hv : inv + 4 ≤ size) (hm : mult + 4 ≤ size) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.redDigit acc inv mult)) s fun t =>
      w32 t.mem base mult = w32 s.mem base (4 * i + acc) * w32 s.mem base inv % 2 ^ 32 ∧
      Keeps [.eax, .edx] s t ∧ Outside base mult 4 s.mem t.mem := by
  have hn := hs.nowrap
  unfold VG.Impl.Mont.X86.Dynamic.redDigit
  refine wp_movS (readSrc_at hs hp ha) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ hv) fun s₂ u₂ _ => ?_
  have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
  refine wp_mul fun s₃ m₃ => ?_
  have hs₃ := hs₂.of_keeps m₃.keeps (by decide)
  refine wp_storeS (hs₃.ea (d := mult) (by omega)) (hs₃.write (d := mult) (n := 4) (by omega))
    fun s₄ m₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [m₄.mem, w32_write_self, m₃.eax, u₂.other .eax (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      BitVec.toNat_ofNat]
  · exact ((u₁.keeps.mono (by decide) |>.widen u₂.keeps).widen m₃.keeps).widen (m₄.keeps [])
  · rw [m₄.mem, m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega)

/-- A word apart from both ranges that changed. -/
theorem outs2_w32 {base : Addr} {o₁ n₁ o₂ n₂ : Nat} {m m' : Mem}
    (h : Outs base [(o₁, n₁), (o₂, n₂)] m m') {d : Nat} (h₁ : d + 4 ≤ o₁ ∨ o₁ + n₁ ≤ d)
    (h₂ : d + 4 ≤ o₂ ∨ o₂ + n₂ ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have := h.val32 (d := d) (k := 1) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hd'
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using this

/-- A number apart from both ranges that changed. -/
theorem outs2_val32 {base : Addr} {o₁ n₁ o₂ n₂ : Nat} {m m' : Mem}
    (h : Outs base [(o₁, n₁), (o₂, n₂)] m m') {d k : Nat} (h₁ : d + 4 * k ≤ o₁ ∨ o₁ + n₁ ≤ d)
    (h₂ : d + 4 * k ≤ o₂ ∨ o₂ + n₂ ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    val32 m' base d k = val32 m base d k :=
  h.val32 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hd'

/-- What the rows change. -/
def clobW : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- Where the rows keep their multiplier: a word apart from the operands. -/
structure MultLay (N size acc a b mo inv mult : Nat) : Prop where
  le : mult + 4 ≤ size
  sacc : mult + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ mult
  sa : a + 4 * N ≤ mult ∨ mult + 4 ≤ a
  sb : b + 4 * N ≤ mult ∨ mult + 4 ≤ b
  smo : mo + 4 * N ≤ mult ∨ mult + 4 ≤ mo
  sinv : inv + 4 ≤ mult ∨ mult + 4 ≤ inv

/-- The invariant of the loop of `mul` after `i` rows, as `LoopInv`. -/
structure LoopInvW (base : Addr) (N acc a b m mult i : Nat) (s t : State) : Prop where
  ebp : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * i)
  out : Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem t.mem
  keeps : Keeps clobW s t
  lt : val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m
  cong : ∃ U, 2 ^ (32 * i) * val32 t.mem base (acc + 4 * i) (2 * N + 1 - i) =
    val32 s.mem base a i * val32 s.mem base b N + U * m

/-- An iteration of the loop, from its multiplier `x` in `[mult]` on. -/
theorem rowTail_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {N acc a b mo inv mult i m : Nat}
    (hL : MulLay N size acc a b mo) (hX : MultLay N size acc a b mo inv mult)
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : val32 s.mem base mo N = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m)
    (hT : val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.rowTail N acc b mo inv mult) s fun u =>
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) + w32 s.mem base mult * val32 s.mem base b N +
          q * m) ∧
      val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps clobW s u := by
  have hN : 0 < N := by omega_using [hi]
  have hn := hs.nowrap
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hX.le
  -- The layout's disjunctions stay in `hL` and `hX`: each side condition
  -- adds the ones it needs, as `omega` case-splits on every disjunction.
  have hmP : m < 2 ^ (32 * N) := hm ▸ val32_lt _ _ _ _
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hpow : 2 ^ (32 * (N + 2)) = 2 ^ (32 * N) * 2 ^ 64 := by rw [pow32_add]
  -- The window: the accumulator's words from `i`, of which only the low
  -- `N + 2` may be nonzero.
  obtain ⟨w, hw⟩ : ∃ w, 4 * i + acc = w := ⟨_, rfl⟩
  have ew : acc + 4 * i = w := by omega_using [hw]
  rw [ew] at hT
  have hsplit : ∀ mem : Mem, val32 mem base w (2 * N + 1 - i) =
      val32 mem base w (N + 2) + 2 ^ (32 * (N + 2)) * val32 mem base (w + 4 * (N + 2)) (N - 1 - i) := by
    intro mem
    rw [show 2 * N + 1 - i = (N + 2) + (N - 1 - i) by omega_using [hi], val32_append]
  have habove : val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hsplit] at hT
    rcases Nat.eq_zero_or_pos (val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i)) with h | h
    · exact h
    · have : 2 ^ (32 * (N + 2)) * 1 ≤ 2 ^ (32 * (N + 2)) * val32 s.mem base (w + 4 * (N + 2)) (N - 1 - i) :=
        Nat.mul_le_mul_left _ h
      have : 2 * 2 ^ (32 * N) ≤ 2 ^ (32 * (N + 2)) := by rw [hpow]; omega_using []
      omega_arith
  have hTw : val32 s.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) := by
    rw [hsplit s.mem, habove]; omega_using []
  simp only [VG.Impl.Mont.X86.Dynamic.rowTail]
  have hp₁ := hp
  have hs₁ := hs
  have k₁ : Keeps clobW s s := Keeps.refl _ _
  -- The window `+= a_i B`.
  have hlt₁ : val32 s.mem base w (N + 2) + w32 s.mem base mult * val32 s.mem base b N <
      2 ^ (32 * (N + 2)) := by
    rw [hTw, hpow]
    have := (s.mem.readW (off base mult) 32).isLt
    have : w32 s.mem base mult * val32 s.mem base b N ≤ (2 ^ 32 - 1) * val32 s.mem base b N :=
      Nat.mul_le_mul_right _ (by simp only [w32]; omega_using [this])
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega_arith
  refine WP.seq (WP.mono (mulRowW_ok hs₁ hN hp₁ hw hL.b_le (by omega_arith) (by have := hL.sb; omega_arith) hX.le
    (by have := hX.sacc; omega_arith) hlt₁) fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have k₂ : Keeps clobW s s₂ := k₁.trans (K₂.mono (by decide))
  have hs₂ := hs.of_keeps k₂ (by decide)
  have hp₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact hp₁
  rw [hTw] at V₂
  -- `[mult] = q`, from the window's low word.
  refine WP.seq (WP.mono (redDigit_ok hs₂ hp₂ (by omega_arith) hv hX.le) fun s₆ ⟨q₆, K₆, O₆⟩ => ?_)
  have k₆ : Keeps clobW s s₆ := k₂.trans (K₆.mono (by decide))
  have hs₆ := hs.of_keeps k₆ (by decide)
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.1 _ (by decide), K₆.1 _ (by decide)]; exact hp₂
  have t0 : (s₂.mem.readW (off base (4 * i + acc)) 32).toNat = val32 s₂.mem base w (N + 2) % 2 ^ 32 := by
    rw [hw, val32]
    have := (s₂.mem.readW (off base w) 32).isLt
    simp only [w32]
    omega_using []
  have inv₂ : w32 s₂.mem base inv = w32 s.mem base inv := by
    rw [O₂.w32 (by omega_arith) (by omega_arith)]
  rw [inv₂] at q₆
  have q₆' : w32 s₆.mem base mult = val32 s₂.mem base w (N + 2) % 2 ^ 32 * w32 s.mem base inv % 2 ^ 32 := by
    rw [q₆, show w32 s₂.mem base (4 * i + acc) = _ from t0]
  -- The window `+= q m`.
  have win₆ : val32 s₆.mem base w (N + 2) = val32 s₂.mem base w (N + 2) :=
    O₆.val32 (by have := hX.sacc; omega_arith) (by omega_arith)
  have hmo₆ : val32 s₆.mem base mo N = m := by
    rw [O₆.val32 (by have := hX.smo; omega_arith) (by omega_arith),
      O₂.val32 (by have := hL.smo; omega_arith) (by omega_arith), hm]
  have hq : w32 s₆.mem base mult < 2 ^ 32 := (s₆.mem.readW (off base mult) 32).isLt
  have hlt₆ : val32 s₆.mem base w (N + 2) + w32 s₆.mem base mult * val32 s₆.mem base mo N <
      2 ^ (32 * (N + 2)) := by
    rw [win₆, V₂, hmo₆, hpow]
    have hW1 := row_lt (q := 0) (a := w32 s.mem base mult) hT (s.mem.readW (off base mult) 32).isLt
      hB (by decide)
    have : w32 s₆.mem base mult * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega_using [hq])
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega_arith
  refine WP.seq (WP.mono (mulRowW_ok hs₆ hN hp₆ hw hL.mo_le (by omega_arith) (by have := hL.smo; omega_arith) hX.le
    (by have := hX.sacc; omega_arith) hlt₆) fun s₇ ⟨O₇, V₇, K₇⟩ => ?_)
  have k₇ : Keeps clobW s s₇ := k₆.trans (K₇.mono (by decide))
  have hp₇ : s₇.gpr .ebp = s₇.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [K₇.1 _ (by decide), K₇.1 _ (by decide)]; exact hp₆
  rw [win₆, V₂, hmo₆] at V₇
  -- `ebp += 4`, and the comparison.
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_movS rfl fun s₉ u₉ _ => ?_
  refine wp_addS rfl fun s₁₀ u₁₀ _ => ?_
  refine wp_cmpS rfl fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have k₁₁ : Keeps clobW s s₁₁ :=
    (((k₇.widen u₈.keeps).widen u₉.keeps).widen u₁₀.keeps).widen (f₁₁.keeps clob)
  have mem₁₁ : s₁₁.mem = s₇.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
  have edi₁₁ : s₁₁.gpr .edi = s₇.gpr .edi := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide)]
  have ebp₁₁ : s₁₁.gpr .ebp = s₇.gpr .ebp + 4 := by
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  have edx₁₀ : s₁₀.gpr .edx = s₇.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ (by decide)]
  have hN32 : 4 * N < 2 ^ 32 := by omega_arith
  -- The new window, and what changed.
  have hO : Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem s₁₁.mem := by
    rw [mem₁₁]
    have e₂ : Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem s₂.mem := fun x hx =>
      O₂ x (by
        have := hx _ (List.mem_cons_self ..)
        simp only at this
        omega_arith)
    have e₆ : Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s₂.mem s₆.mem := Outs.of_outside O₆ (by simp)
    have e₇ : Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s₆.mem s₇.mem := fun x hx =>
      O₇ x (by
        have := hx _ (List.mem_cons_self ..)
        simp only at this
        omega_arith)
    exact (e₂.trans e₆).trans e₇
  have habove' : val32 s₁₁.mem base (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [mem₁₁, O₇.val32 (by omega_arith) (by omega_arith),
      O₆.val32 (by have := hX.sacc; omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith),
      habove]
  have hW2 : val32 s₁₁.mem base w (N + 2) = val32 s.mem base w (2 * N + 1 - i) +
      w32 s.mem base mult * val32 s.mem base b N + w32 s₆.mem base mult * m := by
    rw [mem₁₁, V₇]
  have hlow : val32 s₁₁.mem base w (N + 2) % 2 ^ 32 = 0 := by
    rw [hW2, ← V₂, q₆', ← Nat.mod_add_mod]; exact mont_low32 _ _ _ hinv
  have hT' : val32 s₁₁.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
      val32 s₁₁.mem base (w + 4) (N + 1) := by
    rw [show acc + 4 * (i + 1) = w + 4 by omega_using [ew], show 2 * N + 1 - (i + 1) = (N + 1) + (N - 1 - i) by omega_using [hi],
      val32_append, show w + 4 + 4 * (N + 1) = w + 4 * (N + 2) by omega_using [], habove', Nat.mul_zero, Nat.add_zero]
  have hsh : val32 s₁₁.mem base w (N + 2) = w32 s₁₁.mem base w + 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) :=
    rfl
  have h32 : w32 s₁₁.mem base w < 2 ^ 32 := (s₁₁.mem.readW (off base w) 32).isLt
  have hW : 2 ^ 32 * val32 s₁₁.mem base (w + 4) (N + 1) = val32 s₁₁.mem base w (N + 2) := by omega_using [hlow, hsh, h32]
  have hlt := row_lt (a := w32 s.mem base mult) hT (s.mem.readW (off base mult) 32).isLt hB hq
  refine ⟨?_, ?_, hO, ⟨w32 s₆.mem base mult, ?_⟩, ?_, k₁₁⟩
  · rw [ebp₁₁, edi₁₁, hp₇, row_ebp]
  · have ebp₁₀ : s₁₀.gpr .ebp = s₇.gpr .ebp + 4 := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
    rw [z₁₁, ebp₁₀, edx₁₀, hp₇, row_zf _ hi hN32]
  · rw [hT', hW, hW2, ew]
  · rw [hT']
    rw [← hW2, ← hW] at hlt
    omega_using [hlt]

/-- An iteration of the loop. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {N acc a b mo inv mult i m : Nat}
    (hL : MulLay N size acc a b mo) (hX : MultLay N size acc a b mo inv mult)
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv) (hi : i < N)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hm : val32 s.mem base mo N = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m)
    (hT : val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) < 2 * m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv mult) s fun u =>
      u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outs base [(acc, 4 * (2 * N + 1)), (mult, 4)] s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) + w32 s.mem base (a + 4 * i) * val32 s.mem base b N +
          q * m) ∧
      val32 u.mem base (acc + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps clobW s u := by
  have hn := hs.nowrap
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hX.le
  simp only [VG.Impl.Mont.X86.Dynamic.row]
  refine WP.seq (wp_movS (readSrc_at hs hp (d := a) (by omega_arith)) fun s₀ u₀ _ => ?_)
  have hs₀ := hs.of_keeps u₀.keeps (by decide)
  refine wp_storeS (hs₀.ea (d := mult) (by omega_arith)) (hs₀.write (d := mult) (n := 4) (by omega_arith))
    fun s₁ m₁ => WP.block_nil ?_
  have k₁ : Keeps clobW s s₁ := (u₀.keeps.mono (by decide)).widen (m₁.keeps [])
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr .ebp = s₁.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [m₁.gpr, u₀.other _ (by decide), u₀.other _ (by decide)]; exact hp
  have O₁ : Outside base mult 4 s.mem s₁.mem := by
    rw [m₁.mem, u₀.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have mult₁ : w32 s₁.mem base mult = w32 s.mem base (a + 4 * i) := by
    rw [m₁.mem, w32_write_self, u₀.gpr, Nat.add_comm a]
  have win₁ : val32 s₁.mem base (acc + 4 * i) (2 * N + 1 - i) = val32 s.mem base (acc + 4 * i) (2 * N + 1 - i) :=
    O₁.val32 (by have := hX.sacc; omega_arith) (by omega_arith)
  have b₁ : val32 s₁.mem base b N = val32 s.mem base b N :=
    O₁.val32 (by have := hX.sb; omega_arith) (by omega_arith)
  have mo₁ : val32 s₁.mem base mo N = m := by
    rw [O₁.val32 (by have := hX.smo; omega_arith) (by omega_arith), hm]
  have inv₁ : w32 s₁.mem base inv = w32 s.mem base inv :=
    O₁.w32 (by have := hX.sinv; omega_arith) (by omega_arith)
  refine WP.mono (rowTail_ok hs₁ hL hX hv hsepInv hi hp₁ mo₁ (by rw [inv₁]; exact hinv) (by rw [b₁]; exact hB)
    (by rw [win₁]; exact hT)) fun u ⟨hp', hz, O, ⟨q, hq⟩, hT', K⟩ =>
      ⟨hp', hz, (Outs.of_outside O₁ (by simp)).trans O, ⟨q, by rw [hq, win₁, mult₁, b₁]⟩, hT', k₁.trans K⟩

/-- The loop of `mul`: from the invariant at 0 to the invariant at `N`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {N acc a b mo inv mult m : Nat}
    (hL : MulLay N size acc a b mo) (hX : MultLay N size acc a b mo inv mult)
    (hv : inv + 4 ≤ size) (hsepInv : inv + 4 ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ inv) (hN : 0 < N)
    (hm : val32 s.mem base mo N = m) (hinv : (m * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b N < m) {t : State} (h0 : LoopInvW base N acc a b m mult 0 s t) :
    WP isa (.loop (VG.Impl.Mont.X86.Dynamic.row N acc a b mo inv mult) .ne) t fun u =>
      LoopInvW base N acc a b m mult N s u := by
  have := hL.acc_le
  have := hL.a_le
  have := hL.b_le
  have := hL.mo_le
  have := hX.le
  have hn := hs.nowrap
  refine WP.loop (M := isa)
    (fun n t' => ∃ i, n = N - i ∧ i < N ∧ LoopInvW base N acc a b m mult i s t') ?_ N t ⟨0, rfl, hN, h0⟩
  rintro n t' ⟨i, rfl, hi, I⟩
  have ht := hs.of_keeps I.keeps (by decide)
  have hm' : val32 t'.mem base mo N = m := by
    rw [outs2_val32 I.out (by have := hL.smo; omega_arith) (by have := hX.smo; omega_arith) (by omega_arith), hm]
  have hb' : val32 t'.mem base b N = val32 s.mem base b N :=
    outs2_val32 I.out (by have := hL.sb; omega_arith) (by have := hX.sb; omega_arith) (by omega_arith)
  have ha' : w32 t'.mem base (a + 4 * i) = w32 s.mem base (a + 4 * i) :=
    outs2_w32 I.out (by have := hL.sa; omega_arith) (by have := hX.sa; omega_arith) (by omega_arith)
  have hinv' : (m * w32 t'.mem base inv + 1) % 2 ^ 32 = 0 := by
    rw [outs2_w32 I.out hsepInv (by have := hX.sinv; omega_arith) (by omega_arith)]; exact hinv
  refine WP.mono (row_ok ht hL hX hv hsepInv hi I.ebp hm' hinv' (hb' ▸ hB) I.lt)
    fun u ⟨hp, hz, O, ⟨q, hq⟩, hT, K⟩ => ?_
  rw [hb', ha'] at hq
  have I' : LoopInvW base N acc a b m mult (i + 1) s u := by
    refine ⟨hp, I.out.trans O, I.keeps.trans K, hT, ?_⟩
    obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + 2 ^ (32 * i) * q, ?_⟩
    rw [pow32_succ, val32_succ, Nat.mul_assoc, Nat.mul_left_comm, hq]
    generalize 2 ^ (32 * i) = P at *
    grind
  by_cases hNi : i + 1 = N
  · refine .inl ⟨by simp only [eval, hz, hNi, decide_true, Option.map_some, Bool.not_true], hNi ▸ I'⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hNi, Option.map_some, Bool.not_false],
      N - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hNi], I'⟩

end VG.Proof.Mont.X86.Dynamic

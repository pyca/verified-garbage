module

public import VerifiedGarbage.Proof.Rsa.Arm.KdStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # The key checks' division on ARMv7 (`KeyDiv.divW`): Algorithm D in place -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm)

/-! ## The arithmetic of the fold -/

/-- The window at word `j` before its step: the remainder of the words above it
shifted up a word, plus word `j` of `X`. -/
abbrev winY (X M j : Nat) : Nat := X / 2 ^ (32 * (j + 1)) % M * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32

theorem winY_lt {X M j : Nat} (hM : 0 < M) : winY X M j < M * 2 ^ 32 := by
  have h1 := Nat.mod_lt (X / 2 ^ (32 * (j + 1))) hM
  have h2 := Nat.mod_lt (X / 2 ^ (32 * j)) (Nat.two_pow_pos 32)
  have := Nat.mul_le_mul_right (2 ^ 32) (show X / 2 ^ (32 * (j + 1)) % M + 1 ≤ M by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  simp only [winY]; omega

/-- A step: the window's remainder is that of the words from `j`. -/
theorem winY_mod (X M j : Nat) : winY X M j % M = X / 2 ^ (32 * j) % M := by
  have e : X / 2 ^ (32 * j) = X / 2 ^ (32 * (j + 1)) * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32 := by
    rw [show (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 by rw [Nat.mul_succ, Nat.pow_add],
      ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  conv => rhs; rw [e]
  simp only [winY]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- The value of `[r]` a word down: the words below `j` and the remainder of those from `j`. -/
theorem fold_next (X M j : Nat) :
    X % 2 ^ (32 * (j + 1)) + 2 ^ (32 * (j + 1)) * (X / 2 ^ (32 * (j + 1)) % M) =
      X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j := by
  have e1 : X % 2 ^ (32 * (j + 1)) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % 2 ^ 32) := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
  have e2 : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  simp only [winY]
  generalize X / 2 ^ (32 * (j + 1)) % M = A
  rw [e1, e2, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (2 ^ 32) A]
  omega

/-- The start: below `M`, the words above `j` are their own remainder. -/
theorem fold_top {X M j : Nat} (h : X / 2 ^ (32 * (j + 1)) < M) :
    X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j = X := by
  have e : X / 2 ^ (32 * j) = X / 2 ^ (32 * (j + 1)) * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32 := by
    rw [show (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 by rw [Nat.mul_succ, Nat.pow_add],
      ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  simp only [winY]
  rw [Nat.mod_eq_of_lt h, ← e, Nat.mod_add_div]

/-- Three parts of a number, from its value: the low `L < 2^K`, the middle `Y` of `J` bits and
the high `H = 0` when the whole is `L' + 2^K Y'` for `L' < 2^K` and `Y' < 2^J`. -/
theorem parts_unique {K J L Y H L' Y' : Nat} (hL : L < 2 ^ K) (hL' : L' < 2 ^ K)
    (hY' : Y' < 2 ^ J) (h : L + 2 ^ K * (Y + 2 ^ J * H) = L' + 2 ^ K * Y') : L = L' ∧ Y = Y' ∧ H = 0 := by
  have hK := Nat.two_pow_pos K
  have m1 := congrArg (· % 2 ^ K) h
  have d1 := congrArg (· / 2 ^ K) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL'] at m1
  simp only [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hL, Nat.div_eq_of_lt hL', Nat.zero_add] at d1
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · subst h0; exact ⟨m1, by omega, rfl⟩
  · have := Nat.mul_le_mul_left (2 ^ J) h0; omega

/-! ## Frames -/

/-- A frame widened to ranges that contain its own. -/
theorem Outs.widen {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' := by
  intro x hx
  refine h x fun r hr' => ?_
  obtain ⟨r', hr'', h1, h2⟩ := hr r hr'
  have := hx r' hr''
  omega

/-- Words apart from a step's frame. -/
theorem step_val {B : BitVec 32} {w r t u j : Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j) m m') {o k : Nat}
    (ht : o + 4 * k ≤ arr w t ∨ arr w t + S w ≤ o) (hu : o + 4 * k ≤ arr w u ∨ arr w u + S w ≤ o)
    (hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ o)
    (hwin : o + 4 * k ≤ arr w r + 4 * j ∨ arr w r + 4 * j + 4 * (w / 2 + 1) ≤ o) (fit : o + 4 * k ≤ 2 ^ 64) :
    val32 m' (State.addr B) o k = val32 m (State.addr B) o k := by
  refine Outs.val32 F (fun x hx => ?_) fit
  simp only [stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | rfl
  · rcases hy with rfl | rfl
    · exact ht
    · exact hu
  · refine .inr ?_
    dsimp only
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sMk, sQ, sU0, sU2, sJ, VG.Impl.Rsa.Arm.Keys.sC, VG.Impl.Rsa.Arm.Keys.hdr] at hs ⊢ <;> omega
  · exact hwin

/-- A header word apart from a step's frame. -/
theorem step_slot {B : BitVec 32} {w r t u j : Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j) m m') {e : Nat} (he : e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr)
    (hd : ∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) F (fun x hx => ?_) (by simp only [VG.Impl.Rsa.Arm.Keys.hdr] at he; omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [stepRanges, ranges, List.mem_append, List.mem_map] at hx
  rcases hx with (⟨y, -, rfl⟩ | ⟨d, hd', rfl⟩) | hx
  · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w y := Nat.le_add_right _ _; dsimp only; omega
  · exact hd d hd'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _; dsimp only; omega

/-! ## The loop -/

/-- What the steps read and never change: `w` (16), `P = 2^z` normalizing `M = [m]`
(`w / 2` words), `d`, `d₁` and `v`, `[0]` zero and `[nm] = -M`. -/
structure Prepped (x : State) (B : BitVec 32) (w m nm z M : Nat) : Prop where
  c16 : slot x.mem B 16 = w
  hM : val32 x.mem (State.addr B) (arr w m) (w / 2) = M
  hz : z ≤ 31
  hP : slot x.mem B sP = 2 ^ z
  hMP : M * 2 ^ z < 2 ^ (32 * (w / 2))
  hD : slot x.mem B sD * 2 ^ 32 + slot x.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2))
  hDn : 2 ^ 31 ≤ slot x.mem B sD
  hV : slot x.mem B sV = (2 ^ 64 - 1) / slot x.mem B sD - 2 ^ 32
  z0 : val32 x.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0
  hnm : val32 x.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M

theorem Prepped.step {x x' : State} {B : BitVec 32} {Z w N r m t nm u z M j : Nat} (p : Prepped x B w m nm z M)
    (h : Ws x B Z w N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u)
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hnr : nm ≠ r) (hnt : nm ≠ t) (hnu : nm ≠ u)
    (hj : j + w / 2 ≤ w) (F : Outs (State.addr B) (stepRanges w r t u j) x.mem x'.mem) :
    Prepped x' B w m nm z M := by
  have := h.wle
  have gm := h.fit64 hm
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  have dmr := arr_disj (w := w) hmr
  have dmt := arr_disj (w := w) hmt
  have dmu := arr_disj (w := w) hmu
  have d0r := arr_disj (w := w) hr0
  have d0t := arr_disj (w := w) ht0
  have d0u := arr_disj (w := w) hu0
  have dnr := arr_disj (w := w) hnr
  have dnt := arr_disj (w := w) hnt
  have dnu := arr_disj (w := w) hnu
  simp only [S] at gm g0 gn dmr dmt dmu d0r d0t d0u dnr dnt dnu
  have sl : ∀ {e}, e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr →
      (∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) →
      slot x'.mem B e = slot x.mem B e := fun he hd => step_slot F he hd
  have hs : ∀ a, VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := fun _ => Nat.le_add_right _ _
  refine ⟨?_, ?_, p.hz, ?_, p.hMP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sl (by decide) (by decide)]; exact p.c16
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs m) (by omega) (by omega)]; exact p.hM
  · rw [sl (by decide) (by decide)]; exact p.hP
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hD
  · rw [sl (by decide) (by decide)]; exact p.hDn
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hV
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs 0) (by omega) (by omega)]; exact p.z0
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs nm) (by omega) (by omega)]; exact p.hnm

theorem Prepped.M_pos {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) : 0 < M :=
  Nat.pos_of_ne_zero fun e => by
    have hD := p.hD
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) p.hDn; omega

theorem Prepped.M_lt {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) :
    M < 2 ^ (32 * (w / 2)) :=
  Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) p.hMP

/-- The loop's invariant at the window at word `j`: `[r]`'s `w + 1` words are `X`'s below `j`
and `winY X M j` from `j`; `Prepped`; and only `[r]`, `[t]`, `[u]` and the steps' header words
changed since `s0`. -/
structure DivSt (s0 x : State) (B : BitVec 32) (Z w N r m t nm u z M X j : Nat) : Prop where
  ws : Ws x B Z w N
  pre : Prepped x B w m nm z M
  J : slot x.mem B sJ = 4 * j
  hj : j + w / 2 ≤ w
  val : val32 x.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j
  keep : Keep B w [r, t, u] [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x.mem
  rest : Rest divRegs s0 x

/-- A step from the invariant: the remainder of `X`'s words from `j` there. -/
theorem stepD_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N)
    (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t)
    (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (hdw : 3 ≤ w / 2) :
    WP isa (step r m t nm u) x fun x' => Ws x' B Z w N ∧ Prepped x' B w m nm z M ∧
      slot x'.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      val32 x'.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % M) ∧
      Keep B w [r, t, u] [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x'.mem ∧ Rest divRegs s0 x' := by
  have := I.ws.wle
  have hj := I.hj
  have gr := I.ws.fit64 hr
  have dt := arr_disj (w := w) hrt
  have du := arr_disj (w := w) hru
  simp only [S] at gr dt du
  have hM0 := I.pre.M_pos
  have hMl := I.pre.M_lt
  have hWY : winY X M j < 2 ^ (32 * (w / 2 + 1)) := by
    have := winY_lt (X := X) (j := j) hM0
    rw [show 32 * (w / 2 + 1) = 32 * (w / 2) + 32 by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_of_lt hMl))
  have e1 : w + 1 = j + ((w / 2 + 1) + (w - j - w / 2)) := by omega
  have dec := I.val
  rw [e1, val32_append, val32_append] at dec
  obtain ⟨-, hwin, hhigh⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY dec
  refine WP.mono (step_ok I.ws hr hm ht hnm hu hN hrt hru htu hmt htn hnu ht0 hu0 I.pre.c16 hdw I.J hj hwin
    I.pre.hM (winY_lt hM0) I.pre.hz I.pre.hP I.pre.hMP I.pre.hD I.pre.hDn I.pre.hV I.pre.z0 I.pre.hnm)
    fun x' ⟨W', V', J', F', R'⟩ => ⟨W', I.pre.step I.ws hm hnm hN hmr hmt hmu hr0 ht0 hu0 hnr htn.symm hnu hj F',
      J', ?_, ?_, I.rest.trans R'⟩
  · have hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _
    have hlow := I.val
    rw [e1, val32_append, val32_append, V', winY_mod,
      step_val F' (o := arr w r) (k := j) (by simp only [S]; omega) (by simp only [S]; omega) hs (by omega)
        (by omega),
      step_val F' (o := arr w r + 4 * j + 4 * (w / 2 + 1)) (k := w - j - w / 2) (by simp only [S]; omega)
        (by simp only [S]; omega) (by omega) (by omega) (by omega), hhigh]
    rw [e1, val32_append, val32_append, hhigh, hwin] at hlow
    obtain ⟨hl, -, -⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY hlow
    rw [hl, Nat.mul_zero, Nat.add_zero]
  · refine I.keep.trans (show Keep B w [r, t, u] _ x.mem x'.mem from Outs.widen F' fun q hq => ?_)
    simp only [stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hq ⊢
    rcases hq with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | rfl
    · exact ⟨_, .inl ⟨y, by rcases hy with rfl | rfl <;> simp, rfl⟩, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, .inr ⟨d, hd, rfl⟩, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, .inl ⟨r, by simp, rfl⟩, by dsimp only; omega, by dsimp only; simp only [S]; omega⟩

theorem Prepped.of_mem {x x' : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M)
    (e : x'.mem = x.mem) : Prepped x' B w m nm z M := by
  obtain ⟨a, b, c, d, f, g, i, k, l, n⟩ := p
  exact ⟨e ▸ a, e ▸ b, c, e ▸ d, f, e ▸ g, e ▸ i, e ▸ k, e ▸ l, e ▸ n⟩

/-- The loop: the steps at words `j`, …, `1`, while the window's offset, a word down, is not zero. -/
theorem loop_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) (hj1 : 1 ≤ j) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) :
    WP isa (.loop (.seq (step r m t nm u) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) .ne) x
      fun y => DivSt s0 y B Z w N r m t nm u z M X 0 := by
  refine WP.loop (M := isa) (fun n y => DivSt s0 y B Z w N r m t nm u z M X n ∧ 1 ≤ n) ?_ j x ⟨I, hj1⟩
  rintro n y ⟨In, hn⟩
  have := In.ws.wle
  have hjn := In.hj
  rw [WP.seq_iff]
  refine WP.mono (stepD_ok In hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw)
    fun y1 ⟨W1, P1, J1, V1, K1, R1⟩ => ?_
  refine wp_ldrSlot W1 (d := sJ) (by decide) fun y2 u2 => ?_
  refine wp_cmp (op2_imm (by decide)) fun y3 f3 hz3 => WP.block_nil ?_
  have r0v : y2.gpr .r0 = BitVec.ofNat 32 (4 * n) - 4 := by
    rw [u2.gpr]; apply BitVec.eq_of_toNat_eq; exact J1
  have e4 : (BitVec.ofNat 32 (4 * n) - 4).toNat = 4 * (n - 1) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega
  have m3 : y3.mem = y1.mem := f3.mem.trans u2.mem
  have W3 : Ws y3 B Z w N := (W1.of_upd u2 (by decide) (by decide) (by decide)).of (by rw [f3.gpr])
    (by rw [f3.gpr]) (by rw [f3.gpr]) f3.wr
  have R3 : Rest divRegs s0 y3 := R1.trans ((u2.rest (by decide)).trans (f3.rest _))
  have st : ∀ k, n = k + 1 → DivSt s0 y3 B Z w N r m t nm u z M X k := fun k hk => by
    subst hk
    refine ⟨W3, P1.of_mem m3, ?_, by omega, ?_, by rw [m3]; exact K1, R3⟩
    · simp only [slot]; rw [m3]; simp only [slot] at J1; rw [J1, e4]; rfl
    · rw [m3, V1, fold_next]
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · right
    refine ⟨?_, n - 1, by omega, st (n - 1) (by omega), by omega⟩
    change some (!y3.z) = some true
    rw [hz3, r0v, show BitVec.ofNat 32 (4 * n) - 4 - 0 = BitVec.ofNat 32 (4 * n) - 4 from BitVec.sub_zero _]
    have : BitVec.ofNat 32 (4 * n) - 4 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [e4] at this; simp at this; omega
    rw [show (BitVec.ofNat 32 (4 * n) - 4 == 0) = false from beq_eq_false_iff_ne.mpr this]; rfl
  · left
    have n1 : n = 1 := by omega
    subst n1
    refine ⟨?_, st 0 rfl⟩
    change some (!y3.z) = some false
    rw [hz3, r0v]; decide

end VG.Proof.Rsa.Arm.KeyDiv

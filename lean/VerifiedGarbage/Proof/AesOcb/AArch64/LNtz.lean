import VerifiedGarbage.Proof.AesOcb.AArch64.Args

/-!
# AES-OCB on AArch64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `x25`), shifted right
once more each time (in `x11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `x11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt)

theorem and1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v &&& 1#64 = BitVec.ofNat 64 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_of_lt hv, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat_of_lt (by omega)]

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ∉ ntzRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `x12 ← x14 ∧ 1`, after `x14 ← v`. -/
theorem low1_ok (s : State) {v : Nat} (hv : v < 2 ^ 64) (h14 : s.gpr .x14 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa low1 s = some s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (v % 2) ∧ s'.gpr .x14 = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [low1], ?_, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h14, and1 hv]
  · simp [gpr_write, h14]
  · simp [gpr_write, h1]
  all_goals rfl

/-- Continue the public-index doubling loop from any already computed L_a. -/
theorem lNtzLoop_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i a : Nat} (hi' : i < 2^64)
    (hpos : 0 < i / 2^a) (he : i / 2^a % 2 = 0) (hntz : ntz i = a + ntz (i / 2^a))
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (i / 2^a))
    (hl : blockAtMem s.mem (W + BitVec.ofNat 64 lO) = lAt l a) :
    WP isa (.loop (.block (dbl .x19 lO lO ++ ([.lsr .x .x14 .x14 1] : List Instr) ++ low1)) (.zero .x .x12)) s
      (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ∉ ntzRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ a) _
    ⟨a, rfl, hpos, he, hntz, h14, Frame.refl _ _, hl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, x14, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h19t : t.gpr .x19 = W := by rw [g _ (by decide), h19]
  obtain ⟨t₁, runt₁, D₁⟩ := dbl_ok (s := t) (b := .x19) (a := lO) (d := lO) (by decide) (by decide) h19t h19t
    (by decide) (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [wr]; exact wW (by decide)) (by rw [wr]; exact wW (by decide))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt₂, x14₂', g₂', m₂', sp₂'', rd₂'', wr₂''⟩ : ∃ t₂, runBlock isa [.lsr .x .x14 .x14 1] t₁ = some t₂ ∧
      t₂.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ (∀ r, r ≠ .x14 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have x14₁ : t₁.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), x14]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x14₁, shr1 hv, e]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨t₃, runt₃, x12₃, x14₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := low1_ok t₂ (by omega) x14₂'
  refine WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, runt₁, Option.bind_some, runt₂,
    Option.bind_some, runt₃], ?_⟩
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [m₃, m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₃, m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ∉ ntzRegs → t₃.gpr r = s.gpr r := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r hr.2.2.2.1, g₂' r hr.2.2.2.2.2, D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [sp₃, sp₂'', D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [rd₃, rd₂'', D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [wr₃, wr₂'', D₁.wr, wr]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  have hv' : i / 2 ^ (j + 1) < 2 ^ 64 := by omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_zero x12₃ (by omega)).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', x14₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_zero x12₃ (by omega)).trans (by simp [hodd]), ⟨fr', ?_, g', sp', rd', wr'⟩⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]


theorem lNtz_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 64) (h25 : s.gpr .x25 = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := lO) (by decide) (by decide) h19
    (Proof.AesGcm.AArch64.in_left (wW (by decide))) (Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (wW (by decide)) (wW (by decide))
  obtain ⟨s₁', run₁', x14₁', g₁', m₁', sp₁', rd₁', wr₁'⟩ : ∃ s', runBlock isa [Impl.AesGcm.AArch64.mov .x14 .x25] s₁ =
      some s' ∧ s'.gpr .x14 = BitVec.ofNat 64 i ∧ (∀ r, r ≠ .x14 → s'.gpr r = s₁.gpr r) ∧ s'.mem = s₁.mem ∧
      s'.sp = s₁.sp ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
    have h25₁ : s₁.gpr .x25 = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), h25]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h25₁]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨s₂, run₂, x12₂, x14₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := low1_ok s₁' hi' x14₁'
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ∉ ntzRegs → t.gpr r = s₂.gpr r) → t.sp = s.sp →
      t.rd = s.rd → t.wr = s.wr → LNtzPost W l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        g₂ r hr.2.2.2.1, g₁' r hr.2.2.2.2.2, B₁.gpr r (by simp [hr.1, hr.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂, m₁']; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, m₁', B₁.val, hl0]
  have sp₂' : s₂.sp = s.sp := by rw [sp₂, sp₁', B₁.sp]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁', B₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁', B₁.wr]
  have h19₂ : s₂.gpr .x19 = W := by rw [g₂ _ (by decide), g₁' _ (by decide), B₁.gpr _ (by decide), h19]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₁',
    Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_zero x12₂ (by omega)) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂' rd₂' wr₂'))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  exact WP.mono (lNtzLoop_ok h19₂ (by rw [wr₂']; exact hw) hi' (a := 0)
    (by simpa using hi) (by simpa using he) (by simp) (by simpa using x14₂) v₂) fun t P =>
      post_of t (fr₂.trans P.frame) P.val P.gpr (P.sp.trans sp₂') (P.rd.trans rd₂') (P.wr.trans wr₂')

end VG.Proof.AesOcb.AArch64

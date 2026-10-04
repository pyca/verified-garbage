import VerifiedGarbage.Proof.AesOcb.X86_64.Args

/-!
# AES-OCB on x86-64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `rbp`), shifted right
once more each time (in `r11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `r11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesCcm.X86_64 (runBlock_append eval_e eval_ne toNat_ofNat_of_lt)

theorem even_zf {v : Nat} (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v &&& BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (v % 2 = 0) := by
  rw [sext1]
  have : BitVec.ofNat 64 v &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (v % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by decide), Nat.and_one_is_mod,
      toNat_ofNat_of_lt (by omega)]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> decide

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem lNtz_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {l : Block} {i : Nat} (hi : 0 < i)
    (hi' : i < 2 ^ 64) (hbp : s.gpr .rbp = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost W l i s) := by
  have h15 := E.r15
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := lO) h15 (E.perm.wR (by decide))
    (E.perm.wR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  obtain ⟨s₂, run₂, r11₂, zf₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .r11 .rbp, .alu .test .r11 (.imm 1)] s₁ = some s₂ ∧
      s₂.gpr .r11 = BitVec.ofNat 64 i ∧ s₂.zf = some (decide (i % 2 = 0)) ∧
      (∀ r, r ≠ .r11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hbp₁ : s₁.gpr .rbp = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), hbp]
    refine ⟨_, by orun [hbp₁], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbp₁]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hbp₁, even_zf hi']
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t.gpr r = s₂.gpr r) →
      t.rd = s.rd → t.wr = s.wr → LNtzPost W l i s t := fun t fr v g rd wr =>
    ⟨fr, v, fun r h1 h2 h3 h4 h5 => by
      rw [g r h1 h2 h3 h4 h5, g₂ r h5, B₁.gpr r (by simp [h1, h2])], rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂]; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, B₁.val, hl0]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_e zf₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ _ _ _ _ => rfl) (by rw [rd₂, B₁.rd]) (by rw [wr₂, B₁.wr])))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simpa using hb)]
  have he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa) (c := .e)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t.gpr r = s₂.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using r11₂, fr₂, v₂,
      fun _ _ _ _ _ _ => rfl, by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, r11, fr, v, g, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h15t : t.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide),
    g₂ _ (by decide), B₁.gpr _ (by decide), h15]
  obtain ⟨t₁, runt₁, D₁⟩ := dbl_ok (s := t) (b := .r15) (a := lO) (d := lO) h15t h15t (by decide)
    (by rw [rd, wr]; exact E.perm.wR (by decide)) (by rw [rd, wr]; exact E.perm.wR (by decide))
    (by rw [wr]; exact E.perm.wW (by decide)) (by rw [wr]; exact E.perm.wW (by decide))
  have r11₁ : t₁.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), r11]
  obtain ⟨t₂, runt₂, r11₂', zf₂', g₂', m₂', rd₂', wr₂'⟩ : ∃ t₂,
      runBlock isa [.shift .shr .r11 1, .alu .test .r11 (.imm 1)] t₁ = some t₂ ∧
      t₂.gpr .r11 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ t₂.zf = some (decide (i / 2 ^ (j + 1) % 2 = 0)) ∧
      (∀ r, r ≠ .r11 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    refine ⟨_, by orun [r11₁], ?_, ?_, fun r h => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, r11₁, shr1 hv, e]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, r11₁, shr1 hv, e,
        even_zf (show i / 2 ^ j / 2 < 2 ^ 64 by omega)]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h, ite_false]
    all_goals rfl
  refine WP.of_runBlock ⟨t₂, by rw [runBlock_append, runt₁, Option.bind_some, runt₂], ?_⟩
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₂.mem := by
    rw [m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₂.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r11 → t₂.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [g₂' r h5, D₁.gpr r (by simp [h1, h2, h3, h4]), g r h1 h2 h3 h4 h5]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', r11₂', fr', v', g', by rw [rd₂', D₁.rd, rd], by rw [wr₂', D₁.wr, wr]⟩
  · left
    refine ⟨(eval_e zf₂').trans (by simp [hodd]), post_of t₂ fr' ?_ g' (by rw [rd₂', D₁.rd, rd])
      (by rw [wr₂', D₁.wr, wr])⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

end VG.Proof.AesOcb.X86_64

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverPre

/-!
# `vg_rsa_pkcs1_recover` on AArch64: the call's arguments

`pubArgs_ok`: the first block saves the registers, keeps `out`, `out_len`,
`k` and `hash` in `x19`–`x22`, and sets up the call (`AtCall`), in
`vg_rsa_pkcs1_verify`'s frame.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved save copyArg)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (fb wr_frame in_frame in_frame0 contains_fb saved_offs saved_ho Saved.congr
  Saved.write stackArgAddr_fb)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)

/-- At the call: the registers saved in their slots, `out`, `out_len`, `k`
and `hash` kept in `x19`–`x22`, and the arguments of
`vg_rsa_public_checked` set up. -/
structure AtCall (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = fb s + BitVec.ofNat 64 oEM1
  x1 : t.gpr .x1 = s.gpr .x3
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = s.gpr .x7
  x7 : t.gpr .x7 = s.gpr .x3
  x19 : t.gpr .x19 = s.gpr .x0
  x20 : t.gpr .x20 = s.gpr .x1
  x21 : t.gpr .x21 = s.gpr .x3
  x22 : t.gpr .x22 = ((s.gpr .x6).setWidth 32).setWidth 64
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  a0 : stackArg t 0 = stackArg s 1
  a1 : stackArg t 1 = stackArg s 2

theorem pubArgs_ok {K : Nat} {s u : State} (hp : PreR K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, r ≠ .x8 → u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block pubArgs) u (AtCall s) := by
  unfold pubArgs save
  simp only [List.cons_append, List.append_assoc]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]; exact wr_frame hwr (by have := saved_offs p hp'; unfold frameBytes; omega)
  refine Spill.save_ok (b := .x16) (l := saved) saved_ho hin ?_
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : State, u₂ = { u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr saved } :=
    ⟨_, rfl⟩
  rw [← hu₂]
  have m₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₂.mem := by
    rw [hu₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by have := saved_offs p hp'; unfold frameBytes; omega)
      (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [hu₂, e₁]
    refine Saved.congr (Spill.saveMem_saved (by decide) _ _ _) fun p hp' => ?_
    have : p.1 ≠ .x16 ∧ p.1 ≠ .x8 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this.1), hg _ this.2]
  simp only [List.nil_append, copyArg, List.cons_append]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_movw fun u₆ o₆ e₆ => ?_
  have O₆ : Only [.x19, .x20, .x21, .x22] u₂ u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have sp₆ : u₆.sp = fb s := by rw [O₆.sp, hu₂]; show u₁.sp = _; rw [o₁.sp, hsp]
  have rd₆ : u₆.rd = s.rd := by rw [O₆.rd, hu₂]; show u₁.rd = _; rw [o₁.rd, hrd]
  have wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr, hu₂]; show u₁.wr = _; rw [o₁.wr, hwr]
  have a₁ : u₆.sp + BitVec.ofNat 64 (frameBytes + 8 * 1) = stackArgAddr s 1 := by rw [sp₆, stackArgAddr_fb]
  have in₁ : InRegions (u₆.rd ++ u₆.wr) (stackArgAddr s 1) 8 := by
    rw [rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₁]; exact in₁) fun u₇ o₇ e₇ => ?_
  rw [a₁, O₆.mem, arg_frame hp m₂ (by decide)] at e₇
  have g₂ : ∀ r, u₂.gpr r = u₁.gpr r := fun r => by rw [hu₂]
  have x16₇ : u₇.gpr .x16 = fb s := by rw [o₇.get .x16, O₆.get .x16, g₂, e₁]
  refine wp_strx (by decide) (by rw [x16₇, BitVec.add_zero]) (by rw [o₇.wr, wr₆]; exact in_frame0 _ _ (by decide))
    fun u₈ m₈ => ?_
  have m₈' : Frame [⟨fb s, frameBytes⟩] s.mem u₈.mem := by
    rw [m₈.mem, o₇.mem, O₆.mem]
    exact m₂.writeW (List.mem_singleton_self _) _ (contains_fb s (by decide))
  have a₂ : u₈.sp + BitVec.ofNat 64 (frameBytes + 8 * 2) = stackArgAddr s 2 := by
    rw [m₈.sp, o₇.sp, sp₆, stackArgAddr_fb]
  have in₂ : InRegions (u₈.rd ++ u₈.wr) (stackArgAddr s 2) 8 := by
    rw [m₈.rd, o₇.rd, rd₆]; exact arg_in hp (Covers.left (Covers.refl _)) (by decide)
  refine wp_ldrSp (by decide) (by rw [a₂]; exact in₂) fun u₉ o₉ e₉ => ?_
  rw [a₂, arg_frame hp m₈' (by decide)] at e₉
  have x16₉ : u₉.gpr .x16 = fb s := by rw [o₉.get .x16, m₈.gpr, x16₇]
  refine wp_strx (by decide) (by rw [x16₉]) (by rw [o₉.wr, m₈.wr, o₇.wr, wr₆]; exact in_frame _ _ (by decide))
    fun u₁₀ m₁₀ => ?_
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_addSp (by decide) fun u₁₄ o₁₄ e₁₄ => wp_nil ?_
  have h₁₀ : ∀ r, r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] → u₁₀.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [m₁₀.gpr, o₉.gpr r (by simpa using hr.1), m₈.gpr, o₇.gpr r (by simpa using hr.1),
      O₆.gpr r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), g₂, o₁.gpr r (by simpa using hr.2.1),
      hg r hr.1]
  have hO : Only [.x1, .x6, .x7, .x0] u₁₀ u₁₄ := (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))).mono
  have k₁₉ : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], u₁₄.gpr r = u₆.gpr r := by
    intro r hr
    have : r ∉ [Reg.x1, .x6, .x7, .x0] ∧ r ≠ .x8 := by revert r; decide
    rw [hO.gpr r this.1, m₁₀.gpr, o₉.gpr r (by simpa using this.2), m₈.gpr, o₇.gpr r (by simpa using this.2)]
  have sp₁₀ : u₁₀.sp = fb s := by rw [m₁₀.sp, o₉.sp, m₈.sp, o₇.sp, sp₆]
  have u₁₃sp : u₁₃.sp = fb s := by rw [o₁₃.sp, o₁₂.sp, o₁₁.sp, sp₁₀]
  have mem₁₀ : u₁₀.mem = (u₈.mem).writeW (fb s + BitVec.ofNat 64 8) (stackArg s 2) := by
    rw [m₁₀.mem, o₉.mem, e₉]
  have mem₈ : u₈.mem = (u₂.mem).writeW (fb s) (stackArg s 1) := by
    rw [m₈.mem, o₇.mem, O₆.mem, e₇]
  refine ⟨?sp, ?rd, ?wr, ?x0, ?x1, ?x2, ?x3, ?x4, ?x5, ?x6, ?x7, ?x19, ?x20, ?x21, ?x22, ?hi, ?v, ?mem, ?sv, ?a0,
    ?a1⟩
  case sp => rw [o₁₄.sp, u₁₃sp]
  case rd => rw [hO.rd, m₁₀.rd, o₉.rd, m₈.rd, o₇.rd, rd₆]
  case wr => rw [hO.wr, m₁₀.wr, o₉.wr, m₈.wr, o₇.wr, wr₆]
  case x0 => rw [e₁₄, u₁₃sp]
  case x1 => rw [o₁₄.get .x1, o₁₃.get .x1, o₁₂.get .x1, e₁₁, h₁₀ .x3 (by decide)]
  case x2 => rw [hO.get .x2, h₁₀ .x2 (by decide)]
  case x3 => rw [hO.get .x3, h₁₀ .x3 (by decide)]
  case x4 => rw [hO.get .x4, h₁₀ .x4 (by decide)]
  case x5 => rw [hO.get .x5, h₁₀ .x5 (by decide)]
  case x6 => rw [o₁₄.get .x6, o₁₃.get .x6, e₁₂, o₁₁.get .x7, h₁₀ .x7 (by decide)]
  case x7 => rw [o₁₄.get .x7, e₁₃, o₁₂.get .x3, o₁₁.get .x3, h₁₀ .x3 (by decide)]
  case x19 => rw [k₁₉ .x19 (by decide), o₆.get .x19, o₅.get .x19, o₄.get .x19, e₃, g₂, o₁.get .x0,
    hg .x0 (by decide)]
  case x20 => rw [k₁₉ .x20 (by decide), o₆.get .x20, o₅.get .x20, e₄, o₃.get .x1, g₂, o₁.get .x1,
    hg .x1 (by decide)]
  case x21 => rw [k₁₉ .x21 (by decide), o₆.get .x21, e₅, o₄.get .x3, o₃.get .x3, g₂, o₁.get .x3,
    hg .x3 (by decide)]
  case x22 => rw [k₁₉ .x22 (by decide), e₆, o₅.get .x6, o₄.get .x6, o₃.get .x6, g₂, o₁.get .x6,
    hg .x6 (by decide)]
  case hi =>
    intro r hr
    have : r ∉ [Reg.x1, .x6, .x7, .x0] ∧ r ∉ [Reg.x8, .x16, .x19, .x20, .x21, .x22] := by
      revert r; decide
    rw [hO.gpr r this.1, h₁₀ r this.2]
  case v =>
    intro r hr
    rw [hO.vcs r hr, m₁₀.vcs r hr, o₉.vcs r hr, m₈.vcs r hr, o₇.vcs r hr, O₆.vcs r hr, hu₂]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem =>
    rw [hO.mem, mem₁₀]
    exact m₈'.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  case sv =>
    rw [hO.mem, mem₁₀, mem₈]
    exact Saved.write (d := 8) (Saved.write (d := 0) (by simpa using sv₂) (by decide) _ |> fun h => by
      simpa using h) (by decide) _
  case a0 =>
    show (u₁₄.mem).readW (u₁₄.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [o₁₄.sp, u₁₃sp, hO.mem, mem₁₀]
    simp only [Nat.mul_zero, BitVec.add_zero]
    rw [Mem.readW_writeW_sep (Offset.sep_base (fb s) (by decide) (by decide)) (by decide), mem₈]
    exact Mem.readW_writeW_self64 _ _ _
  case a1 =>
    show (u₁₄.mem).readW (u₁₄.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [o₁₄.sp, u₁₃sp, hO.mem, mem₁₀]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.RsaPkcs1Sig.AArch64.Rec

module

public import VerifiedGarbage.Proof.AesGcm.X86_64.InitP
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Convert
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Converting the cached powers in place at key setup, one pair per iteration -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Gcm.X86_64.Prepared
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Spec.Gcm (Block blockAt ctxH hpow PowersRepr PreparedPowersRepr)
open VG.Proof.Gcm.X86_64.Stitch (in_sub)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF ones consts_ok vinsSelf_ok)
open VG.Proof.Gcm.X86_64.StitchZR (preparedPower_eq)
open VG.Impl.Gcm.X86_64.Pclmul (revMask xInv poly)
open VG.Impl.AesGcm.X86_64 (ptr imm)
open VG.Impl.AesGcm.X86_64.Prepared (pair convert convertSetup)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)
open VG.Proof.AesGcm.X86_64 (imm_eq)

/-- Before pair `j`: `rdi` at it, `rax` at the end, and only completed pairs
differ from the original context. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * j)
  rax : s.gpr .rax = s₀.gpr .rdi + BitVec.ofNat 64 768
  gpr : ∀ r, r ≠ .rdi → r ≠ .rax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 32*j⟩] s₀.mem s.mem
  pairs : ∀ k < j, ∀ l < 2,
    s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256+32*k+16*l)) 128 =
      hInvF (hpow (ctxH s₀.mem (s₀.gpr .rdi)) (2*k+2-l))
  m0 : ∀ l < 2, s.lane .xmm0 l = revMask
  c8 : ∀ l < 2, s.lane .xmm8 l = xInv
  c9 : ∀ l < 2, s.lane .xmm9 l = ones

theorem toNat_add_lt {p : Addr} {d n : Nat} (hw : p.toNat + n ≤ 2 ^ 64) (hd : d < n) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  have := p.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at hw this ⊢
  omega

theorem conv_zf (p : Addr) {j : Nat} (hj : j ≤ 24) :
    ((p + BitVec.ofNat 64 (32 * j)) - (p + BitVec.ofNat 64 768) == 0) = decide (j = 24) := by
  by_cases h : j = 24
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have e2 := congrArg (· + (p + BitVec.ofNat 64 768)) e
    simp only [BitVec.sub_add_cancel] at e2
    have e3 : BitVec.ofNat 64 (32 * j) = BitVec.ofNat 64 768 :=
      (BitVec.add_right_inj p).mp (by simpa using e2)
    have := congrArg BitVec.toNat e3
    simp at this; omega

/-- The loop's step and test: `rdi` past the pair, compared with `rax`. -/
theorem next_run {p : Addr} {j : Nat} (hj : j < 24) {t : State}
    (hdi : t.gpr .rdi = p + BitVec.ofNat 64 (32 * j)) (hax : t.gpr .rax = p + BitVec.ofNat 64 768) :
    ∃ t', runBlock isa ([.alu .add .rdi (imm 32), .alu .cmp .rdi (.reg .rax)] : List Instr) t = some t' ∧
      t'.gpr .rdi = p + BitVec.ofNat 64 (32 * (j + 1)) ∧
      (∀ r, r ≠ .rdi → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      t'.xmm = t.xmm ∧ t'.ymmHi = t.ymmHi ∧ isa.eval .ne t' = some (decide (j + 1 ≠ 24)) := by
  have e : p + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 32 = p + BitVec.ofNat 64 (32 * (j + 1)) := by
    rw [Offset.add_add]; congr 2
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, hdi, imm_eq (show 32 < 2 ^ 31 by decide), e]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals try simp [mem_arithFlags, mem_setReg, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    xmm_arithFlags, xmm_setReg, ymmHi_arithFlags, ymmHi_setReg]
  show Option.map (!·) (some _) = _
  simp only [gpr_setReg, gpr_arithFlags, ite_true, hdi, hax, imm_eq (show 32 < 2 ^ 31 by decide),
    Option.map_some, reduceCtorEq, ite_false, e]
  rw [conv_zf p (by omega)]
  by_cases h23 : j = 23 <;> simp [h23]

/-- One iteration: pair `j` converted, `rdi` past it. -/
theorem step_ok {s₀ s : State} (hp : PowersRepr s₀.mem (s₀.gpr .rdi))
    (hin : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hw : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) {j : Nat} (hj : j < 24) (I : Inv s₀ j s) :
    WP isa (.block (pair 0 ++ ([.alu .add .rdi (imm 32), .alu .cmp .rdi (.reg .rax)] : List Instr))) s
      fun s' => Inv s₀ (j+1) s' ∧ isa.eval .ne s' = some (decide (j + 1 ≠ 24)) := by
  rw [WP.block_append_iff]
  have hin' : InRegions s.wr (s.gpr .rdi) (1024 - 32 * j) := by
    rw [I.wr, I.rdi]; exact in_sub hin (by omega)
  have hw' : (s.gpr .rdi).toNat + (1024 - 32 * j) ≤ 2 ^ 64 := by
    rw [I.rdi, toNat_add_lt hw (by omega : 32 * j < 1024)]; omega
  refine WP.mono (pair_ok 0 s hin' hw' (by omega) I.m0 I.c8 I.c9) fun s₁ ⟨v, f, g, rd, wr, lanes⟩ => ?_
  rw [I.rdi] at v f
  have hdi : s₁.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * j) := by rw [g, I.rdi]
  have hax : s₁.gpr .rax = s₀.gpr .rdi + BitVec.ofNat 64 768 := by rw [g, I.rax]
  obtain ⟨s', run, hdi', hg', hm', hrd', hwr', hx', hy', he⟩ := next_run hj hdi hax
  refine WP.of_runBlock ⟨s', run, ⟨⟨hdi', by rw [hg' _ (by decide), hax],
    fun r h1 h2 => by rw [hg' r h1, g, I.gpr r h1 h2], by rw [hrd', rd, I.rd], by rw [hwr', wr, I.wr],
    ?_, ?_, ?_, ?_, ?_⟩, he⟩⟩
  · rw [hm']
    have f' : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * j), 32⟩] s.mem s₁.mem := by
      rw [Offset.add_add] at f
      rwa [show 32 * j + (256 + 32 * 0) = 256 + 32 * j by omega] at f
    exact (StitchZP.frame_sub (Nat.le_refl _) (by omega) I.frame).trans
      (StitchZP.frame_sub (by omega) (by omega) f')
  · intro k hk l hl
    rw [hm']
    have raw : blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 (272+32*j-16*l)) =
        hpow (ctxH s₀.mem (s₀.gpr .rdi)) (2*j+2-l) := by
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame I.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)),
        show 272+32*j-16*l = 256+16*(2*j+1-l) by omega, hp _ (by omega)]
      congr 1; omega
    by_cases hkj : k = j
    · subst k
      have e := v l hl
      rw [Offset.add_add, Offset.add_add] at e
      rw [show 256 + 32 * j + 16 * l = 32 * j + (256 + 32 * 0 + 16 * l) by omega, e,
        show 32 * j + (272 + 32 * 0 - 16 * l) = 272 + 32 * j - 16 * l by omega, raw]
    · have f' : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * j), 32⟩] s.mem s₁.mem := by
        rw [Offset.add_add] at f
        rwa [show 32 * j + (256 + 32 * 0) = 256 + 32 * j by omega] at f
      rw [StitchZP.keepAt f' (by omega) (by omega) (by omega)]
      exact I.pairs k (by omega) l hl
  · intro l hl
    rw [show s'.lane .xmm0 l = s₁.lane .xmm0 l by simp only [State.lane, hx', hy'],
      lanes _ (by decide) (by decide) (by decide) l hl]; exact I.m0 l hl
  · intro l hl
    rw [show s'.lane .xmm8 l = s₁.lane .xmm8 l by simp only [State.lane, hx', hy'],
      lanes _ (by decide) (by decide) (by decide) l hl]; exact I.c8 l hl
  · intro l hl
    rw [show s'.lane .xmm9 l = s₁.lane .xmm9 l by simp only [State.lane, hx', hy'],
      lanes _ (by decide) (by decide) (by decide) l hl]; exact I.c9 l hl

/-- The complete key-setup conversion writes only the power table. -/
theorem convert_ok (s₀ : State) (hin : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hw : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) (hp : PowersRepr s₀.mem (s₀.gpr .rdi)) :
    WP isa convert s₀ fun s =>
      PreparedPowersRepr s.mem (s₀.gpr .rdi) ∧
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [convert, convertSetup, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  have m0₅ : ∀ l < 2, s₅.lane .xmm0 l = revMask := fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl
  -- `rax` at the end of the table.
  obtain ⟨s₆, run₆, h6⟩ : ∃ s₆, runBlock isa (ptr .rax .rdi 768) s₅ = some s₆ ∧
      s₆.gpr .rax = s₀.gpr .rdi + BitVec.ofNat 64 768 ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧
      s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr ∧ s₆.xmm = s₅.xmm ∧ s₆.ymmHi = s₅.ymmHi := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, imm_eq (show 768 < 2 ^ 31 by decide), g₅ .rdi (by decide)]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals simp [mem_arithFlags, mem_setReg, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      xmm_arithFlags, xmm_setReg, ymmHi_arithFlags, ymmHi_setReg]
  obtain ⟨h6a, h6g, h6m, h6rd, h6wr, h6x, h6y⟩ := h6
  have lane6 : ∀ r l, s₆.lane r l = s₅.lane r l := fun r l => by simp only [State.lane, h6x, h6y]
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have I0 : Inv s₀ 0 s₆ := by
    refine ⟨by rw [h6g _ (by decide), g₅ _ (by decide)]; exact (BitVec.add_zero _).symm, h6a,
      fun r h1 h2 => by rw [h6g r h2, g₅ r h2], by rw [h6rd, rd₅], by rw [h6wr, wr₅],
      by rw [h6m, mm₅]; exact Frame.refl _ _, fun k hk => absurd hk (by omega),
      fun l hl => by rw [lane6]; exact m0₅ l hl, fun l hl => by rw [lane6]; exact c8 l hl,
      fun l hl => by rw [lane6]; exact c9 l hl⟩
  refine WP.mono (WP.loop (M := isa) (fun m s => ∃ j, j < 24 ∧ m = 24 - j ∧ Inv s₀ j s)
    (Q := Inv s₀ 24) (fun m s ⟨j, hj, hm, I⟩ => ?_) 24 s₆ ⟨0, by decide, rfl, I0⟩) fun s I => ?_
  · subst hm
    refine WP.mono (step_ok hp hin hw hj I) fun s' ⟨I', he⟩ => ?_
    rw [he]
    by_cases hl : j + 1 = 24
    · left; rw [hl] at I'; exact ⟨by simp [hl], I'⟩
    · right; exact ⟨by simp [hl], 24 - (j + 1), by omega, j + 1, by omega, rfl, I'⟩
  have hH : ctxH s.mem (s₀.gpr .rdi) = ctxH s₀.mem (s₀.gpr .rdi) :=
    VG.Proof.Aes.X86_64.AesNi.blockAt_frame I.frame fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have powers : PreparedPowersRepr s.mem (s₀.gpr .rdi) := by
    intro k hk
    rw [preparedPower_eq, preparedPower_eq, hH]
    refine ⟨?_, ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] using I.pairs k hk 0 (by decide)
    · have v := I.pairs k hk 1 (by decide)
      rw [show 256+32*k+16*1 = 272+32*k by omega,
        show 2*k+2-1 = 2*k+1 by omega] at v
      exact v
  exact ⟨powers, I.frame, fun r h1 h2 => I.gpr r h2 h1, I.rd, I.wr⟩

end VG.Proof.Gcm.X86_64.Prepared

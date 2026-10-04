import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops

/-!
# AES-GCM-SIV on x86-64: POLYVAL (`absorb`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up to
64 blocks to `W + 768` with the bytes of each reversed, so that GHASH reads
each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them; `absorb` absorbs the padded string so (`absorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off)

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .rdx (.mem (at_ .rsi 8)), .bswap .rax, .bswap .rdx,
    .store (at_ .rdi 0) .rdx, .store (at_ .rdi 8) .rax, .alu .add .rsi (imm 16), .alu .add .rdi (imm 16),
    .alu .sub .rcx (imm 1)]

theorem revStep_ok {t : State} {S P : Addr} {j : Nat} (hj : j < 2 ^ 63)
    (hsi : t.gpr .rsi = S) (hdi : t.gpr .rdi = P) (hcx : t.gpr .rcx = BitVec.ofNat 64 (j + 1))
    (hr₀ : InRegions (t.rd ++ t.wr) S 8) (hr₈ : InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 8) 8)
    (hw₀ : InRegions t.wr P 8) (hw₈ : InRegions t.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧
      t'.mem = (t.mem.writeW P (bswap64 (t.mem.readW (S + BitVec.ofNat 64 8) 64))).writeW (P + BitVec.ofNat 64 8)
        (bswap64 (t.mem.readW S 64)) ∧
      t'.gpr .rsi = S + BitVec.ofNat 64 16 ∧ t'.gpr .rdi = P + BitVec.ofNat 64 16 ∧
      t'.gpr .rcx = BitVec.ofNat 64 j ∧ t'.zf = some (decide (j = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t'.gpr r = t.gpr r) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by srun [hsi, hdi, hr₀, hr₈, hw₀, hw₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hsi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)]; rfl
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hcx,
      Proof.AesGcm.X86_64.sub_beq (show j + 1 < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by decide)]
    simp
  · intro r h₁ h₂ h₃ h₄ h₅; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
  all_goals rfl

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (W : Addr) (Q : Addr) (c j : Nat) (t₀ t : State) : Prop where
  rsi : t.gpr .rsi = Q + BitVec.ofNat 64 (16 * j)
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (768 + 16 * j)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (c - j)
  frame : Frame [⟨W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 768) j =
    (List.range j).map fun k => Spec.GcmSiv.ofBytes (bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * k)) 16)
  regs : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- `revLoop`: `c` blocks at `Q` copied to `W + 768`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {K W SP : Addr} (L : Lay K W SP) {t₀ : State} (E : Env K W SP t₀) {Q : Addr} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Buf K W SP t₀ Q (16 * c)) (h14 : t₀.gpr .r14 = BitVec.ofNat 64 c)
    (hsi : t₀.gpr .rsi = Q) (hdi : t₀.gpr .rdi = W + BitVec.ofNat 64 768) :
    WP isa revLoop t₀ fun t => Frame [⟨W + BitVec.ofNat 64 768, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (W + BitVec.ofNat 64 768) c =
        (List.range c).map (fun k => Spec.GcmSiv.ofBytes (bytesAt t₀.mem (Q + BitVec.ofNat 64 (16 * k)) 16)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = t₀.gpr r) ∧
      t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  obtain ⟨t₁, run₁, hcx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa [.mov .rcx (.reg .r14)] t₀ = some t₁ ∧
      t₁.gpr .rcx = BitVec.ofNat 64 c ∧ (∀ r, r ≠ .rcx → t₁.gpr r = t₀.gpr r) ∧ t₁.mem = t₀.mem ∧
      t₁.rd = t₀.rd ∧ t₁.wr = t₀.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, h14]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have I₀ : RInv W Q c 0 t₀ t₁ := ⟨by rw [hg₁ _ (by decide), hsi, Nat.mul_zero, BitVec.add_zero],
    by rw [hg₁ _ (by decide), hdi], by rw [hcx₁, Nat.sub_zero], by rw [hm₁]; exact Frame.refl _ _,
    by simp only [Spec.Gcm.blocksAt, List.range_zero, List.map_nil],
    fun r _ _ _ _ h => hg₁ r h, hrd₁, hwr₁⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv W Q c j t₀ t) ?_ (c - 0) t₁ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  have hw := L.ww
  have rq₀ := in_off (d := 16 * j) (n := 8) hQ.rd (by omega) hQ.lt
  have rq₈ := in_off (d := 16 * j + 8) (n := 8) hQ.rd (by omega) hQ.lt
  rw [← add_ofNat_assoc] at rq₈
  have ww₀ := E.perm.wW (d := 768 + 16 * j) (n := 8) (by omega)
  have ww₈ := E.perm.wW (d := 768 + 16 * j + 8) (n := 8) (by omega)
  rw [← add_ofNat_assoc] at ww₈
  rw [← I.rd, ← I.wr] at rq₀ rq₈
  rw [← I.wr] at ww₀ ww₈
  obtain ⟨t', run', hm', si', di', cx', zf', hg', hrd', hwr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega) I.rsi I.rdi (by rw [I.rcx]; congr 1; omega) rq₀ rq₈ ww₀ ww₈
  refine WP.of_runBlock ⟨t', run', ?_⟩
  -- The source is outside the copies.
  have src : ∀ d, d + 8 ≤ 16 * c → t.mem.readW (Q + BitVec.ofNat 64 d) 64 = t₀.mem.readW (Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => I.frame.readW (r := ⟨Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.w.sub_left (Offset.sub_base Q (by omega))).sub_right (Lay.wSub (by omega))) (by decide)
  have c₁ : (⟨W + BitVec.ofNat 64 768, 16 * c⟩ : Region).Contains (W + BitVec.ofNat 64 (768 + 16 * j)) (64 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  have c₂ : (⟨W + BitVec.ofNat 64 768, 16 * c⟩ : Region).Contains
      (W + BitVec.ofNat 64 (768 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) := by
    rw [add_ofNat_assoc]; exact Offset.contains W (by omega) (by omega) (by omega)
  have I' : RInv W Q c (j + 1) t₀ t' := by
    refine ⟨by rw [si', add_ofNat_assoc]; congr 2, by rw [di', add_ofNat_assoc]; congr 2, by rw [cx']; congr 1, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => by rw [hg' r h₁ h₂ h₃ h₄ h₅, I.regs r h₁ h₂ h₃ h₄ h₅],
      by rw [hrd', I.rd], by rw [hwr', I.wr]⟩
    · rw [hm']
      exact (I.frame.writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂
    · have fr : Frame [⟨W + BitVec.ofNat 64 (768 + 16 * j), 16⟩] t.mem t'.mem := by
        rw [hm']
        have cP0 : (⟨W + BitVec.ofNat 64 (768 + 16 * j), 16⟩ : Region).Contains (W + BitVec.ofNat 64 (768 + 16 * j))
            (64 / 8) := Offset.contains W (Nat.le_refl _) (by omega) (by omega)
        have cP8 : (⟨W + BitVec.ofNat 64 (768 + 16 * j), 16⟩ : Region).Contains
            (W + BitVec.ofNat 64 (768 + 16 * j) + BitVec.ofNat 64 8) (64 / 8) :=
          Offset.contains_base (W + BitVec.ofNat 64 (768 + 16 * j)) (show 8 + 8 ≤ 16 by decide) (by decide)
        exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ cP0).writeW (List.mem_singleton_self _) _ cP8
      have s₈ := src (16 * j + 8) (by omega)
      rw [← add_ofNat_assoc] at s₈
      rw [blocksAt_succ, Proof.AesGcm.X86_64.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)) (by omega), I.out, List.range_succ,
        List.map_append, List.map_cons, List.map_nil, add_ofNat_assoc, hm', blockAt_two, GcmSiv.ofBytes_bytesAt,
        src (16 * j) (by omega), s₈]
  by_cases he : j + 1 = c
  · left
    refine ⟨(eval_ne zf').trans (by simp [show c - j - 1 = 0 by omega]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, I'.regs, I'.rd, I'.wr⟩
  · right
    exact ⟨(eval_ne zf').trans (by simp [show c - j - 1 ≠ 0 by omega]), c - (j + 1), by omega, j + 1, rfl,
      by omega, I'⟩

end VG.Proof.AesGcmSiv.X86_64

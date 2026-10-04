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
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall GhPost gh_call ofNat_add_ofNat in_off toNat_ofNat_of_lt)

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

/-- What absorbing writes: GHASH's accumulator, the block at `W + 128`, the
reversed blocks, `vg_ghash`'s working space and the stack below `SP`. -/
abbrev absR (W SP : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 768, 1024⟩,
    ⟨W + BitVec.ofNat 64 1792, 256⟩, below SP 8]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What `absorbChunk` leaves, from `t`, after absorbing `k` of the `b`
blocks at `Q`. -/
structure ChunkPost (K W SP : Addr) (Q : Addr) (b k : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * k)
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - k)
  zf : t'.zf = some (decide (b - k = 0))
  frame : Frame (absR W SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80)) (elemsAt t.mem Q k)

theorem chunk_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : Buf K W SP t Q (16 * b))
    (h12 : t.gpr .r12 = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (absorbChunk v.callees) t (ChunkPost K W SP Q b (min b 64) t) := by
  have hbl : b < 2 ^ 60 := by have := hQ.lt; omega
  have h15 := E.r15
  -- `r14 := min b 64`.
  obtain ⟨t₁, run₁, h14₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State,
      runBlock isa [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)] t = some t₁ ∧
      t₁.gpr .r14 = BitVec.ofNat 64 64 ∧ t₁.cf = some (decide (b < 64)) ∧
      (∀ r, r ≠ .r14 → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true]
    · simp only [cf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx,
        toNat_ofNat_of_lt (show b < 2 ^ 64 by omega)]
      rfl
    · intro r hr; simp only [gpr_arithFlags, gpr_setReg, hr, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have hite : WP isa (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block [])) t₁ fun t₂ =>
      t₂.gpr .r14 = BitVec.ofNat 64 (min b 64) ∧ (∀ r, r ≠ .r14 → t₂.gpr r = t.gpr r) ∧ t₂.mem = t.mem ∧
      t₂.rd = t.rd ∧ t₂.wr = t.wr := by
    refine WP.ite (decide (b < 64)) (eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
    · refine WP.of_runBlock ⟨_, by srun [], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, hg₁ _ (by decide : Reg.rbx ≠ .r14), hbx]
        simp at ht; rw [Nat.min_eq_left (by omega)]
      · simp only [gpr_setReg, hr, ite_false]; exact hg₁ r hr
      · exact hm₁
      · exact hrd₁
      · exact hwr₁
    · refine WP.block_nil ⟨?_, hg₁, hm₁, hrd₁, hwr₁⟩
      simp at hf; rw [h14₁, Nat.min_eq_right (by omega)]
  refine WP.seq (WP.mono hite fun t₂ ⟨h14₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  -- The source and the destination of the copies.
  have h15₂ : t₂.gpr .r15 = W := by rw [hg₂ _ (by decide), h15]
  obtain ⟨t₃, run₃, hsi₃, hdi₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State,
      runBlock isa ([.mov .rsi (.reg .r12)] ++ ptr .rdi .r15 revO) t₂ = some t₃ ∧
      t₃.gpr .rsi = Q ∧ t₃.gpr .rdi = W + BitVec.ofNat 64 768 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hg₂ _ (by decide : Reg.r12 ≠ .r14), h12]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r h₁ h₂; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have kE₃ : ∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [hg₃ _ (by decide) (by decide), hg₂ _ (by decide)]
  have E₃ : Env K W SP t₃ := E.keep kE₃ (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])
  have hQ₃ : Buf K W SP t₃ Q (16 * min b 64) :=
    (hQ.take (by omega)).of_eq (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂])
  have h14₃ : t₃.gpr .r14 = BitVec.ofNat 64 (min b 64) := by rw [hg₃ _ (by decide) (by decide), h14₂]
  refine WP.seq (WP.mono (revLoop_ok L E₃ (by omega) (by omega) hQ₃ h14₃ hsi₃ hdi₃)
    fun t₄ ⟨fr₄, out₄, hg₄, hrd₄, hwr₄⟩ => ?_)
  have h15₄ : t₄.gpr .r15 = W := by rw [hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₃.r15]
  have h14₄ : t₄.gpr .r14 = BitVec.ofNat 64 (min b 64) := by
    rw [hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h14₃]
  -- `vg_ghash`'s arguments.
  obtain ⟨t₅, run₅, rdi₅, rsi₅, r8₅, rdx₅, rcx₅, hg₅, hm₅, hrd₅, hwr₅⟩ : ∃ t₅ : State,
      runBlock isa (ghArgs ++ ptr .rdx .r15 revO ++ [.mov .rcx (.reg .r14)]) t₄ = some t₅ ∧
      t₅.gpr .rdi = W + BitVec.ofNat 64 64 ∧ t₅.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₅.gpr .r8 = W + BitVec.ofNat 64 1792 ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 768 ∧
      t₅.gpr .rcx = BitVec.ofNat 64 (min b 64) ∧ (∀ r ∈ calleeSaved, t₅.gpr r = t₄.gpr r) ∧
      t₅.mem = t₄.mem ∧ t₅.rd = t₄.rd ∧ t₅.wr = t₄.wr := by
    refine ⟨_, by srun [ghArgs], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h14₄]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₅ : Env K W SP t₅ := E₃.of_saved (fun r hr => by
      rw [hg₅ r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hrd₅, hrd₄]) (by rw [hwr₅, hwr₄])
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, WP.seq ?_⟩)
  refine WP.mono (gh_call v.gh (gargs L E₅ (d := 768) (n := min b 64) (by decide) (by omega) rdi₅ rsi₅ rdx₅ rcx₅ r8₅))
    fun t₆ P => ?_
  have h12₆ : t₆.gpr .r12 = Q := by
    rw [P.saved _ (by decide), hg₅ _ (by decide), hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hg₃ _ (by decide) (by decide), hg₂ _ (by decide), h12]
  have hbx₆ : t₆.gpr .rbx = BitVec.ofNat 64 b := by
    rw [P.saved _ (by decide), hg₅ _ (by decide), hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hg₃ _ (by decide) (by decide), hg₂ _ (by decide), hbx]
  have h14₆ : t₆.gpr .r14 = BitVec.ofNat 64 (min b 64) := by rw [P.saved _ (by decide), hg₅ _ (by decide), h14₄]
  have E₆ : Env K W SP t₆ := E₅.of_saved P.saved P.rd P.wr
  have hm₃' : t₃.mem = t.mem := hm₃.trans hm₂
  have dH : ∀ r ∈ [(⟨W + BitVec.ofNat 64 768, 16 * min b 64⟩ : Region)], (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have dY : ∀ r ∈ [(⟨W + BitVec.ofNat 64 768, 16 * min b 64⟩ : Region)], (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by decide) (by omega)
  have fr₆ := P.frame
  rw [E₅.rsp] at fr₆
  have out₆ := P.out
  rw [hm₅, Proof.AesGcm.X86_64.blockAt_frame fr₄ dH, Proof.AesGcm.X86_64.blockAt_frame fr₄ dY, out₄, hm₃'] at out₆
  refine WP.of_runBlock ⟨_, by srun [], ?_⟩
  refine ⟨E₆.keep (fun r hr => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [rd_arithFlags, rd_setReg]; rw [P.rd, hrd₅, hrd₄, hrd₃, hrd₂]
  · simp only [wr_arithFlags, wr_setReg]; rw [P.wr, hwr₅, hwr₄, hwr₃, hwr₂]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rw [P.saved _ (by decide), hg₅ _ (by decide), hg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hg₃ _ (by decide) (by decide), hg₂ _ (by decide)]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h12₆, h14₆,
      Proof.AesGcm.X86_64.times16_val]
  · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx₆, h14₆]
    exact Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)
  · simp only [zf_setReg, zf_arithFlags, gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hbx₆, h14₆,
      Proof.AesGcm.X86_64.sub_beq (show b < 2 ^ 64 by omega) (show min b 64 < 2 ^ 64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · simp only [mem_arithFlags, mem_setReg]
    rw [← hm₃']
    refine ((fr₄.sub fun r hr => ?_).trans (hm₅ ▸ Frame.refl _ _)).trans (fr₆.mono fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 768, 1024⟩, by simp, Region.sub_prefix (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  · simp only [mem_arithFlags, mem_setReg]; rw [out₆]

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

/-- A buffer misses what absorbing writes. -/
theorem buf_absR {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : Buf K W SP s Q k) :
    ∀ r ∈ absR W SP, (⟨Q, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.w.sub_right (Lay.wSub (by decide))
  · exact h.stk.symm

/-- So do the other parts of `W`. -/
theorem w_absR {K W SP : Addr} (L : Lay K W SP) {d k : Nat}
    (hd : d + k ≤ 80 ∨ 96 ≤ d ∧ d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 768) :
    ∀ r ∈ absR W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rcases hd with hd | hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

theorem elemsAt_frame {K W SP : Addr} {s : State} {m m' : Mem} (hf : Frame (absR W SP) m m') {Q : Addr} {k : Nat}
    (h : Buf K W SP s Q (16 * k)) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt,
    Proof.AesGcm.X86_64.bytesAt_frame hf (buf_absR h) (by have := h.lt; omega)]

/-- What absorbing leaves, from `t`, having absorbed the elements `xs`. -/
structure AbsPost (K W SP : Addr) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (absR W SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80)) xs

theorem chunks_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t)
    {Q : Addr} {b : Nat} (hb : 1 ≤ b) (hQ : Buf K W SP t Q (16 * b))
    (h12 : t.gpr .r12 = Q) (hbx : t.gpr .rbx = BitVec.ofNat 64 b) :
    WP isa (.loop (absorbChunk v.callees) .ne) t fun t' => AbsPost K W SP (elemsAt t.mem Q b) t t' ∧
      t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * b) ∧ t'.gpr .rbp = t.gpr .rbp := by
  refine WP.loop (M := isa) (body := absorbChunk v.callees) (c := .ne)
    (fun (m : Nat) (t' : State) => ∃ d, m = b - d ∧ d < b ∧ AbsPost K W SP (elemsAt t.mem Q d) t t' ∧
      t'.gpr .r12 = Q + BitVec.ofNat 64 (16 * d) ∧ t'.gpr .rbx = BitVec.ofNat 64 (b - d) ∧
      t'.gpr .rbp = t.gpr .rbp) ?_ (b - 0) t
    ⟨0, rfl, hb, ⟨E, rfl, rfl, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h12, Nat.mul_zero, BitVec.add_zero], by rw [hbx, Nat.sub_zero], rfl⟩
  rintro m t' ⟨d, rfl, hd, P, h12', hbx', hbp'⟩
  have hQ' : Buf K W SP t' (Q + BitVec.ofNat 64 (16 * d)) (16 * (b - d)) :=
    (hQ.slice (by omega)).of_eq P.rd P.wr
  refine WP.mono (chunk_ok v L P.env (by omega) hQ' h12' hbx') fun t'' C => ?_
  have hk : 1 ≤ min (b - d) 64 := by omega
  have P' : AbsPost K W SP (elemsAt t.mem Q (d + min (b - d) 64)) t t'' := by
    refine ⟨C.env, C.rd.trans P.rd, C.wr.trans P.wr, P.frame.trans C.frame, ?_⟩
    rw [C.out, P.out, Proof.AesGcm.X86_64.blockAt_frame P.frame (w_absR L (.inl (by decide))),
      elemsAt_frame P.frame ((hQ.slice (k := 16 * min (b - d) 64) (by omega))), elemsAt_add,
      Proof.Gcm.ghashFrom_append]
  have r12'' : t''.gpr .r12 = Q + BitVec.ofNat 64 (16 * (d + min (b - d) 64)) := by
    rw [C.r12, add_ofNat_assoc, Nat.mul_add]
  have rbp'' : t''.gpr .rbp = t.gpr .rbp := C.rbp.trans hbp'
  by_cases he : b - d - min (b - d) 64 = 0
  · left
    have hdb : d + min (b - d) 64 = b := by omega
    refine ⟨(eval_ne C.zf).trans (by simp [he]), hdb ▸ P', hdb ▸ r12'', rbp''⟩
  · right
    refine ⟨(eval_ne C.zf).trans (by simp [he]), b - (d + min (b - d) 64), by omega, d + min (b - d) 64, rfl,
      by omega, P', r12'', by rw [C.rbx]; congr 1; omega, rbp''⟩

end VG.Proof.AesGcmSiv.X86_64

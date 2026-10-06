import VerifiedGarbage.Proof.AesGcm.X86_64.Init
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init_precomputed`

Untrusted: everything here is checked by Lean. `init`'s code (`initWith_wp`),
then the hash subkey `H` copied to `ctx + 256` (`powStart_ok`), which is
`H¹` (`hpow_one`), and `H²`–`H⁴⁸` after it, each `vg_ghash` from a zero
block over the one before it: `(0 ⊕ Hᵏ) • H = Hᵏ⁺¹` (`powStep_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt hpow mul ghashFrom)

/-- A fold whose steps keep the first component, keeps it. -/
theorem foldl_fst_keep {β : Type} (F : β × β → Nat → β × β) (P : Nat → Prop)
    (hF : ∀ zv i, P i → (F zv i).1 = zv.1) : ∀ (l : List Nat) (zv : β × β), (∀ i ∈ l, P i) → (l.foldl F zv).1 = zv.1
  | [], _, _ => rfl
  | i :: l, zv, h => by
    rw [List.foldl_cons, foldl_fst_keep F P hF l _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      hF zv i (h i (List.mem_cons_self ..))]

/-- `1 • y = y`: only the first bit of `1` is set, so the product is `y`. -/
theorem mul_one_left (y : Block) : mul Spec.Gcm.one y = y := by
  unfold mul
  rw [List.range_succ_eq_map, List.foldl_cons,
    foldl_fst_keep _ (fun i => Spec.Gcm.one.getMsbD i = false) (fun zv i h => by simp only [h]; rfl) _ _
      fun i hi => ?_]
  · have h0 : Spec.Gcm.one.getMsbD 0 = true := by decide
    simp only [h0, ↓reduceIte]
    exact BitVec.zero_xor
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have : ∀ j < 127, Spec.Gcm.one.getMsbD (j + 1) = false := by decide
    exact this j (List.mem_range.mp hj)

theorem hpow_one (h : Block) : hpow h 1 = h := mul_one_left h

/-- The regions of `vg_aes_gcm_init_precomputed`: the key context of 1024
bytes at `Ctx`, the working space at `W`, the return address at `SP` and the
stack below it. -/
structure IPLay (Ctx W SP : Addr) : Prop where
  cw : Ctx.toNat + 1024 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨W, 2560⟩
  kc : (below SP 8).Disjoint ⟨Ctx, 1024⟩
  ks : (below SP 8).Disjoint ⟨W, 2560⟩
  rc : (⟨SP, 8⟩ : Region).Disjoint ⟨Ctx, 1024⟩
  rs : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩

theorem IPLay.of {s : State} (hp : Proof.AesGcm.initPreL 1024 s) :
    IPLay (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsp) ∧ Covers [⟨s.gpr .rdx, 1024⟩] s.wr ∧
      Covers [⟨s.gpr .rcx, 2560⟩] s.wr := by
  simp only [Proof.AesGcm.initPreL, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨-, hwr, -, -, d_cs, r_c, r_s, -, k_c, k_s, wc, ws, -⟩ := hp
  exact ⟨⟨wc, ws, d_cs, k_c, k_s, r_c, r_s⟩, by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- What the powers leave, after `j` of them from `m₅`: `Hᵏ⁺¹` at
`Ctx + 256 + 16 k` for `k ≤ j`, and `rbp` past them. -/
structure PowInv (Ctx W SP : Addr) (rd wr : List Region) (m₅ : Mem) (j : Nat) (t : State) : Prop where
  r13 : t.gpr .r13 = Ctx
  r15 : t.gpr .r15 = W
  rbp : t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j)
  rsp : t.gpr .rsp = SP
  rd : t.rd = rd
  wr : t.wr = wr
  frame : Frame [⟨Ctx + BitVec.ofNat 64 256, 768⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] m₅ t.mem
  pows : ∀ k ≤ j, blockAt t.mem (Ctx + BitVec.ofNat 64 (256 + 16 * k)) =
    hpow (blockAt m₅ (Ctx + BitVec.ofNat 64 240)) (k + 1)

section
variable {Ctx W SP : Addr} (L : IPLay Ctx W SP)
include L

/-- `H` copied to `Ctx + 256`, and `rbp` past it. -/
theorem powStart_ok {t : State} (pC : Covers [⟨Ctx, 1024⟩] t.wr) (h13 : t.gpr .r13 = Ctx)
    (h15 : t.gpr .r15 = W) (hsp : t.gpr .rsp = SP) :
    WP isa (.block (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
      .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272)) t
      (PowInv Ctx W SP t.rd t.wr t.mem 0) := by
  have r₁ := in_left (rd := t.rd) (in_off pC (show 240 + 8 ≤ 1024 by decide) (by decide))
  have r₂ := in_left (rd := t.rd) (in_off pC (show 248 + 8 ≤ 1024 by decide) (by decide))
  have w₁ := in_off pC (show 256 + 8 ≤ 1024 by decide) (by decide)
  have w₂ := in_off pC (show 264 + 8 ≤ 1024 by decide) (by decide)
  have sep : Mem.Sep (Ctx + BitVec.ofNat 64 248) (64 / 8) (Ctx + BitVec.ofNat 64 256) (64 / 8) :=
    Offset.sep _ (.inl (by decide)) (by have := L.cw; omega) (by have := L.cw; omega)
  obtain ⟨t', run, hm, h13', h15', hbp, hsp', hrd, hwr⟩ : ∃ t', runBlock isa
      (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
        .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272) t = some t' ∧
      t'.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 256) (t.mem.readW (Ctx + BitVec.ofNat 64 240) 64)).writeW
        (Ctx + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (t.mem.readW (Ctx + BitVec.ofNat 64 248) 64) ∧
      t'.gpr .r13 = Ctx ∧ t'.gpr .r15 = W ∧ t'.gpr .rbp = Ctx + BitVec.ofNat 64 272 ∧ t'.gpr .rsp = SP ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
    rw [add_ofNat_assoc]
    refine ⟨_, by xrun [h13, r₁, r₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags, Mem.readW_writeW_sep sep (by decide)]
    · simp [gpr_setReg, gpr_arithFlags, h13]
    · simp [gpr_setReg, gpr_arithFlags, h15]
    · simp [gpr_setReg, gpr_arithFlags, h13, imm_eq]
    · simp [gpr_setReg, gpr_arithFlags, hsp]
    all_goals simp [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨t', run, h13', h15', by rw [hbp], hsp', hrd, hwr, ?_, fun k hk => ?_⟩
  · rw [hm]
    exact (Cmac.frame_store2 _ _ _).sub fun r hr => ⟨_, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  · have hk0 : k = 0 := by omega
    subst hk0
    show blockAt t'.mem (Ctx + BitVec.ofNat 64 256) = hpow _ 1
    have e : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
      (add_ofNat_assoc Ctx 240 8).symm
    rw [hpow_one, blockAt, blockAt, hm, Cmac.bytesAt_store2, Cmac.le8_readW, Cmac.le8_readW, e,
      ← Cmac.bytesAt_split]
end


section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : IPLay Ctx W SP)
include L

/-- The blocks in the key context from byte 256 stay where they are, outside
the working space and the stack. -/
theorem ctx_frame {m m' : Mem} (hf : Frame [⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] m m') {d : Nat}
    (hd : d + 16 ≤ 1024) : blockAt m' (Ctx + BitVec.ofNat 64 d) = blockAt m (Ctx + BitVec.ofNat 64 d) :=
  blockAt_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (L.cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by decide))
    · exact (L.kc.sub_right (Offset.sub_base _ hd)).symm

/-- The arguments of the call of `vg_ghash` for the next power, after `j`. -/
theorem powArgs_ok {j : Nat} (hj : j < 47) {t : State} (h13 : t.gpr .r13 = Ctx) (h15 : t.gpr .r15 = W)
    (hbp : t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j)) (hsp : t.gpr .rsp = SP)
    (pC' : Covers [⟨Ctx, 1024⟩] t.wr) (pW' : Covers [⟨W, 2560⟩] t.wr) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .rbp 0) .rax, .store (at_ .rbp 8) .rax] : List Instr) ++
        ptr .rdi .r13 240 ++ ([.mov .rsi (.reg .rbp), .mov .rdx (.reg .rbp), .alu .sub .rdx (imm 16),
        .mov32 .rcx (imm 1)] : List Instr) ++ ptr .r8 .r15 scrO)) t fun t₁ =>
      GhCall t₁ (Ctx + BitVec.ofNat 64 240) (Ctx + BitVec.ofNat 64 (272 + 16 * j))
        (Ctx + BitVec.ofNat 64 (256 + 16 * j)) (W + BitVec.ofNat 64 512) 1 ∧
      t₁.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 (272 + 16 * j)) (0 : BitVec 64)).writeW
        (Ctx + BitVec.ofNat 64 (272 + 16 * j) + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have cw := L.cw
  generalize hY : Ctx + BitVec.ofNat 64 (272 + 16 * j) = Y at hbp ⊢
  have w₁ : InRegions t.wr (Y + BitVec.ofNat 64 0) 8 := by
    rw [← hY, add_ofNat_assoc]; exact in_off pC' (by omega) (by decide)
  have w₂ : InRegions t.wr (Y + BitVec.ofNat 64 8) 8 := by
    rw [← hY, add_ofNat_assoc]; exact in_off pC' (by omega) (by decide)
  have eD : Y - BitVec.ofNat 64 16 = Ctx + BitVec.ofNat 64 (256 + 16 * j) := by
    rw [← hY, Offset.add_ofNat_sub _ (by omega)]; congr 2; omega
  obtain ⟨t₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hcs, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      (([.mov32 .rax (imm 0), .store (at_ .rbp 0) .rax, .store (at_ .rbp 8) .rax] : List Instr) ++
        ptr .rdi .r13 240 ++ ([.mov .rsi (.reg .rbp), .mov .rdx (.reg .rbp), .alu .sub .rdx (imm 16),
        .mov32 .rcx (imm 1)] : List Instr) ++ ptr .r8 .r15 scrO) t = some t₁ ∧
      t₁.mem = (t.mem.writeW Y (0 : BitVec 64)).writeW (Y + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      t₁.gpr .rdi = Ctx + BitVec.ofNat 64 240 ∧ t₁.gpr .rsi = Y ∧
      t₁.gpr .rdx = Ctx + BitVec.ofNat 64 (256 + 16 * j) ∧ t₁.gpr .rcx = BitVec.ofNat 64 1 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 512 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by xrun [hbp, h13, h15, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, h13, imm_eq]
    · simp [gpr_setReg, gpr_arithFlags, hbp]
    · simp [gpr_setReg, gpr_arithFlags, hbp, imm_eq, eD]
    · simp [gpr_setReg, gpr_arithFlags]
    · simp [gpr_setReg, gpr_arithFlags, h15, imm_eq, scrO]
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
    all_goals simp [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨t₁, run₁, ?_, hm₁, hcs, hrd₁, hwr₁⟩
  have hsp₁ : t₁.gpr .rsp = SP := by rw [hcs .rsp (by decide), hsp]
  have pC₁ : Covers [⟨Ctx, 1024⟩] t₁.wr := by rw [hwr₁]; exact pC'
  have pW₁ : Covers [⟨W, 2560⟩] t₁.wr := by rw [hwr₁]; exact pW'
  have sY : Region.Sub ⟨Y, 16⟩ ⟨Ctx, 1024⟩ := by rw [← hY]; exact Offset.sub_base _ (by omega)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 512, 256⟩ ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have dY : ∀ {d : Nat}, d + 16 ≤ 272 + 16 * j → (⟨Ctx + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨Y, 16⟩ :=
    fun hd => by rw [← hY]; exact Offset.disjoint _ (.inl hd) (by omega) (by omega)
  have cY : Covers [⟨Y, 16⟩] t₁.wr := by rw [← hY]; exact covers_off pC₁ (by omega) (by decide)
  · refine ⟨hdi, hsi, hdx, hcx, hr8, by decide, dY (by omega),
      (L.cs.sub_left (Offset.sub_base _ (by decide))).sub_right sS, (dY (by omega)).symm,
      (L.cs.sub_left sY).sub_right sS, (L.cs.sub_left (Offset.sub_base _ (by omega))).sub_right sS,
      by rw [hsp₁]; exact L.kc.sub_right (Offset.sub_base _ (by decide)), by rw [hsp₁]; exact L.kc.sub_right sY,
      by rw [hsp₁]; exact L.kc.sub_right (Offset.sub_base _ (by omega)), by rw [hsp₁]; exact L.ks.sub_right sS, ?_, ?_⟩
    · exact covers_cons (covers_left (covers_off pC₁ (by decide) (by decide))) (covers_cons
        (covers_left (covers_off pC₁ (n := 16 * 1) (by omega) (by decide))) (covers_cons (covers_left cY)
        (covers_left (covers_off pW₁ (by decide) (by decide)))))
    · exact covers_cons cY (covers_off pW₁ (by decide) (by decide))

/-- One more power. -/
theorem powStep_ok {rd wr : List Region} (pC : Covers [⟨Ctx, 1024⟩] wr) (pW : Covers [⟨W, 2560⟩] wr)
    {m₅ : Mem} {j : Nat} (hj : j < 47) {t : State} (h : PowInv Ctx W SP rd wr m₅ j t) :
    WP isa (powStep v.callees) t (PowInv Ctx W SP rd wr m₅ (j + 1)) := by
  have cw := L.cw
  have pC' : Covers [⟨Ctx, 1024⟩] t.wr := by rw [h.wr]; exact pC
  have pW' : Covers [⟨W, 2560⟩] t.wr := by rw [h.wr]; exact pW
  refine WP.seq (WP.mono (powArgs_ok L hj h.r13 h.r15 h.rbp h.rsp pC' pW') fun t₁ ⟨gc, hm₁, hcs, hrd₁, hwr₁⟩ => ?_)
  have hbp := h.rbp
  generalize hY : Ctx + BitVec.ofNat 64 (272 + 16 * j) = Y at gc hm₁ hbp
  have hsp₁ : t₁.gpr .rsp = SP := by rw [hcs .rsp (by decide), h.rsp]
  have sY' : Region.Sub ⟨Y, 16⟩ ⟨Ctx + BitVec.ofNat 64 256, 768⟩ := by rw [← hY]; exact Offset.sub _ (by omega) (by omega)
  have sS : Region.Sub ⟨W + BitVec.ofNat 64 512, 256⟩ ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have dY : ∀ {d : Nat}, d + 16 ≤ 272 + 16 * j → (⟨Ctx + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨Y, 16⟩ :=
    fun hd => by rw [← hY]; exact Offset.disjoint _ (.inl hd) (by omega) (by omega)
  refine WP.seq (WP.mono (gh_call v.gh gc) fun t₂ g => ?_)
  have hbp₂ : t₂.gpr .rbp = Y := by rw [g.saved .rbp (by decide), hcs .rbp (by decide), hbp]
  obtain ⟨t₃, run₃, hbp₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa [.alu .add .rbp (imm 16)] t₂ = some t₃ ∧
      t₃.gpr .rbp = Y + BitVec.ofNat 64 16 ∧ (∀ r, r ≠ .rbp → t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, hbp₂, imm_eq]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals simp [mem_arithFlags, mem_setReg, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  have keep : ∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [hg₃ _ (by decide), g.saved _ (by decide), hcs _ (by decide)]
  have f₁ : Frame [⟨Y, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Cmac.frame_store2 _ _ _
  have f₂ : Frame [⟨Y, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] t₁.mem t₂.mem := by
    have := g.frame; rw [hsp₁] at this; exact this
  have hH₁ : blockAt t₁.mem (Ctx + BitVec.ofNat 64 240) = blockAt m₅ (Ctx + BitVec.ofNat 64 240) := by
    rw [blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dY (by omega)]
    exact blockAt_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
      · exact (L.cs.sub_left (Offset.sub_base _ (by decide))).sub_right sS
      · exact (L.kc.sub_right (Offset.sub_base _ (by decide))).symm
  have hY₁ : blockAt t₁.mem Y = 0 := by rw [blockAt, hm₁, zeroT_bytes]; decide
  have hD₁ : blockAt t₁.mem (Ctx + BitVec.ofNat 64 (256 + 16 * j)) =
      hpow (blockAt m₅ (Ctx + BitVec.ofNat 64 240)) (j + 1) := by
    rw [blockAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dY (by omega)]
    exact h.pows j (Nat.le_refl _)
  have out := g.out
  rw [hH₁, hY₁, blocksAt_one, hD₁] at out
  refine ⟨by rw [keep .r13 (by simp), h.r13], by rw [keep .r15 (by simp), h.r15], ?_,
    by rw [keep .rsp (by simp), h.rsp], by rw [hrd₃, g.rd, hrd₁, h.rd], by rw [hwr₃, g.wr, hwr₁, h.wr], ?_,
    fun k hk => ?_⟩
  · rw [hbp₃, ← hY, add_ofNat_assoc]; congr 2
  · rw [hm₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sY'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., sY'⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · rw [hm₃]
    rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
    · rw [blockAt_frame f₂ (fun r hr => ?_), blockAt_frame f₁ (fun r hr => ?_)]
      · exact h.pows k (by omega)
      · simp only [List.mem_singleton] at hr; subst hr; exact dY (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dY (by omega)
        · exact (L.cs.sub_left (Offset.sub_base _ (by omega))).sub_right sS
        · exact (L.kc.sub_right (Offset.sub_base _ (by omega))).symm
    · have hk1 : k = j + 1 := by omega
      subst hk1
      have e : Ctx + BitVec.ofNat 64 (256 + 16 * (j + 1)) = Y := by rw [← hY]; congr 2; omega
      rw [e, out]
      exact congrArg (mul · _) BitVec.zero_xor


/-- `n` more powers. -/
theorem powSteps_ok {rd wr : List Region} (pC : Covers [⟨Ctx, 1024⟩] wr) (pW : Covers [⟨W, 2560⟩] wr)
    {m₅ : Mem} : ∀ (n : Nat), n ≤ 47 → ∀ {t : State}, PowInv Ctx W SP rd wr m₅ 0 t →
      WP isa (powSteps v.callees n) t (PowInv Ctx W SP rd wr m₅ n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, _, h => WP.seq (WP.mono (powSteps_ok pC pW n (by omega) h) fun _ h' =>
      powStep_ok v L pC pW (by omega) h')

end

/-- What the key context holds, outside a frame that leaves its first 256 bytes. -/
theorem keyRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {key : List Byte}
    (hl : key.length = 16 ∨ key.length = 24 ∨ key.length = 32) (hd : ∀ r ∈ rs, (⟨p, 256⟩ : Region).Disjoint r)
    (h : Spec.Gcm.KeyRepr m p key) : Spec.Gcm.KeyRepr m' p key := by
  have hR : 16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
    rcases hl with h | h | h <;> rw [h] <;> decide
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega)]
    exact h.1
  · have e : blockAt m' (p + BitVec.ofNat 64 240) = blockAt m (p + BitVec.ofNat 64 240) :=
      blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))
    exact e.trans h.2

/-- `vg_aes_gcm_init_precomputed`. -/
theorem initP_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.initPrecomputedX86_64.pre s) :
    WP isa (initPrecomputed v.callees) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.initPrecomputedX86_64.post s s' := by
  obtain ⟨L, pC, pW⟩ := IPLay.of hp
  have hl : (s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32 :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2
  refine initWith_wp v (by decide) hp fun s₅ D => ?_
  have pC₅ : Covers [⟨s.gpr .rdx, 1024⟩] s₅.wr := by rw [D.wr]; exact pC
  have pW₅ : Covers [⟨s.gpr .rcx, 2560⟩] s₅.wr := by rw [D.wr]; exact pW
  refine WP.seq (WP.mono (powStart_ok L pC₅ D.r13 D.r15 D.rsp) fun t I => ?_)
  refine WP.seq (WP.mono (powSteps_ok v L pC₅ pW₅ 47 (Nat.le_refl _) I) fun t' I' => ?_)
  have dS : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region), ⟨s.gpr .rcx + BitVec.ofNat 64 512, 256⟩,
      below (s.gpr .rsp) 8], (savedR (s.gpr .rcx)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ((L.cs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact (L.ks.sub_right (Offset.sub_base _ (by decide))).symm
  have hret : t'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    rw [ret_kept I'.frame (fun r hr => ?_), D.ret]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.rc.sub_right (Offset.sub_base _ (by decide))
    · exact L.rs.sub_right (Offset.sub_base _ (by decide))
    · exact ret_below _
  refine WP.mono (exit_ok I'.r15 I'.rsp (covers_left (by rw [I'.wr]; exact pW₅)) (D.saved.frame I'.frame dS) hret)
    fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.initPrecomputedX86_64]
  rw [hm]
  have dC : ∀ {d : Nat}, d + 16 ≤ 256 → ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region),
      ⟨s.gpr .rcx + BitVec.ofNat 64 512, 256⟩, below (s.gpr .rsp) 8],
      (⟨s.gpr .rdx + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inl hd) (by omega) (by decide)
    · exact (L.cs.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
    · exact (L.kc.sub_right (Offset.sub_base _ (by omega))).symm
  have hH : Spec.Gcm.ctxH t'.mem (s.gpr .rdx) = blockAt s₅.mem (s.gpr .rdx + BitVec.ofNat 64 240) :=
    blockAt_frame I'.frame (dC (by decide))
  refine ⟨keyRepr_frame I'.frame (by rw [length_bytesAt]; exact hl) (fun r hr => ?_) D.key,
    fun k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by have := L.cw; omega)
    · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact (L.kc.sub_right (Region.sub_prefix (by decide))).symm
  · rw [hH]; exact I'.pows k (by omega)

end VG.Proof.AesGcm.X86_64

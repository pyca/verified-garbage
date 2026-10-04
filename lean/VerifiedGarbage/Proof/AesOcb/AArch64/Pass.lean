import VerifiedGarbage.Proof.AesOcb.AArch64.Hash

/-!
# AES-OCB on AArch64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xor16_ok`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off eval_nonzero toNat_ofNat_of_lt)

/-- The registers a body writes. -/
abbrev bodyRegs : List Reg := [.x9, .x10, .x11, .x12]

/-- What a body does to the block at `B` (in `x23`) and the checksum, with
the offset at `W + ofsO`. -/
def BodyOk (W : Addr) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (B : Addr), t.gpr .x23 = B → t.gpr .x19 = W →
    InRegions (t.rd ++ t.wr) B 8 → InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8 →
    InRegions t.wr B 8 → InRegions t.wr (B + BitVec.ofNat 64 8) 8 →
    InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 16) 8 → InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 24) 8 →
    InRegions t.wr (W + BitVec.ofNat 64 32) 8 → InRegions t.wr (W + BitVec.ofNat 64 40) 8 →
    (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩ →
    ∃ t', runBlock isa body t = some t' ∧
      blockAtMem t'.mem B = fB (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem B) (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨B, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      (∀ r, r ∉ bodyRegs → t'.gpr r = t.gpr r) ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

theorem xorOfs_ok {W : Addr} : BodyOk W xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ _ _ hBW
  refine ⟨_, by orun [xorOfs, h23, h19, rB₀, rB₈, wB₀, wB₈, rO₀, rO₈], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩ <;>
    try simp only [mem_write, sp_write, rd_write, wr_write]
  · rw [blockAtMem_store2, show W + 24#64 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_xor_words]; rfl
  · rw [blockAtMem_frame (Proof.Cmac.frame_store2 _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hBW.sub_right (Lay.wSub (W := W) (d := 32) (n := 16) (by decide))).symm]
  · exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  · simp only [bodyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- `addCk`: the checksum XORed with the block at `B`. -/
theorem addCk_ok {W B : Addr} {t : State} (h23 : t.gpr .x23 = B) (h19 : t.gpr .x19 = W)
    (rB₀ : InRegions (t.rd ++ t.wr) B 8) (rB₈ : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 8) 8)
    (wC₀ : InRegions t.wr (W + BitVec.ofNat 64 32) 8) (wC₈ : InRegions t.wr (W + BitVec.ofNat 64 40) 8) :
    ∃ t', runBlock isa addCk t = some t' ∧
      BlkStep W ckO (blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ blockAtMem t.mem B) bodyRegs t t' := by
  obtain ⟨t', run, Bk⟩ := xor16_ok (s := t) (b := .x23) (a := 0) (d := ckO) (by decide) (by decide) h19 h23
    (by decide) (by decide) (by decide) (by rw [BitVec.add_zero]; exact rB₀) rB₈ wC₀ wC₈
  rw [BitVec.add_zero] at Bk
  exact ⟨t', run, Bk⟩

theorem blockAtMem_ck {W B : Addr} (hBW : (⟨B, 16⟩ : Region).Disjoint ⟨W, 2560⟩) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') : blockAtMem m' B = blockAtMem m B :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hBW.sub_right (Lay.wSub (by decide))

theorem blockAtMem_ofs_ck {W : Addr} {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m m') :
    blockAtMem m' (W + BitVec.ofNat 64 ofsO) = blockAtMem m (W + BitVec.ofNat 64 ofsO) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (d := 16) (n := 16) (e := 32) (k := 16) (.inl (by decide)) (by omega) (by omega)

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok {W : Addr} :
    BodyOk W (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, B₁⟩ := addCk_ok h23 h19 rB₀ rB₈ wC₀ wC₈
  obtain ⟨t₂, run₂, b₂, c₂, f₂, g₂, sp₂, rd₂, wr₂⟩ := xorOfs_ok t₁ B (by rw [B₁.gpr _ (by decide), h23])
    (by rw [B₁.gpr _ (by decide), h19]) (by rw [B₁.rd, B₁.wr]; exact rB₀) (by rw [B₁.rd, B₁.wr]; exact rB₈)
    (by rw [B₁.wr]; exact wB₀) (by rw [B₁.wr]; exact wB₈) (by rw [B₁.rd, B₁.wr]; exact rO₀)
    (by rw [B₁.rd, B₁.wr]; exact rO₈) (by rw [B₁.wr]; exact wC₀) (by rw [B₁.wr]; exact wC₈) hBW
  refine ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [sp₂, B₁.sp], by rw [rd₂, B₁.rd], by rw [wr₂, B₁.wr]⟩
  · rw [b₂, blockAtMem_ck hBW B₁.frame, blockAtMem_ofs_ck B₁.frame]
  · rw [c₂, B₁.val]
  · exact (B₁.frame.mono (by simp)).trans f₂
  · rw [g₂ r hr, B₁.gpr r hr]

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok {W : Addr} :
    BodyOk W (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₁, run₁, b₁, c₁, f₁, g₁, sp₁, rd₁, wr₁⟩ := xorOfs_ok t B h23 h19 rB₀ rB₈ wB₀ wB₈ rO₀ rO₈ wC₀ wC₈ hBW
  obtain ⟨t₂, run₂, B₂⟩ := addCk_ok (t := t₁) (by rw [g₁ _ (by decide), h23])
    (by rw [g₁ _ (by decide), h19]) (by rw [rd₁, wr₁]; exact rB₀) (by rw [rd₁, wr₁]; exact rB₈)
    (by rw [wr₁]; exact wC₀) (by rw [wr₁]; exact wC₈)
  refine ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, ?_, fun r hr => ?_,
    by rw [B₂.sp, sp₁], by rw [B₂.rd, rd₁], by rw [B₂.wr, wr₁]⟩
  · rw [blockAtMem_ck hBW B₂.frame, b₁]
  · rw [B₂.val, c₁, b₁]
  · exact f₁.trans (B₂.frame.mono (by simp))
  · rw [B₂.gpr r hr, g₁ r hr]

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x23, .x24, .x25]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them. -/
structure PassInv (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (fB : Block → Block → Block) (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env K W D R n SP t
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  x23 : t.gpr .x23 = D + BitVec.ofNat 64 (16 * i)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (i + 1)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (m - i)
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem pass_step {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W t₀ D (16 * m)) (hm : m < 2 ^ 60) {t : State} {i : Nat} (hi : i < m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv K W D R n SP m O0 l X fB ckF t₀ t' (i + 1) := by
  have hDt : DBuf K W t D (16 * m) := hD.of_eq P.rd P.wr
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega)
  have E := P.env
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (lNtz_ok E.x19 E.perm.w (by omega) (by omega) P.x25 P.l0) fun t₁ P₁ => ?_))
  have h19₁ : t₁.gpr .x19 = W := by rw [P₁.gpr _ (by decide), E.x19]
  obtain ⟨t₂, run₂, B₂⟩ := xor16_ok (s := t₁) (b := .x19) (a := lO) (d := ofsO) (by decide) (by decide) h19₁ h19₁
    (by decide) (by decide) (by decide) (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.rd, P₁.wr]; exact E.perm.wR (by decide))
    (by rw [P₁.wr]; exact E.perm.wW (by decide)) (by rw [P₁.wr]; exact E.perm.wW (by decide))
  refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    rw [B₂.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      P₁.gpr r hr]
  have rd₂ : t₂.rd = t.rd := by rw [B₂.rd, P₁.rd]
  have wr₂ : t₂.wr = t.wr := by rw [B₂.wr, P₁.wr]
  have sp₂ : t₂.sp = t.sp := by rw [B₂.sp, P₁.sp]
  have h19₂ : t₂.gpr .x19 = W := by rw [g₂ _ (by decide), E.x19]
  have h23₂ : t₂.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₂ _ (by decide), P.x23]
  have fW₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩] t.mem t₂.mem :=
    (P₁.frame.mono (by simp)).trans (B₂.frame.mono (by simp))
  have kW₂ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₂.mem Q = blockAtMem t.mem Q :=
    fun hQ => blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have ofs₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [B₂.val, blockAtMem_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), P.ofs,
      P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kW₂ hBi.w, P.blk i hi]; simp
  obtain ⟨t₃, run₃, blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ := hB t₂ _ h23₂ h19₂
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact hBi.rd _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      by simpa using Offset.contains_base (D + BitVec.ofNat 64 (16 * i)) (d := 0) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [wr₂]; exact hBi.wr _ _ ⟨_, List.mem_singleton_self _,
      Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)⟩)
    (by rw [rd₂, wr₂]; exact E.perm.wR (by decide)) (by rw [rd₂, wr₂]; exact E.perm.wR (by decide))
    (by rw [wr₂]; exact E.perm.wW (by decide)) (by rw [wr₂]; exact E.perm.wW (by decide)) hBi.w
  have g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃ r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h | h | h <;> simp [h])),
      g₂ r hr]
  have x24₃ : t₃.gpr .x24 = BitVec.ofNat 64 (m - i) := by rw [g₃' _ (by decide), P.x24]
  have x25₃ : t₃.gpr .x25 = BitVec.ofNat 64 (i + 1) := by rw [g₃' _ (by decide), P.x25]
  have x23₃ : t₃.gpr .x23 = D + BitVec.ofNat 64 (16 * i) := by rw [g₃' _ (by decide), P.x23]
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem t₃.mem Q = blockAtMem t.mem Q := fun h₁ h₂ => by
    rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right (Lay.wSub (by decide))), kW₂ h₂]
  refine Proof.AesGcm.AArch64.WP.run (Q := fun t' => t' = ((t₃.write .x .x23 (t₃.gpr .x23 + 16#64)).write .x .x25
    (t₃.gpr .x25 + 1#64)).write .x .x24 (t₃.gpr .x24 - 1#64))
    ⟨_, by rw [runBlock_append, run₃, Option.bind_some]; orun [nextBlock], rfl⟩ fun t' ht' => ?_
  subst ht'
  have hw := hD.wrap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩ <;>
    try simp only [mem_write, rd_write, wr_write]
  · exact E.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [gpr_write, reduceCtorEq, ite_false] <;>
        exact g₃' _ (by decide))
      (by simp only [sp_write]; rw [sp₃, sp₂]) (by simp only [rd_write]; rw [rd₃, rd₂])
      (by simp only [wr_write]; rw [wr₃, wr₂])
  · exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · rw [rd₃, rd₂, P.rd]
  · rw [wr₃, wr₂, P.wr]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x23₃, Offset.add_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x25₃, ← BitVec.ofNat_add]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x24₃]
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 16) (n := 16) (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega)
      rw [kB₃ (Offset.disjoint D (by omega) (by omega) (by omega)) hBk.w, P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hBi.w.sub_right (Lay.wSub (W := W) (d := 80) (n := 16) (by decide))).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]

theorem pass_ok {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk W body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W t₀ D (16 * m)) (hm0 : 0 < m) (hm : m < 2 ^ 60) {t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv K W D R n SP m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv K W D R n SP m O0 l X fB ckF t₀ u i) ?_
    (m - 0) _ ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hD hm hi P) fun u' P' => ?_
  have ev := eval_nonzero P'.x24 (by omega)
  by_cases he : m - (i + 1) = 0
  · left
    exact ⟨ev.trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.AArch64

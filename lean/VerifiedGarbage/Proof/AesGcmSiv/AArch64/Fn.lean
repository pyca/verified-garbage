import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Cmp

/-!
# AES-GCM-SIV on AArch64: the arguments and the entry

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the public arguments (`prmOf`), how they lie (`lay_of`)
and what the state may access (`args_of_seal`, `args_of_open`). `entry`
loads `W` from the stack, saves our caller's registers at `W + 128`, as
AES-GCM does, keeps the arguments in `x19`–`x26` and `tag` at `W + 216`
(`entry_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (saved)
open VG.Proof.AesGcm.AArch64 (covers_of_mem covers_left SavedAt savedR save_ok savedMem_frame savedAt_save in_off
  Others)

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := s.gpr .x0
  W := stackArg s 0
  N := s.gpr .x2
  A := s.gpr .x3
  D := s.gpr .x5
  T := s.gpr .x7
  SP := s.sp
  R := (s.gpr .x1).toNat
  al := (s.gpr .x4).toNat
  n := (s.gpr .x6).toNat

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, _, _, b1, b2, b3, b4, b5, b6, _, hR⟩ := h
  exact ⟨b1, b6, b2, b3, b4, d2, d1, d4, d3, d6, d5, d9, b5, d8, d7, hR, BitVec.isLt _, BitVec.isLt _⟩

/-- The permissions, from the buffers' coverage. -/
theorem perm_of_cov {s : State} (hk : Covers [⟨s.gpr .x0, 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨s.gpr .x2, 12⟩] (s.rd ++ s.wr)) (hA : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 0, 3808⟩] s.wr)
    (hT : Covers [⟨s.gpr .x7, 16⟩] (s.rd ++ s.wr)) : Perm (prmOf s) s :=
  ⟨hk, hN, hA, hD, hW, hT⟩

/-- `seal`'s layout and permissions, its tag to write, and its stack argument
to read. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [⟨s.gpr .x7, 16⟩] s.wr ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩, args s],
      Covers [r] (s.rd ++ s.wr) := fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨s.gpr .x7, 16⟩, ⟨stackArg s 0, 3808⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (covers_left (mwr _ (by simp))), mwr _ (by simp), mrd _ (by simp)⟩

/-- `open`'s layout and permissions, with its received tag to read, and its
stack argument to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    Lay (prmOf s) ∧ Perm (prmOf s) s ∧ Covers [args s] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .x0, 240⟩ : Region), ⟨s.gpr .x2, 12⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x7, 16⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region), ⟨stackArg s 0, 3808⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨lay_of hl, perm_of_cov (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)) (mrd _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the entry writes: the save area and `tag`'s address. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 96⟩

/-- `tag`'s address, at `W + 216`. -/
abbrev TagSlot (p : Prm) (m : Mem) : Prop := m.readW (p.W + BitVec.ofNat 64 216) 64 = p.T

/-- `entry`. -/
theorem entry_ok {s : State} (P : Perm (prmOf s) s) (hA : Covers [args s] (s.rd ++ s.wr)) :
    WP isa (.block entry) s fun s₁ => Env (prmOf s) s₁ ∧ SavedAt s₁.mem (prmOf s).W s ∧
      Frame [entryR (prmOf s).W] s.mem s₁.mem ∧ TagSlot (prmOf s) s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₀ : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa [args, stackArgAddr] using in_off (d := 0) (n := 8) hA (by decide) (by decide)
  refine WP.block_append (WP.block_append (WP.run ⟨_, by grun [BitVec.add_zero, a₀], rfl⟩ fun s₀ hs₀ => ?_))
  subst hs₀
  have hW₀ : (s.write .x .x9 (s.mem.readW s.sp 64)).gpr .x9 = (prmOf s).W := by
    simp [gpr_write, prmOf, stackArg, stackArgAddr]
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok _ .x9 hW₀ (by simpa only [wr_write] using P.w2560)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hWv : (prmOf s).W = s.mem.readW s.sp 64 := by simp [prmOf, stackArg, stackArgAddr, Mem.readW]
  have w216 : InRegions s₁.wr (s.mem.readW s.sp 64 + BitVec.ofNat 64 216) 8 := by
    rw [wr₁, ← hWv]; simpa only [wr_write] using in_off P.w (show 216 + 8 ≤ 3808 by decide) (by decide)
  refine WP.run ⟨_, by grun [g₁, BitVec.add_zero, w216], rfl⟩ fun s₂ hs₂ => ?_
  subst hs₂
  have hs : ∀ r ∈ saved, (s.write .x .x9 (s.mem.readW s.sp 64)).gpr r.1 = s.gpr r.1 := by
    intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have sv : SavedAt s₁.mem (prmOf s).W s := by
    rw [m₁]; exact fun p hp => (savedAt_save _ _ _ p hp).trans (hs p hp)
  have fS : Frame [entryR (prmOf s).W] s.mem s₁.mem := by
    rw [m₁]; simp only [mem_write]
    exact (savedMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have c216 : (entryR (prmOf s).W).Contains ((prmOf s).W + BitVec.ofNat 64 216) (64 / 8) := by
    rw [show (prmOf s).W + BitVec.ofNat 64 216 = ((prmOf s).W + BitVec.ofNat 64 128) + BitVec.ofNat 64 88 from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by decide) (by decide)
  have e : ∀ (m : Mem) (a : Addr) (v : BitVec 64), m.write a 8 v = m.writeW a v := fun m a v => by
    simp [Mem.writeW]
  rw [← hWv] at *
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [sp_write]; rw [sp₁]; rfl,
    P.of_eq (by simp only [rd_write]; exact rd₁) (by simp only [wr_write]; exact wr₁)⟩, ?_, ?_, ?_, ?_, ?_⟩
  iterate 8 (simp [gpr_write, g₁, prmOf, ofNat_toNat64, stackArg, stackArgAddr, Mem.readW])
  · simp only [mem_write, e]
    exact sv.frame ((Frame.refl [(⟨(prmOf s).W + BitVec.ofNat 64 216, 8⟩ : Region)] _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · simp only [mem_write, e]
    exact fS.writeW (List.mem_singleton_self _) _ c216
  · simp only [mem_write, e, TagSlot, Mem.readW_writeW_self64]
    simp [gpr_write, g₁, prmOf]
  · simp only [rd_write]; exact rd₁
  · simp only [wr_write]; exact wr₁

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

/-- `recv`: the received tag, at `T`, copied to `W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨p.W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.W 16 = bytesAt s.mem p.T 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions (s.rd ++ s.wr) p.T 8 := by simpa using in_off (d := 0) (n := 8) E.perm.t (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) E.perm.t (by decide) (by decide)
  have w₀ : InRegions s.wr p.W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  have hs : Mem.Sep (p.T + BitVec.ofNat 64 8) (64 / 8) p.W (64 / 8) :=
    L.t_w.sep (Offset.contains_base p.T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base p.W (d := 0) (n := 8) (k := 3808) (by decide) (by decide))
  refine ⟨_, by simp only [recv]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-- `tagOut`: the tag at `W` copied to `T`, which the state may write. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hT : TagSlot p s.mem)
    (hTw : Covers [⟨p.T, 16⟩] s.wr) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨p.T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem p.T 16 = bytesAt s.mem p.W 16 ∧ s'.gpr .x9 = p.T ∧ Others [.x9, .x10] s s' ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := E.perm.wR (show 216 + 8 ≤ 3808 by decide)
  have t₀ : InRegions s.wr p.T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have hT' : s.mem.read (p.W + BitVec.ofNat 64 216) 8 = p.T := by rw [read8_readW]; exact hT
  have hs : Mem.Sep (p.W + BitVec.ofNat 64 8) (64 / 8) p.T (64 / 8) :=
    L.t_w.symm.sep (Offset.contains_base p.W (d := 8) (n := 8) (k := 3808) (by decide) (by decide))
      (by simpa using Offset.contains_base p.T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by simp only [tagOut]; grun [E.x19, BitVec.add_zero, r₀, hT', t₀, t₈, w₀, w₈], ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, read8_readW]
    exact bytesAt_copy2 _ _ _ hs
  · simp [gpr_write]

/-! ## Regions -/

/-- Proves that a region is disjoint from each of a list of regions: parts
of `W`, the data, or the key schedule. -/
macro "disj_tac" L:term : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  repeat' apply And.intro
  all_goals first
    | (with_reducible refine Lay.w_w $L (.inl ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.w_w $L (.inr ?_) ?_ ?_) <;> decide
    | (with_reducible refine Lay.d_w' $L ?_) <;> decide
    | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide
    | (with_reducible refine Lay.k_w' $L ?_) <;> decide
    | (with_reducible refine Lay.n_w' $L ?_) <;> decide
    | (with_reducible refine Lay.a_w' $L ?_) <;> decide
    | with_reducible exact Lay.k_d $L
    | with_reducible exact Lay.n_d $L
    | with_reducible exact Lay.a_d $L
    | (with_reducible refine Lay.t_w' $L ?_) <;> decide
    | with_reducible exact Lay.t_d $L
    | with_reducible exact (Lay.t_d $L).symm
    | with_reducible exact (Lay.d_w $L).symm))

end VG.Proof.AesGcmSiv.AArch64

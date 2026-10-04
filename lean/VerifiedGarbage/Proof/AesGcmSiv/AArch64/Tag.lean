import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval

/-!
# AES-GCM-SIV on AArch64: the tag (`tag`)

Untrusted: everything here is checked by Lean. `tag o` encrypts the block at
`W + 96` with the encryption key's schedule at `W + 512` into the block at
`W + o`, by `vg_aes_ctr32` of one zero block from a copy of it at `W + 112`
(`tag_ok`): the tag, the tag `open` computes, and counter mode's last
keystream block.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (GcmImpl CtrCall CtrPost ctr_call covers_cons covers_nil covers_append
  add_ofNat_assoc Others)

theorem blockAt_zero2 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero2 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 64)).writeW
    (W + BitVec.ofNat 64 120) (m.readW (W + BitVec.ofNat 64 104) 64)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) := by
  rw [copyMem, show W + BitVec.ofNat 64 120 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, show W + BitVec.ofNat 64 120 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 2048, 2048⟩]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : Prm) (o : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = t.gpr .x27
  x28 : t'.gpr .x28 = t.gpr .x28
  frame : Frame (tagR p.W o) t.mem t'.mem
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 512) p.R (bytesAt t.mem (p.W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {p : Prm} {t : State} (E : Env p t) {o : Nat} (ho : o = 0 ∨ o = 224 ∨ o = 240) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [Impl.AesGcm.AArch64.ptr .x3 .x19 o]) t =
      some t₁ ∧ t₁.mem = Proof.Cmac.zero2 (copyMem t.mem p.W) (p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .x0 = p.W + BitVec.ofNat 64 512 ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧
      t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧ t₁.gpr .x3 = p.W + BitVec.ofNat 64 o ∧
      t₁.gpr .x4 = BitVec.ofNat 64 1 ∧ t₁.gpr .x5 = p.W + BitVec.ofNat 64 2048 ∧
      Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 8 ≤ 4096 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 4096 by decide)
  have z₀ := E.perm.wW (show o + 8 ≤ 4096 by omega)
  have z₈ := E.perm.wW (show o + 8 + 8 ≤ 4096 by omega)
  have o₁ : o % 8 = 0 := by omega
  have o₂ : o < 32768 := by omega
  have o₃ : (o + 8) % 8 = 0 := by omega
  have o₄ : o + 8 < 32768 := by omega
  have o₅ : o < 4096 := by omega
  refine ⟨_, by simp only [copy16, zero16, ctrArgs]; grun [E.x19, E.x22, r₀, r₈, w₀, w₈, z₀, z₈, o₁, o₂, o₃, o₄, o₅],
    ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 112) 8 v).read (p.W + BitVec.ofNat 64 104) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 104) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [Proof.Cmac.zero2, copyMem, add_ofNat_assoc]
    simp only [mem_write, sep, Mem.writeW, BitVec.setWidth_eq, read8_readW, movz0]
  all_goals simp [gpr_write, E.x19, E.x22]

/-- The arguments of `tag o`'s call, as `vg_aes_ctr32` needs them. -/
theorem tagCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {o : Nat} (ho : o = 0 ∨ o = 224 ∨ o = 240)
    (x0 : t₁.gpr .x0 = p.W + BitVec.ofNat 64 512) (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R)
    (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112) (x3 : t₁.gpr .x3 = p.W + BitVec.ofNat 64 o)
    (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1) (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 2048) :
    CtrCall t₁ (p.W + BitVec.ofNat 64 512) (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 o)
      (p.W + BitVec.ofNat 64 2048) p.R 1 :=
  have hw := L.ww
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by rw [L.toNat_W (by omega)]; omega
    n_lt := by decide
    kc := L.w_w (.inr (by decide)) (by decide) (by decide)
    kd := L.w_w (.inr (by omega)) (by decide) (by omega)
    ks := L.w_w (.inl (by decide)) (by decide) (by decide)
    cd := (L.w_w (by omega) (by omega) (by decide) :
      (⟨p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 112, 16⟩).symm
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := L.w_w (.inl (by omega)) (by omega) (by decide)
    reads := covers_append (covers_cons (E₁.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (E₁.perm.wCR (by omega))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by omega))
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

theorem tag_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat}
    (ho : o = 0 ∨ o = 224 ∨ o = 240) :
    WP isa (tag v.callees o) t (TagPost p o t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok E ho
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dO : (⟨p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc := tagCall L E₁ ho x0 x1 x2 x3 x4 x5
  have fZ := Proof.Cmac.frame_store2 (m := copyMem t.mem p.W) (p.W + BitVec.ofNat 64 o) 0 0
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero2]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero2, Proof.AesGcm.AArch64.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (p.W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact blockAt_zero2 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (L.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [Nat.mul_one] at fc
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [P.rd, rd₁], by rw [P.wr, wr₁],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 512) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.AArch64

import VerifiedGarbage.Proof.AesGcmSiv.Arm.Polyval

/-!
# AES-GCM-SIV on ARMv7: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 512` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' add_ofNat_assoc
  add_ofNat_zero mem_store gpr_store sp_store rd_store wr_store z_store)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [add_ofNat_assoc, Nat.reduceAdd]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (SP : BitVec 32) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 2048, 2048⟩, below SP]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : Prm) (o : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = t.gpr .r4
  r5 : t'.gpr .r5 = t.gpr .r5
  frame : Frame (tagR (State.addr p.W) p.SP o) t.mem t'.mem
  out : bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 512) p.R
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16)

/-- The arguments of `tag o`'s call. -/
theorem tagArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : o = 0 ∨ o = 224 ∨ o = 240) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
        ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 2048 ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 4 ≤ 4096 by decide)
  have r₁ := E.perm.wR (show 100 + 4 ≤ 4096 by decide)
  have r₂ := E.perm.wR (show 104 + 4 ≤ 4096 by decide)
  have r₃ := E.perm.wR (show 108 + 4 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 112 + 4 ≤ 4096 by decide)
  have w₁ := E.perm.wW (show 116 + 4 ≤ 4096 by decide)
  have w₂ := E.perm.wW (show 120 + 4 ≤ 4096 by decide)
  have w₃ := E.perm.wW (show 124 + 4 ≤ 4096 by decide)
  have z₀ := E.perm.wW (show o + 4 ≤ 4096 by omega)
  have z₁ := E.perm.wW (show o + 4 + 4 ≤ 4096 by omega)
  have z₂ := E.perm.wW (show o + 8 + 4 ≤ 4096 by omega)
  have z₃ := E.perm.wW (show o + 12 + 4 ≤ 4096 by omega)
  have o₁ : o < 4096 := by omega
  have o₂ : o + 4 < 4096 := by omega
  have o₃ : o + 8 < 4096 := by omega
  have o₄ : o + 12 < 4096 := by omega
  have oe : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl | rfl <;> decide
  refine ⟨_, by simp only [copy16, Impl.AesGcm.Arm.zero16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃,
    w₀, w₁, w₂, w₃, z₀, z₁, z₂, z₃, o₁, o₂, o₃, o₄, oe], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, by rfl,
    by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.zero4,
      Proof.Cmac.store4, copyMem, add_ofNat_assoc, Nat.reduceAdd]
    rfl
  all_goals simp [gpr_setReg, E.r8, E.r11]

/-- The arguments of `tag o`'s call, as `vg_aes_ctr32` needs them. -/
theorem tagCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {o : Nat} (ho : o = 0 ∨ o = 224 ∨ o = 240)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 512) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 o)
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 2048) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o)
      (p.W + BitVec.ofNat 32 2048) p.R 1 := by
  have hw := L.ww
  have o₁ : o < 4096 := by omega
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega,
    by rw [L.wN (by decide)]; omega, by rw [L.wN o₁]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 512 < 4096 by decide), L.wA (show 112 < 4096 by decide), L.wA o₁,
      L.wA (show 2048 < 4096 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.w_w (by omega) (by omega) (by decide) :
      (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by omega)
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by omega))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

theorem tag_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : o = 0 ∨ o = 224 ∨ o = 240) :
    WP isa (tag o) t (TagPost p o t) := by
  have hw := L.ww
  have o₁ : o < 4096 := by omega
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok L E ho
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dO : (⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have cc := tagCall L E₁ ho r0 r1 r2 r3 r12 lr
  have fZ := Proof.Cmac.frame_store4 (m := copyMem t.mem (State.addr p.W)) (State.addr p.W + BitVec.ofNat 64 o) 0 0 0 0
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o, 16⟩]
      t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.Arm.bytesAt_frame fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (State.addr p.W + BitVec.ofNat 64 o) = 0 := by
    rw [hm₁]; exact blockAt_zero4 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (L.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 512 < 4096 by decide), L.wA (show 112 < 4096 by decide), L.wA o₁,
    L.wA (show 2048 < 4096 by decide), E₁.sp, Nat.mul_one] at fc hout
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [P.rd, rd₁], by rw [P.wr, wr₁],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide)],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 512) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.Arm

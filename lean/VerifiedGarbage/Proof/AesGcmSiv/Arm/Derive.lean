import VerifiedGarbage.Proof.AesGcmSiv.Arm.Env
import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.Cmac.Block32

/-!
# AES-GCM-SIV on ARMv7: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 176` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_ok`): after the loop, the halves of
`derive_keys` (`derive_ok`, `DInv.keys`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc
  covers_cons covers_nil covers_append' eval_ne' z_cmp ofNat_sub32 ofNat_add32 toNat32 mem_store gpr_store sp_store
  rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags wr_subFlags)

/-- An offset into the nonce, as a 64-bit address. -/
theorem Lay.nA {p : Prm} (L : Lay p) {d : Nat} (hd : d < 12) :
    State.addr (p.N + BitVec.ofNat 32 d) = State.addr p.N + BitVec.ofNat 64 d :=
  addr_add (by have := L.nw; omega)

/-- The memory after a step's block: the counter block and a zero block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)
    (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)) (W + BitVec.ofNat 64 176)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (h4 : t.gpr .r4 = BitVec.ofNat 32 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = derMem t.mem (State.addr p.W) (State.addr p.N) i ∧
      t₁.gpr .r0 = p.K ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧ t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧
      t₁.gpr .r3 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r12 = BitVec.ofNat 32 1 ∧
      t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have n₀ : InRegions (t.rd ++ t.wr) (State.addr p.N) 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  have w₅ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  have w₆ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  have w₇ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  have w₈ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [deriveBlock, Impl.AesGcm.Arm.zero16]; srun [E.r10, E.r11, add_ofNat_zero, L.nA, L.wA,
    n₀, n₄, n₈, w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, derMem, Proof.Cmac.zero4,
      Proof.Cmac.store4, h4, add_ofNat_assoc, Nat.reduceAdd]
    rfl
  · simp [gpr_setReg, E.r9]
  · simp [gpr_setReg, E.r8]
  · simp [gpr_setReg, E.r11]
  · simp [gpr_setReg, E.r11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, E.r11]


/-- What the code after a step's call writes: the 8 bytes kept. -/
def postMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (m.readW (W + BitVec.ofNat 64 176) 32)).writeW
    (W + BitVec.ofNat 64 (20 + 8 * i)) (m.readW (W + BitVec.ofNat 64 180) 32)

theorem ofNat_lsl3 {p : Prm} (L : Lay p) {i k : Nat} (hi : 8 * i + k < 3760) :
    State.addr (p.W + BitVec.ofNat 32 i <<< 3 + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 (k + 8 * i) := by
  rw [ofNat_lsl32, add32_ofNat_assoc, L.wA (by omega)]
  congr 2; omega

/-- The code after the call of a step. -/
theorem derPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h4 : t.gpr .r4 = BitVec.ofNat 32 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧ t'.mem = postMem t.mem (State.addr p.W) i ∧
      t'.gpr .r4 = BitVec.ofNat 32 (i + 1) ∧ t'.z = decide (i + 1 = p.R / 2 - 1) ∧
      Others [.r0, .r1, .r2, .r4, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have r₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  have wo₀ := E.perm.wW (d := 16 + 8 * i) (n := 4) (by omega)
  have wo₁ := E.perm.wW (d := 20 + 8 * i) (n := 4) (by omega)
  have ea₀ := ofNat_lsl3 L (i := i) (k := 16) (by omega)
  have ea₁ := ofNat_lsl3 L (i := i) (k := 20) (by omega)
  refine ⟨_, by simp only [derivePost]; srun [E.r8, E.r11, h4, L.wA, ea₀, ea₁, r₀, r₁, wo₀, wo₁], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, postMem]
  · simp [gpr_setReg, h4, ofNat_add32]
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, z_store, gpr_store, h4, E.r8,
      ofNat_lsr32 L.ofNat_R_lt, ofNat_add32]
    rw [ofNat_sub32 (by rcases hR with h | h <;> rw [h] <;> decide) (by have := L.ofNat_R_lt; omega),
      z_cmp (by have := L.ofNat_R_lt; omega) (by have := L.ofNat_R_lt; omega), Nat.pow_one]
    congr 1; apply propext; omega

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] m (postMem m W i) := by
  have c₀ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (16 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  have c₁ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (20 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega) (by omega) (by omega)
  unfold postMem
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₀).writeW (List.mem_singleton_self _) _ c₁

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  rw [derMem, Proof.Cmac.zero4, Proof.AesGcm.Arm.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_ofNat, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add,
    add_ofNat_assoc]
  simp only [List.append_assoc]


/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (derMem m W N i) (W + BitVec.ofNat 64 176) = 0 := by
  rw [derMem, Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 176, 16⟩] m (derMem m W N i) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
    ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- What `derive` writes. -/
abbrev derR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 176, 16⟩,
    ⟨W + BitVec.ofNat 64 1712, 2048⟩, below SP]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env p t
  r4 : t.gpr .r4 = BitVec.ofNat 32 i
  le : i ≤ p.R / 2 - 1
  frame : Frame (derR (State.addr p.W) p.SP) σ.mem t.mem
  out : bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (bytesAt σ.mem (State.addr p.N) 12) i

/-- Buffers apart from `W` and the stack below `SP` are kept by `derive`. -/
theorem bytesAt_derR {p : Prm} {P : Addr} {len : Nat}
    (hP : (⟨P, len⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (hb : (below p.SP).Disjoint ⟨P, len⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (derR (State.addr p.W) p.SP) m m') :
    bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hP.sub_right (Lay.wSub (by decide))
    · exact hb.symm) hl

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (derR (State.addr p.W) p.SP) m m') :
    Spec.GcmSiv.ctxCiph m' (State.addr p.K) p.R = Spec.GcmSiv.ctxCiph m (State.addr p.K) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_derR (L.k_w.sub_left (Region.sub_prefix L.rounds_le))
    (L.bk.sub_right (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) (r0 : t₁.gpr .r0 = p.K)
    (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R) (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112)
    (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 176) (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1)
    (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have ww := L.ww
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, L.kw,
    by rw [L.wN (by decide)]; omega, by rw [L.wN (by decide)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 112 < 3760 by decide), L.wA (show 176 < 3760 by decide),
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.bk
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact E₁.perm.k
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by decide))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))


/-- The 8 bytes a step keeps: the first 8 of the block at `W + 176`. -/
theorem postMem_bytes (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    bytesAt (postMem m W i) (W + BitVec.ofNat 64 (16 + 8 * i)) 8 = bytesAt m (W + BitVec.ofNat 64 176) 8 := by
  have e : W + BitVec.ofNat 64 (20 + 8 * i) = W + BitVec.ofNat 64 (16 + 8 * i) + BitVec.ofNat 64 4 := by
    rw [add_ofNat_assoc]; congr 2; omega
  have d : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  rw [show (8 : Nat) = 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← e,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, postMem,
    Proof.Cmac.readW_writeW_disj _ d.symm, Mem.readW_writeW_self32, Mem.readW_writeW_self32, add_ofNat_assoc]

/-- A step of `derive`. -/
theorem derStep_ok {p : Prm} (L : Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq Impl.AesGcm.Arm.ctrFrame (.block derivePost))) t fun t' =>
      DInv p σ (i + 1) t' ∧ t'.z = decide (i + 1 = p.R / 2 - 1) := by
  have hR := L.rounds
  have hw := L.ww
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega
  have eN : bytesAt t.mem (State.addr p.N) 12 = bytesAt σ.mem (State.addr p.N) 12 :=
    bytesAt_derR L.n_w L.bn (by decide) I.frame
  have eK := ciph_derR L I.frame
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok L I.env I.r4
  have E₁ : Env p t₁ := I.env.of_others ho₁ sp₁ rd₁ wr₁
  have cc := derCall L E₁ r0 r1 r2 r3 r12 lr
  have hb₁ : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      Spec.GcmSiv.le32 i ++ bytesAt t.mem (State.addr p.N) 12 := by
    rw [hm₁]; exact derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (State.addr p.W + BitVec.ofNat 64 176) = 0 := by
    rw [hm₁]; exact derZero_block _ _ _ _
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩]
      t.mem t₁.mem := by rw [hm₁]; exact derMem_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call cc) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = BitVec.ofNat 32 i := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), I.r4]
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 112 < 3760 by decide), L.wA (show 176 < 3760 by decide),
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  obtain ⟨t₃, run₃, hm₃, r4₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := derPost_ok L E₂ hi h4₂
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, by omega, ?_, ?_⟩, z₃⟩
  · -- The frame.
    have mem : ∀ {r : Region}, r ∈ derR (State.addr p.W) p.SP → ∃ r' ∈ derR (State.addr p.W) p.SP, Region.Sub r r' :=
      fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact mem (by simp)
    · rw [hm₃]
      exact (postMem_frame _ _ _ (by omega)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
  · -- The bytes.
    have dW : ∀ {d k : Nat}, d + k ≤ 3760 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨State.addr p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega) (by omega) h₁
    have keep : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (postMem_frame _ _ _ (by omega))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.Arm.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact dW (by decide) (by omega)
          · exact (L.bw' (by omega)).symm) (by omega),
        Proof.AesGcm.Arm.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega)) (by omega)]
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R
          (Spec.GcmSiv.le32 i ++ bytesAt σ.mem (State.addr p.N) 12)).take 8 := by
      have e16 : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
          bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 8 ++
            bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.K) p.R = Spec.GcmSiv.ctxCiph t.mem (State.addr p.K) p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega)]
      rw [hm₃, postMem_bytes _ _ _ (by omega),
        show bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 8 =
          (bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.K) (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.K) p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa derive σ (DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  refine WP.seq (Proof.AesGcm.Arm.WP.run (Q := fun t => DInv p σ 0 t) ⟨_, by srun [], ?_⟩ fun t I₀ => ?_)
  · exact ⟨E.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      by simp [gpr_setReg], Nat.zero_le _, by rw [mem_setReg]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_ok L hi I) fun t' ⟨I', hz⟩ => ?_
  have ev := eval_ne' hz
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp [he]), (p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : Prm} (L : Lay p) {σ t : State} (I : DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
        (bytesAt σ.mem (State.addr p.N) 12) =
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.Arm

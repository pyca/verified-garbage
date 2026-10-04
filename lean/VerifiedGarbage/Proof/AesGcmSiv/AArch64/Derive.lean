import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Env
import VerifiedGarbage.Proof.GcmSiv.Spec

/-!
# AES-GCM-SIV on AArch64: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 224` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i`: after the loop, the halves of `derive_keys`
(`derive_ok`, `DInv.keys`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call GcmImpl in_off covers_off covers_left covers_cons
  covers_nil covers_append ofNat_add_ofNat add_ofNat_assoc ofNat_sub lsr_ofNat toNat_ofNat_of_lt eval_nonzero
  Others)

theorem setWidth_rt32 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem read4_readW (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

theorem read8_readW (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

/-- The memory after a step's block: the counter block and a zero block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  ((Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
    (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
    (W + BitVec.ofNat 64 224) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 232) (0 : BitVec 64)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : Prm} {t : State} (E : Env p t) {i : Nat} (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = derMem t.mem p.W p.N i ∧
      t₁.gpr .x0 = p.K ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧ t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧
      t₁.gpr .x3 = p.W + BitVec.ofNat 64 224 ∧ t₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760 ∧
      Others [.x9, .x10, .x11, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  have n₀ : InRegions (t.rd ++ t.wr) p.N 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  have w₁ := E.perm.wW (show 112 + 4 ≤ 3808 by decide)
  have w₂ := E.perm.wW (show 116 + 4 ≤ 3808 by decide)
  have w₃ := E.perm.wW (show 120 + 4 ≤ 3808 by decide)
  have w₄ := E.perm.wW (show 124 + 4 ≤ 3808 by decide)
  have w₅ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
  have w₆ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [deriveBlock, zero16]; grun [E.x19, E.x20, BitVec.add_zero, n₀, n₄, n₈, w₁, w₂, w₃,
    w₄, w₅, w₆], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, derMem, Proof.Cmac.store4, Mem.writeW,
      BitVec.setWidth_eq, setWidth_rt32, read4_readW, h27, add_ofNat_assoc, Nat.reduceAdd, Nat.reduceDiv, movz0]
  · simp [gpr_write, E.x21]
  · simp [gpr_write, E.x22]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19]
  · simp [gpr_write]
  · simp [gpr_write, E.x19]

theorem zc₁ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 224) (64 / 8) :=
  contains_at0 _ (by decide) (by decide)

theorem zc₂ (W : Addr) : (⟨W + BitVec.ofNat 64 224, 16⟩ : Region).Contains (W + BitVec.ofNat 64 232) (64 / 8) := by
  rw [show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact contains_at _ (show 8 + 8 ≤ 16 by decide) (by decide)

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  have c₁ := zc₁ W
  have c₂ := zc₂ W
  rw [derMem, Proof.AesGcm.AArch64.bytesAt_frame
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (derMem m W N i) (W + BitVec.ofNat 64 224) = 0 := by
  rw [derMem, Spec.Gcm.blockAt, show W + BitVec.ofNat 64 232 = W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8 by
    rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩] m (derMem m W N i) :=
  (((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (zc₁ W)).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (zc₂ W)

/-- What `derive` writes. -/
abbrev derR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩,
    ⟨W + BitVec.ofNat 64 1760, 2048⟩]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env p t
  x27 : t.gpr .x27 = BitVec.ofNat 64 i
  le : i ≤ p.R / 2 - 1
  frame : Frame (derR p.W) σ.mem t.mem
  out : bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (bytesAt σ.mem p.N 12) i

/-- The code after the call of a step. -/
theorem derPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧
      t'.mem = t.mem.writeW (p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (p.W + BitVec.ofNat 64 224) 64) ∧
      t'.gpr .x27 = BitVec.ofNat 64 (i + 1) ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) ∧
      Others [.x9, .x10, .x27] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have rb := E.perm.wR (show 224 + 8 ≤ 3808 by decide)
  have wo := E.perm.wW (d := 16 + 8 * i) (n := 8) (by omega)
  have ea : p.W + BitVec.ofNat 64 i <<< 3 + BitVec.ofNat 64 16 = p.W + BitVec.ofNat 64 (16 + 8 * i) := by
    rw [ofNat_lsl, add_ofNat_assoc]; congr 2; omega
  rw [← ea] at wo
  refine ⟨_, by simp only [derivePost]; grun [E.x19, E.x22, h27, rb, wo], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
      read8_readW, ea]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27, ofNat_add_ofNat, E.x22]
    rw [lsr_ofNat _ _ (by omega), ofNat_sub (by omega) (by omega), ofNat_sub (by omega) (by omega)]

/-- Buffers outside `W` are kept by `derive`. -/
theorem bytesAt_derR {p : Prm} (_L : Lay p) {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨p.W, 3808⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (derR p.W) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (derR p.W) m m') :
    Spec.GcmSiv.ctxCiph m' p.K p.R = Spec.GcmSiv.ctxCiph m p.K p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_derR L (L.k_w.sub_left (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) (x0 : t₁.gpr .x0 = p.K)
    (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R) (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112)
    (x3 : t₁.gpr .x3 = p.W + BitVec.ofNat 64 224) (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1)
    (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 64 112) (p.W + BitVec.ofNat 64 224) (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by rw [L.toNat_W (by decide)]; have := L.ww; omega
    n_lt := by decide
    kc := L.k_w' (by decide)
    kd := L.k_w' (by decide)
    ks := L.k_w' (by decide)
    cd := L.w_w (.inl (by decide)) (by decide) (by decide)
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := L.w_w (.inl (by decide)) (by decide) (by decide)
    reads := covers_append (covers_cons E₁.perm.k covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (E₁.perm.wCR (by decide))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (E₁.perm.wC (by decide))
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) t fun t' =>
      DInv p σ (i + 1) t' ∧ t'.gpr .x10 = BitVec.ofNat 64 (p.R / 2 - 1 - (i + 1)) := by
  have hR := L.rounds
  have hw := L.ww
  have eN : bytesAt t.mem p.N 12 = bytesAt σ.mem p.N 12 := bytesAt_derR L L.n_w (by decide) I.frame
  have eK : Spec.GcmSiv.ctxCiph t.mem p.K p.R = Spec.GcmSiv.ctxCiph σ.mem p.K p.R := ciph_derR L I.frame
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok I.env I.x27
  have E₁ : Env p t₁ := I.env.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have cc := derCall L E₁ x0 x1 x2 x3 x4 x5
  have hb₁ : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem p.N 12 := by
    rw [hm₁]; exact derBlock_bytes _ _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (p.W + BitVec.ofNat 64 224) = 0 := by rw [hm₁]; exact derZero_block _ _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact derMem_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h27₂ : t₂.gpr .x27 = BitVec.ofNat 64 i := by rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), I.x27]
  obtain ⟨t₃, run₃, hm₃, x27₃, x10₃, ho₃, sp₃, rd₃, wr₃⟩ := derPost_ok L E₂ hi h27₂
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep (fun r hr => ho₃ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃, x27₃, by omega, ?_, ?_⟩,
    x10₃⟩
  · -- The frame.
    have fc := P.frame
    refine (I.frame.trans (f₁.sub fun r hr => ?_)).trans ((fc.sub fun r hr => ?_).trans (by
        rw [hm₃]
        exact (Frame.refl _ _).writeW (List.mem_cons_self) _ (Offset.contains p.W (d := 16 + 8 * i) (n := 8)
          (e := 16) (k := 48) (by omega) (by omega) (by omega))))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  · -- The bytes.
    have fc := P.frame
    have dW : ∀ {d k : Nat}, d + k ≤ 3808 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega) (by omega) h₁
    have keep : bytesAt t₃.mem (p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.AArch64.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self (p.W + BitVec.ofNat 64 (16 + 8 * i)) 8))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega) (by omega)) (by omega),
        Proof.AesGcm.AArch64.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact dW (by decide) (by omega)) (by omega),
        Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega)) (by omega)]
    have hout := P.out
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem p.K p.R (Spec.GcmSiv.le32 i ++ bytesAt σ.mem p.N 12)).take 8 := by
      have e16 : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 =
          bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 8 ++
            bytesAt t₂.mem (p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem p.K p.R = Spec.GcmSiv.ctxCiph t.mem p.K p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega)]
      rw [hm₃, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW,
        show bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 8 = (bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem p.K (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem p.K p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa (derive v.callees) σ (DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  refine WP.seq (WP.run (Q := fun t => DInv p σ 0 t) ⟨_, by grun [], ?_⟩ fun t I₀ => ?_)
  · exact ⟨E.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write], Nat.zero_le _, by rw [mem_write]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_ok v L hi I) fun t' ⟨I', h10⟩ => ?_
  have ev := eval_nonzero h10 (by omega)
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega), (p.R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : Prm} (L : Lay p) {σ t : State} (I : DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem p.K p.R) (Spec.GcmSiv.keyLen p.R) (bytesAt σ.mem p.N 12) =
      (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem p.K p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.AArch64

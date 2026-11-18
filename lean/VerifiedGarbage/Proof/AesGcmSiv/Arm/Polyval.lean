module

public import VerifiedGarbage.Proof.Cmac.Block32
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesGcmSiv.Arm
public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Env
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.GcmSiv.Ctr
public import VerifiedGarbage.Proof.GcmSiv.Spec

/-! ### `AesGcmSiv.Arm.Absorb`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.Arm.Keys`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.Arm.Derive`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on ARMv7: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 176` (`derArgs_ok`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_ok`): after the loop, the halves of
`derive_keys` (`derive_ok`, `DInv.keys`).
-/

@[expose] public section

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
  addr_add (by have := L.nw; omega_arith)

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
  rw [ofNat_lsl32, add32_ofNat_assoc, L.wA (by omega_arith)]
  congr 2; omega_arith

/-- The code after the call of a step. -/
theorem derPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (h4 : t.gpr .r4 = BitVec.ofNat 32 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧ t'.mem = postMem t.mem (State.addr p.W) i ∧
      t'.gpr .r4 = BitVec.ofNat 32 (i + 1) ∧ t'.z = decide (i + 1 = p.R / 2 - 1) ∧
      Others [.r0, .r1, .r2, .r4, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have r₀ := E.perm.wR (show 176 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 180 + 4 ≤ 3760 by decide)
  have wo₀ := E.perm.wW (d := 16 + 8 * i) (n := 4) (by omega_arith)
  have wo₁ := E.perm.wW (d := 20 + 8 * i) (n := 4) (by omega_arith)
  have ea₀ := ofNat_lsl3 L (i := i) (k := 16) (by omega_arith)
  have ea₁ := ofNat_lsl3 L (i := i) (k := 20) (by omega_arith)
  refine ⟨_, by simp only [derivePost]; srun [E.r8, E.r11, h4, L.wA, ea₀, ea₁, r₀, r₁, wo₀, wo₁], ?_⟩
  refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, postMem]
  · simp [gpr_setReg, h4, ofNat_add32]
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, z_store, gpr_store, h4, E.r8,
      ofNat_lsr32 L.ofNat_R_lt, ofNat_add32]
    rw [ofNat_sub32 (by rcases hR with h | h <;> rw [h] <;> decide) (by have := L.ofNat_R_lt; omega_arith),
      z_cmp (by have := L.ofNat_R_lt; omega_arith) (by have := L.ofNat_R_lt; omega_arith), Nat.pow_one]
    congr 1; apply propext; omega_arith

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] m (postMem m W i) := by
  have c₀ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (16 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
  have c₁ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (20 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
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
    (L.bk.sub_right (Region.sub_prefix L.rounds_le)) (by have := L.rounds_le; omega_arith) hf]

/-- The arguments of a step's call. -/
theorem derCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) (r0 : t₁.gpr .r0 = p.K)
    (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R) (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112)
    (r3 : t₁.gpr .r3 = p.W + BitVec.ofNat 32 176) (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1)
    (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have ww := L.ww
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, L.kw,
    by rw [L.wN (by decide)]; omega_arith, by rw [L.wN (by decide)]; omega_arith, by rw [L.wN (by decide)]; omega_arith,
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
    rw [add_ofNat_assoc]; congr 2; omega_arith
  have d : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
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
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega_arith
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
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, by omega_arith, ?_, ?_⟩, z₃⟩
  · -- The frame.
    have mem : ∀ {r : Region}, r ∈ derR (State.addr p.W) p.SP → ∃ r' ∈ derR (State.addr p.W) p.SP, Region.Sub r r' :=
      fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact mem (by simp)
    · rw [hm₃]
      exact (postMem_frame _ _ _ (by omega_arith)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · -- The bytes.
    have dW : ∀ {d k : Nat}, d + k ≤ 3760 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨State.addr p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega_arith) (by omega_arith) h₁
    have keep : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (postMem_frame _ _ _ (by omega_arith))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega_arith) (by omega_arith)) (by omega_arith),
        Proof.AesGcm.Arm.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega_arith)
          · exact dW (by decide) (by omega_arith)
          · exact dW (by decide) (by omega_arith)
          · exact (L.bw' (by omega_arith)).symm) (by omega_arith),
        Proof.AesGcm.Arm.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega_arith)) (by omega_arith)]
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
          (by omega_arith)]
      rw [hm₃, postMem_bytes _ _ _ (by omega_arith),
        show bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 8 =
          (bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.K) (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.K) p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega_arith, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
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
  · right; exact ⟨ev.trans (by simp [he]), (p.R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : Prm} (L : Lay p) {σ t : State} (I : DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
        (bytesAt σ.mem (State.addr p.N) 12) =
      (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  have hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 192` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`).
`keys_ok`: the three together.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (hkeyOf)
open VG.Proof.AesGcm.Arm (KeyCall KeyPost key_call below add_ofNat_zero add_ofNat_assoc covers_cons covers_nil
  covers_append' ofNat_sub32 mem_store gpr_store sp_store rd_store wr_store z_store)

/-! ## Blocks stored a word at a time -/

/-- A block stored as four words, read by GHASH. -/
theorem blockAt_store4 (m : Mem) (p : Addr) (a b c d : BitVec 32) :
    Spec.Gcm.blockAt (Proof.Cmac.store4 m p a b c d) p = Proof.Gcm.Arm.w4 (rev a) (rev b) (rev c) (rev d) := by
  have dj : ∀ {x y : Nat}, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 16 → y + 4 ≤ 16 →
      (⟨p + BitVec.ofNat 64 x, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 y, 4⟩ :=
    fun h hx hy => Offset.disjoint p h (by omega_arith) (by omega_arith)
  have d₀ : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by
    simpa using dj (x := 0) (y := 4) (.inl (by decide)) (by decide) (by decide)
  have d₀' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by
    simpa using dj (x := 0) (y := 8) (.inl (by decide)) (by decide) (by decide)
  have d₀'' : (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by
    simpa using dj (x := 0) (y := 12) (.inl (by decide)) (by decide) (by decide)
  rw [Proof.Gcm.Arm.blockAt_rev, Proof.Cmac.store4]
  simp only [Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 8) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 12) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ (dj (x := 8) (y := 4) (.inr (by decide)) (by decide) (by decide)),
    Proof.Cmac.readW_writeW_disj _ d₀.symm, Proof.Cmac.readW_writeW_disj _ d₀'.symm,
    Proof.Cmac.readW_writeW_disj _ d₀''.symm, Mem.readW_writeW_self32]

/-! ## `expand` -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 192`. -/
structure ExpPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩, ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩]
    t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
    Spec.GcmSiv.aes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

theorem keyLen_lsl {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 32 R - BitVec.ofNat 32 6) <<< 2 = BitVec.ofNat 32 (Spec.GcmSiv.keyLen R) := by
  rw [ofNat_sub32 (by omega_arith) (by omega_arith), ofNat_lsl32]
  congr 1; unfold Spec.GcmSiv.keyLen; omega_arith

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa expandArgs t = some t₁ ∧
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 1712)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ ∧ t₁.mem = t.mem := by
  have hl : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    unfold Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h] <;> decide
  have hR := L.rounds
  have ww := L.ww
  refine ⟨_, by simp only [expandArgs]; srun [E.r8, E.r11], ⟨?r0, ?r1, ?r2, ?r3, ?len, ?fK, ?fC, ?fS, ?kc, ?ks, ?cs,
    ?rd, ?wr⟩, E.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by rfl⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E.r11]
  case r1 => simp [gpr_setReg, E.r8, keyLen_lsl hR]
  case r2 => simp [gpr_setReg, E.r11]
  case r3 => simp [gpr_setReg, E.r11]
  case len => omega_arith
  case fK => rw [L.wN (by decide)]; omega_arith
  case fC => rw [L.wN (by decide)]; omega_arith
  case fS => rw [L.wN (by decide)]; omega_arith
  case kc => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  case ks => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  case cs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case rd => rw [L.wA (by decide)]; exact E.perm.wCR (by omega_arith)
  case wr =>
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

theorem expand_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) : WP isa expand t (ExpPost p t) := by
  obtain ⟨t₁, run₁, kc, E₁, hm₁⟩ := expArgs_ok L E
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call kc) fun t₂ P => ?_
  have fr := P.frame
  have out := P.out
  simp only [L.wA (show 32 < 3760 by decide), L.wA (show 192 < 3760 by decide),
    L.wA (show 1712 < 3760 by decide)] at fr out
  refine ⟨E₁.of_saved P.saved P.sp P.rd P.wr, by rw [← hm₁]; exact fr, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) = p.R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; rcases L.rounds with h | h <;> rw [h]
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

/-! ## `hkey` -/

/-- GHASH's key from the words `w₀`–`w₃` of the authentication key, as
`hkey` computes it: its four words, the most significant first. -/
abbrev hk3 (w₀ w₃ : BitVec 32) : BitVec 32 := (w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)
abbrev hkW (lo hi : BitVec 32) : BitVec 32 := (lo >>> 1) ||| (hi <<< 31)

/-- The memory `hkey` leaves. -/
def hkeyMem (m : Mem) (W : Addr) : Mem :=
  let w₀ := m.readW (W + BitVec.ofNat 64 16) 32
  let w₁ := m.readW (W + BitVec.ofNat 64 20) 32
  let w₂ := m.readW (W + BitVec.ofNat 64 24) 32
  let w₃ := m.readW (W + BitVec.ofNat 64 28) 32
  Proof.Cmac.zero4 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 64) (rev (hk3 w₀ w₃)) (rev (hkW w₂ w₃))
    (rev (hkW w₁ w₂)) (rev (hkW w₀ w₁))) (W + BitVec.ofNat 64 80)

theorem hkeyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m (hkeyMem m W) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩).trans
    ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩)

theorem hkeyMem_key (m : Mem) (W : Addr) :
    Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16)) := by
  rw [hkeyMem, Proof.Cmac.zero4, Proof.AesGcm.Arm.blockAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.hkeyOf_words,
    GcmSiv.Words32.ofBytes_bytesAt, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem hkeyMem_acc (m : Mem) (W : Addr) : Spec.Gcm.blockAt (hkeyMem m W) (W + BitVec.ofNat 64 80) = 0 := by
  rw [hkeyMem, Proof.Cmac.zero4, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_zero]
  decide

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧ t'.mem = hkeyMem t.mem (State.addr p.W) ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 16 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 20 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 24 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 28 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 64 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 68 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 72 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 76 + 4 ≤ 3760 by decide)
  have w₄ := E.perm.wW (show 80 + 4 ≤ 3760 by decide)
  have w₅ := E.perm.wW (show 84 + 4 ≤ 3760 by decide)
  have w₆ := E.perm.wW (show 88 + 4 ≤ 3760 by decide)
  have w₇ := E.perm.wW (show 92 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [hkey, Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, w₄,
    w₅, w₆, w₇], ?_, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, hkeyMem, Proof.Cmac.zero4,
    Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  rfl

/-! ## `keys` -/

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule, the working spaces and the
stack below `SP`. -/
abbrev keyR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 192, 3568⟩, below SP]

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (p : Prm) (σ t : State) : Prop where
  env : Env p t
  frame : Frame (keyR (State.addr p.W) p.SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
    (bytesAt σ.mem (State.addr p.N) 12)).1 = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (State.addr p.K) p.R) (Spec.GcmSiv.keyLen p.R)
      (bytesAt σ.mem (State.addr p.N) 12)).2
  hkey : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
    hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0

theorem keys_ok {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) : WP isa keys σ (KeysPost p σ) := by
  have hR := L.rounds
  refine WP.seq (WP.mono (derive_ok L E) fun t₂ I => ?_)
  have k0 : (⟨State.addr p.W + BitVec.ofNat 64 16, 112⟩ : Region) ∈ keyR (State.addr p.W) p.SP := List.mem_cons_self
  have k1 : (⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region) ∈ keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have k2 : (⟨State.addr p.W + BitVec.ofNat 64 192, 3568⟩ : Region) ∈ keyR (State.addr p.W) p.SP :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have k3 : below p.SP ∈ keyR (State.addr p.W) p.SP := by simp
  have f₂ : Frame (keyR (State.addr p.W) p.SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k1, fun _ h => h⟩
    · exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, k3, fun _ h => h⟩
  refine WP.seq (WP.mono (expand_ok L I.env) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hm₄, ho₄, sp₄, rd₄, wr₄⟩ := hkey_ok L X.env
  have dK : ∀ {d k : Nat}, d + k ≤ 64 → 16 ≤ d → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 512⟩],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  have f₃ : Frame (keyR (State.addr p.W) p.SP) t₂.mem t₃.mem := X.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, k2, Offset.sub _ (by decide) (by decide)⟩
  have f₄ : Frame (keyR (State.addr p.W) p.SP) t₃.mem t₄.mem := by
    rw [hm₄]; exact (hkeyMem_frame _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, k0, Offset.sub _ (by decide) (by decide)⟩
  have dH : ∀ {d k : Nat}, d + k ≤ 64 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl h) (by omega_arith) (by decide)
  have dH' : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 64, 32⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  have keys := I.keys L
  have a₃ : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame X.frame (dK (by decide) (by decide)) (by decide)
  have a₄ : bytesAt t₄.mem (State.addr p.W + BitVec.ofNat 64 16) 16 =
      bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 16) 16 := by
    rw [hm₄]; exact Proof.AesGcm.Arm.bytesAt_frame (hkeyMem_frame _ _) (dH (by decide)) (by decide)
  refine WP.of_runBlock ⟨t₄, run₄, X.env.of_others ho₄ sp₄ rd₄ wr₄, (f₂.trans f₃).trans f₄, ?_, ?_, ?_, ?_⟩
  · rw [keys, a₄, a₃]
  · have hk := keys
    rw [Prod.ext_iff] at hk
    rw [hk.2, ← X.ciph]
    unfold Spec.GcmSiv.ctxCiph
    rw [hm₄, Proof.AesGcm.Arm.bytesAt_frame (hkeyMem_frame _ _) (fun r hr =>
      (dH' r hr).sub_left (Region.sub_prefix L.rounds_le)) (by omega_arith)]
  · rw [hm₄, hkeyMem_key, ← hm₄, a₄]
  · rw [hm₄]; exact hkeyMem_acc _ _

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: POLYVAL (`chunk`)

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the
key `H · x` on the same bits (`Proof.GcmSiv.Polyval`): `revLoop` copies up
to 64 blocks to `W + 432` with the bytes of each reversed, so that GHASH
reads each copy as POLYVAL reads the original (`revLoop_ok`), and `vg_ghash`
absorbs them (`chunk_ok`); chunks follow each other until fewer than 16
bytes are left (`chunks_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall GhPost gh_call below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc covers_cons
  covers_nil covers_append' covers_off covers_prefix eval_ne' eval_eq' z_cmp ofNat_sub32 ofNat_add32 toNat32
  mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

/-! ## Reversing blocks -/

/-- The body of `revLoop`. -/
abbrev revBody : List Instr :=
  [.ldr .r0 .r4 12, .ldr .r1 .r4 8, .ldr .r12 .r4 4, .ldr .lr .r4 0, .rev .r0 .r0, .rev .r1 .r1,
    .rev .r12 .r12, .rev .lr .lr, .str .r0 .r2 0, .str .r1 .r2 4, .str .r12 .r2 8, .str .lr .r2 12,
    Impl.AesGcm.Arm.addI .r4 .r4 16, Impl.AesGcm.Arm.addI .r2 .r2 16, .subs .r3 .r3 (Impl.AesGcm.Arm.imm 1)]

/-- The registers `revLoop` writes. -/
abbrev revRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12, .lr]

/-- What one step of `revLoop` stores: the words of the block at `S` in the
other order, each reversed. -/
def revMem (m : Mem) (S P : Addr) : Mem :=
  Proof.Cmac.store4 m P (rev (m.readW (S + BitVec.ofNat 64 12) 32)) (rev (m.readW (S + BitVec.ofNat 64 8) 32))
    (rev (m.readW (S + BitVec.ofNat 64 4) 32)) (rev (m.readW S 32))

theorem revStep_ok {t : State} {S P : BitVec 32} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (hS : ∀ o, o < 16 → State.addr (S + BitVec.ofNat 32 o) = State.addr S + BitVec.ofNat 64 o)
    (hP : ∀ o, o < 16 → State.addr (P + BitVec.ofNat 32 o) = State.addr P + BitVec.ofNat 64 o)
    (h4 : t.gpr .r4 = S) (h2 : t.gpr .r2 = P) (h3 : t.gpr .r3 = BitVec.ofNat 32 (j + 1))
    (hr : Covers [⟨State.addr S, 16⟩] (t.rd ++ t.wr)) (hw : Covers [⟨State.addr P, 16⟩] t.wr) :
    ∃ t' : State, runBlock isa revBody t = some t' ∧ t'.mem = revMem t.mem (State.addr S) (State.addr P) ∧
      t'.gpr .r4 = S + BitVec.ofNat 32 16 ∧ t'.gpr .r2 = P + BitVec.ofNat 32 16 ∧
      t'.gpr .r3 = BitVec.ofNat 32 j ∧ t'.z = decide (j = 0) ∧ Others revRegs t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain r₀ : InRegions (t.rd ++ t.wr) (State.addr S) 4 := by simpa using in_off hr (d := 0) (n := 4) (by decide) (by decide)
  obtain r₄ := in_off hr (d := 4) (n := 4) (by decide) (by decide)
  obtain r₈ := in_off hr (d := 8) (n := 4) (by decide) (by decide)
  obtain r₁₂ := in_off hr (d := 12) (n := 4) (by decide) (by decide)
  obtain w₀ : InRegions t.wr (State.addr P) 4 := by simpa using in_off hw (d := 0) (n := 4) (by decide) (by decide)
  obtain w₄ := in_off hw (d := 4) (n := 4) (by decide) (by decide)
  obtain w₈ := in_off hw (d := 8) (n := 4) (by decide) (by decide)
  obtain w₁₂ := in_off hw (d := 12) (n := 4) (by decide) (by decide)
  refine ⟨_, by srun [h4, h2, h3, add_ofNat_zero, hS, hP, r₀, r₄, r₈, r₁₂, w₀, w₄, w₈, w₁₂], ?_⟩
  refine ⟨?_, by simp [gpr_setReg, h4], by simp [gpr_setReg, h2], ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, revMem,
      Proof.Cmac.store4]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h3]
    rw [ofNat_sub32 (by omega_arith) (by omega_arith)]; rfl
  · simp only [z_setReg, z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h3]
    rw [z_cmp (by omega_arith) (by decide)]
    congr 1; apply propext; omega_arith
where
  in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k) (hk : k < 2 ^ 64) :
      InRegions rs (p + BitVec.ofNat 64 d) n := Proof.AesGcm.Arm.in_off h hd hk

theorem blocksAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Gcm.blocksAt m p (j + 1) = Spec.Gcm.blocksAt m p j ++ [Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * j))] := by
  simp [Spec.Gcm.blocksAt, List.range_succ]

/-- The block `revMem` stores, as GHASH reads it: POLYVAL's field element of
the source. -/
theorem revMem_block (m : Mem) (S P : Addr) :
    Spec.Gcm.blockAt (revMem m S P) P = Spec.GcmSiv.ofBytes (bytesAt m S 16) := by
  rw [revMem, blockAt_store4, rev_rev, rev_rev, rev_rev, rev_rev, Proof.Gcm.Arm.w4, GcmSiv.Words32.ofBytes_bytesAt]

/-- POLYVAL's field elements of the `k` blocks at `Q`. -/
abbrev elemsAt (m : Mem) (Q : Addr) (k : Nat) : List Spec.GcmSiv.Elem :=
  (List.range k).map fun i => Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * i)) 16)

/-- What a chunk may read: `k` bytes at `Q` apart from what it writes. -/
structure Src (p : Prm) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨State.addr Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  y : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩
  rev : (⟨State.addr Q, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 432, 1280⟩
  stk : (below p.SP).Disjoint ⟨State.addr Q, k⟩

namespace Src

variable {p : Prm} {s : State} {Q : BitVec 32} {n : Nat} (h : Src p s Q n)
include h

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega_arith

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src p s' Q n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem addr {j : Nat} (hj : j < n) : State.addr (Q + BitVec.ofNat 32 j) = State.addr Q + BitVec.ofNat 64 j :=
  addr_add (by have := h.wrap; omega_arith)

theorem toNat_add {j : Nat} (hj : j < n) : (Q + BitVec.ofNat 32 j).toNat = Q.toNat + j := by
  have := h.wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Src p s Q k where
  rd := covers_prefix h.rd hk
  wrap := by have := h.wrap; omega_arith
  y := h.y.sub_left (Region.sub_prefix hk)
  rev := h.rev.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`, for `a < n`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) (ha : a < n) : Src p s (Q + BitVec.ofNat 32 a) k := by
  obtain e := h.addr ha
  obtain hs : Region.Sub ⟨State.addr Q + BitVec.ofNat 64 a, k⟩ ⟨State.addr Q, n⟩ := Offset.sub_base _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact covers_off h.rd hk h.lt
  · rw [h.toNat_add ha]; have := h.wrap; omega_arith
  · rw [e]; exact h.y.sub_left hs
  · rw [e]; exact h.rev.sub_left hs
  · rw [e]; exact h.stk.sub_right hs

end Src

/-- What `revLoop` leaves after `j` blocks, from `t₀`. -/
structure RInv (p : Prm) (Q : BitVec 32) (c j : Nat) (t₀ t : State) : Prop where
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * j)
  r2 : t.gpr .r2 = p.W + BitVec.ofNat 32 (432 + 16 * j)
  r3 : t.gpr .r3 = BitVec.ofNat 32 (c - j)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem
  out : Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) j = elemsAt t₀.mem (State.addr Q) j
  others : Others revRegs t₀ t
  sp : t.sp = t₀.sp
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr

/-- `revLoop`: `c` blocks at `Q` copied to `W + 432`, each reversed, so that
GHASH reads POLYVAL's field elements of them. -/
theorem revLoop_ok {p : Prm} (L : Lay p) {t₀ : State} (E : Env p t₀) {Q : BitVec 32} {c : Nat}
    (hc1 : 1 ≤ c) (hc : c ≤ 64) (hQ : Src p t₀ Q (16 * c)) (h4 : t₀.gpr .r4 = Q)
    (h2 : t₀.gpr .r2 = p.W + BitVec.ofNat 32 432) (h3 : t₀.gpr .r3 = BitVec.ofNat 32 c) :
    WP isa revLoop t₀ fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * c⟩] t₀.mem t.mem ∧
      Spec.Gcm.blocksAt t.mem (State.addr p.W + BitVec.ofNat 64 432) c = elemsAt t₀.mem (State.addr Q) c ∧
      t.gpr .r4 = Q + BitVec.ofNat 32 (16 * c) ∧
      Others revRegs t₀ t ∧ t.sp = t₀.sp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr := by
  have hw := L.ww
  obtain I₀ : RInv p Q c 0 t₀ t₀ := ⟨by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h2],
    by rw [h3, Nat.sub_zero], Frame.refl _ _, by simp only [Spec.Gcm.blocksAt, elemsAt, List.range_zero, List.map_nil],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.loop (M := isa) (body := .block revBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = c - j ∧ j < c ∧ RInv p Q c j t₀ t) ?_ (c - 0) t₀ ⟨0, rfl, hc1, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  obtain eS : State.addr (Q + BitVec.ofNat 32 (16 * j)) = State.addr Q + BitVec.ofNat 64 (16 * j) :=
    hQ.addr (by omega_arith)
  obtain hS : ∀ o, o < 16 → State.addr (Q + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 o) =
      State.addr (Q + BitVec.ofNat 32 (16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, hQ.addr (by omega_arith), eS, add_ofNat_assoc]
  obtain hP : ∀ o, o < 16 → State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j) + BitVec.ofNat 32 o) =
      State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)) + BitVec.ofNat 64 o := fun o ho => by
    rw [add32_ofNat_assoc, L.wA (by omega_arith), L.wA (by omega_arith), add_ofNat_assoc]
  obtain hr : Covers [⟨State.addr (Q + BitVec.ofNat 32 (16 * j)), 16⟩] (t.rd ++ t.wr) := by
    rw [I.rd, I.wr, eS]; exact covers_off hQ.rd (by omega_arith) hQ.lt
  obtain hwr : Covers [⟨State.addr (p.W + BitVec.ofNat 32 (432 + 16 * j)), 16⟩] t.wr := by
    rw [I.wr, L.wA (by omega_arith)]; exact E.perm.wC (by omega_arith)
  obtain ⟨t', run', hm', r4', r2', r3', z', ho', sp', rd', wr'⟩ :=
    revStep_ok (j := c - j - 1) (by omega_arith) hS hP I.r4 I.r2 (by rw [I.r3]; congr 1; omega_arith) hr hwr
  refine WP.of_runBlock ⟨t', run', ?_⟩
  rw [eS, L.wA (by omega_arith)] at hm'
  -- The source is outside the copies.
  obtain src : bytesAt t.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 =
      bytesAt t₀.mem (State.addr Q + BitVec.ofNat 64 (16 * j)) 16 :=
    Proof.AesGcm.Arm.bytesAt_frame I.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hQ.rev.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub _ (by omega_arith) (by omega_arith)))
      (by decide)
  obtain fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 (432 + 16 * j), 16⟩] t.mem t'.mem := by
    rw [hm', revMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain I' : RInv p Q c (j + 1) t₀ t' := by
    refine ⟨by rw [r4', add32_ofNat_assoc, Nat.mul_succ], by rw [r2', add32_ofNat_assoc, Nat.mul_succ, Nat.add_assoc],
      by rw [r3', Nat.sub_sub], ?_, ?_, fun r hr => by rw [ho' r hr, I.others r hr],
      by rw [sp', I.sp], by rw [rd', I.rd], by rw [wr', I.wr]⟩
    · exact I.frame.trans (fr.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_arith) (by omega_arith)⟩)
    · rw [blocksAt_succ, Proof.AesGcm.Arm.blocksAt_frame fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), I.out]
      simp only [elemsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [add_ofNat_assoc, hm', revMem_block, src]
  obtain ev := eval_ne' z'
  by_cases he : j + 1 = c
  · left
    refine ⟨ev.trans (by simp [show c - j - 1 = 0 by omega_arith]), ?_⟩
    exact ⟨I'.frame, he ▸ I'.out, he ▸ I'.r4, I'.others, I'.sp, I'.rd, I'.wr⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩


/-! ## A chunk -/

/-- What a chunk writes: GHASH's accumulator, the reversed blocks,
`vg_ghash`'s working space and the stack below `SP`. -/
abbrev absR (W : Addr) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 432, 1280⟩, below SP]

/-- What a chunk leaves, from `t`, after absorbing `k` blocks of the `m`
bytes at `Q`. -/
structure ChunkPost (p : Prm) (Q : BitVec 32) (m k : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  z : t'.z = decide ((m - 16 * k) / 16 = 0)
  frame : Frame (absR (State.addr p.W) p.SP) t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) (elemsAt t.mem (State.addr Q) k)

/-- `chunkLen`: the number of blocks of the chunk. -/
theorem chunkLen_ok {t : State} {m : Nat} (hm : m < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkLen t fun t' => t'.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      Others [.r6] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, run₁, r6₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.mov .r6 (.shifted .r5 .lsr 10), .cmp .r6 (Impl.AesGcm.Arm.imm 0)] t = some t₁ ∧
      t₁.gpr .r6 = BitVec.ofNat 32 (m / 1024) ∧ t₁.z = decide (m / 1024 = 0) ∧ Others [.r6] t t₁ ∧
      t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h5], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, ofNat_lsr32 hm]
    · simp only [z_subFlags, gpr_setReg, ite_true, ofNat_lsr32 hm]
      rw [z_cmp (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (m / 1024 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 1024 = 0 := by simpa using ht
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true, ho₁ .r5 (by decide), h5, ofNat_lsr32 hm]
      congr 1; omega_arith
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)
  · have h0 : m / 1024 ≠ 0 := by simpa using hf
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t' ht' => ?_
    subst ht'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_setReg, ite_true]
      congr 1; omega_arith
    · simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false]; exact ho₁ r (by simpa using hr)

/-- A chunk up to its call: up to 64 blocks reversed at `W + 432`, the
pointer and the count past them, and the arguments of `vg_ghash`. -/
structure ChunkPre (p : Prm) (Q : BitVec 32) (m k : Nat) (t t₅ : State) : Prop where
  call : GhCall t₅ (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 432)
    (p.W + BitVec.ofNat 32 1456) k
  env : Env p t₅
  rd : t₅.rd = t.rd
  wr : t₅.wr = t.wr
  r4 : t₅.gpr .r4 = Q + BitVec.ofNat 32 (16 * k)
  r5 : t₅.gpr .r5 = BitVec.ofNat 32 (m - 16 * k)
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 432, 16 * k⟩] t.mem t₅.mem
  out : Spec.Gcm.blocksAt t₅.mem (State.addr p.W + BitVec.ofNat 64 432) k = elemsAt t.mem (State.addr Q) k

/-- The pieces of a chunk before its call. -/
theorem chunkPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunkPre t (ChunkPre p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (chunkLen_ok hm h5) fun t₁ ⟨r6₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨t₂, run₂, r2₂, r3₂, ho₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ t₂, runBlock isa
      [Impl.AesGcm.Arm.addI .r2 .r11 revO, .mov .r3 (.reg .r6)] t₁ = some t₂ ∧
      t₂.gpr .r2 = p.W + BitVec.ofNat 32 432 ∧ t₂.gpr .r3 = BitVec.ofNat 32 (min (m / 16) 64) ∧
      Others [.r2, .r3] t₁ t₂ ∧ t₂.mem = t₁.mem ∧ t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    refine ⟨_, by srun [], ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, ho₁ .r11 (by decide), E.r11]
    · simp [gpr_setReg, r6₁]
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  obtain E₂ : Env p t₂ := (E.of_others ho₁ sp₁ rd₁ wr₁).of_others ho₂ sp₂ rd₂ wr₂
  obtain hk1 : 1 ≤ min (m / 16) 64 := by omega_arith
  obtain hQ₂ : Src p t₂ Q (16 * min (m / 16) 64) :=
    (hQ.take (by omega_arith)).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain h4₂ : t₂.gpr .r4 = Q := by rw [ho₂ _ (by decide), ho₁ _ (by decide), h4]
  refine WP.seq (WP.mono (revLoop_ok L E₂ hk1 (by omega_arith) hQ₂ h4₂ r2₂ r3₂)
    fun t₃ ⟨fr₃, out₃, r4₃, ho₃, sp₃, rd₃, wr₃⟩ => ?_)
  obtain E₃ : Env p t₃ := E₂.of_others ho₃ sp₃ rd₃ wr₃
  obtain r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (min (m / 16) 64) := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), r6₁]
  obtain r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 m := by
    rw [ho₃ _ (by decide), ho₂ _ (by decide), ho₁ _ (by decide), h5]
  obtain m₂₁ : t₂.mem = t.mem := by rw [m₂, m₁]
  rw [m₂₁] at fr₃ out₃
  refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [chunkArgs]; srun [], rfl⟩ fun t₄ ht₄ => ?_
  subst ht₄
  refine ⟨⟨?r0, ?r1, ?r2, ?r3, ?r12, ?hsp, ?fH, ?fY, ?fD, ?fS, ?hy, ?hs, ?yd, ?ys, ?ds, ?bh, ?bY, ?bd, ?bs,
      ?reads, ?writes⟩,
    E₃.keep (fun r hr => ?regs) (by rfl) (by rfl) (by rfl), by simp only [rd_setReg]; rw [rd₃, rd₂, rd₁],
    by simp only [wr_setReg]; rw [wr₃, wr₂, wr₁], ?_, ?_, by simp only [mem_setReg]; exact fr₃,
    by simp only [mem_setReg]; exact out₃⟩
  case regs =>
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  case r0 => simp [gpr_setReg, E₃.r11]
  case r1 => simp [gpr_setReg, E₃.r11]
  case r2 => simp [gpr_setReg, E₃.r11]
  case r3 => simp [gpr_setReg, r6₃]
  case r12 => simp [gpr_setReg, E₃.r11]
  case hsp => simp only [sp_setReg]; rw [E₃.sp]; exact L.sp8
  case fH => rw [L.wN (by decide)]; omega_arith
  case fY => rw [L.wN (by decide)]; omega_arith
  case fD => rw [L.wN (by decide)]; omega_arith
  case fS => rw [L.wN (by decide)]; omega_arith
  case hy => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case hs => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case yd => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  case ys => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  case ds => rw [L.wA (by decide), L.wA (by decide)]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  case bh => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bY => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case bd => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by omega_arith)
  case bs => simp only [sp_setReg]; rw [E₃.sp, L.wA (by decide)]; exact L.bw' (by decide)
  case reads =>
    simp only [rd_setReg, wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_append' (covers_cons (E₃.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₃.perm.wCR (by omega_arith)) covers_nil)
  case writes =>
    simp only [wr_setReg]
    rw [L.wA (by decide), L.wA (by decide)]
    exact covers_cons (E₃.perm.wC (by decide)) (covers_cons (E₃.perm.wC (by decide)) covers_nil)
  · simp [gpr_setReg, r4₃]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, r5₃, r6₃, ofNat_lsl32]
    rw [ofNat_sub32 (by omega_arith) hm]; congr 2; omega_arith


/-- `wholeLeft`: `Z` set iff fewer than 16 of the `r` bytes are left. -/
theorem wholeLeft_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    ∃ t' : State, runBlock isa wholeLeft t = some t' ∧ t'.z = decide (r / 16 = 0) ∧ Others [.r12] t t' ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by simp only [wholeLeft]; srun [h5], ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, ofNat_lsr32 hr]
  rw [z_cmp (by omega_arith) (by decide)]

theorem chunk_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa chunk t (ChunkPost p Q m (min (m / 16) 64) t) := by
  have hw := L.ww
  obtain hk : 16 * min (m / 16) 64 ≤ 1024 := by omega_arith
  refine WP.seq (WP.mono (chunkPre_ok L E hm h16 hQ h4 h5) fun t₅ Pr => ?_)
  refine WP.seq (WP.mono (gh_call Pr.call) fun t₆ P => ?_)
  obtain E₆ : Env p t₆ := Pr.env.of_saved P.saved P.sp P.rd P.wr
  obtain r5₆ : t₆.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) := by
    rw [P.saved _ (by decide) (by decide), Pr.r5]
  have fr := P.frame
  have out₆ := P.out
  simp only [L.wA (show 64 < 3760 by decide), L.wA (show 80 < 3760 by decide),
    L.wA (show 432 < 3760 by decide), L.wA (show 1456 < 3760 by decide), Pr.env.sp] at fr out₆
  obtain dH : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  obtain dY : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 432, 16 * min (m / 16) 64⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 80, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  rw [Proof.AesGcm.Arm.blockAt_frame Pr.frame dH, Proof.AesGcm.Arm.blockAt_frame Pr.frame dY, Pr.out] at out₆
  obtain ⟨t₇, run₇, z₇, ho₇, m₇, sp₇, rd₇, wr₇⟩ := wholeLeft_ok (by omega_arith) r5₆
  refine WP.of_runBlock ⟨t₇, run₇, E₆.of_others ho₇ sp₇ rd₇ wr₇, by rw [rd₇, P.rd, Pr.rd],
    by rw [wr₇, P.wr, Pr.wr], ?_, by rw [ho₇ _ (by decide), r5₆], z₇, ?_, by rw [m₇]; exact out₆⟩
  · rw [ho₇ _ (by decide), P.saved _ (by decide) (by decide), Pr.r4]
  · rw [m₇]
    refine (Pr.frame.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-! ## Absorbing -/

theorem elemsAt_add (m : Mem) (Q : Addr) (d k : Nat) :
    elemsAt m Q (d + k) = elemsAt m Q d ++ elemsAt m (Q + BitVec.ofNat 64 (16 * d)) k := by
  simp only [elemsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, add_ofNat_assoc, Nat.mul_add]

theorem elemsAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨Q, 16 * k⟩ : Region).Disjoint r) (hk : 16 * k ≤ 2 ^ 64) : elemsAt m' Q k = elemsAt m Q k := by
  unfold elemsAt
  rw [← GcmSiv.elems_bytesAt, ← GcmSiv.elems_bytesAt, Proof.AesGcm.Arm.bytesAt_frame hf hd hk]

/-- What absorbing writes: what a chunk writes, and the block at `W + 176`. -/
abbrev absorbR (W : Addr) (SP : BitVec 32) : List Region := ⟨W + BitVec.ofNat 64 176, 16⟩ :: absR W SP

/-- What absorbing leaves, from `t`, having absorbed the elements `xs` and
written only `rs`. -/
structure Absorbed (p : Prm) (rs : List Region) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame rs t.mem t'.mem
  out : Spec.Gcm.blockAt t'.mem (State.addr p.W + BitVec.ofNat 64 80) =
    Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64))
      (Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80)) xs

/-- What absorbing a string leaves. -/
abbrev AbsPost (p : Prm) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop :=
  Absorbed p (absorbR (State.addr p.W) p.SP) xs t t'

theorem absorbR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absorbR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm

/-- A buffer apart from `W` and the stack below `SP` misses what absorbing writes. -/
theorem absorbR_buf {p : Prm} {P : Addr} {k : Nat} (hd : (⟨P, k⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩)
    (hb : (below p.SP).Disjoint ⟨P, k⟩) : ∀ r ∈ absorbR (State.addr p.W) p.SP, (⟨P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hd.sub_right (Lay.wSub (by decide))
  · exact hb.symm

theorem absR_sub (W : Addr) (SP : BitVec 32) : ∀ r ∈ absR W SP, ∃ r' ∈ absorbR W SP, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem Absorbed.trans {p : Prm} {rs : List Region} {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (hH : ∀ r ∈ rs, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r)
    (h₁ : Absorbed p rs xs t t₁) (h₂ : Absorbed p rs ys t₁ t₂) : Absorbed p rs (xs ++ ys) t t₂ := by
  refine ⟨h₂.env, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame, ?_⟩
  rw [h₂.out, h₁.out, Proof.AesGcm.Arm.blockAt_frame h₁.frame hH, Proof.Gcm.ghashFrom_append]

theorem Absorbed.sub {p : Prm} {rs rs' : List Region} {xs : List Spec.GcmSiv.Elem} {t t' : State}
    (h : Absorbed p rs xs t t') (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Absorbed p rs' xs t t' :=
  ⟨h.env, h.rd, h.wr, h.frame.sub hs, h.out⟩

theorem AbsPost.trans {p : Prm} (L : Lay p) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost p xs t t₁) (h₂ : AbsPost p ys t₁ t₂) : AbsPost p (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

theorem Absorbed.of_chunk {p : Prm} {Q : BitVec 32} {m k : Nat} {t t' : State}
    (h : ChunkPost p Q m k t t') : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) k) t t' :=
  ⟨h.env, h.rd, h.wr, h.frame, h.out⟩

theorem Absorbed.of_eq {p : Prm} {rs : List Region} {xs : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h : Absorbed p rs xs t₁ t₂) (hm : t₁.mem = t.mem) (hrd : t₁.rd = t.rd) (hwr : t₁.wr = t.wr) :
    Absorbed p rs xs t t₂ :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, hm ▸ h.frame, by rw [h.out, hm]⟩

theorem absR_H {p : Prm} (L : Lay p) :
    ∀ r ∈ absR (State.addr p.W) p.SP, (⟨State.addr p.W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r :=
  fun r hr => absorbR_H L r (List.mem_cons_of_mem _ hr)

/-- The chunks of the `m` bytes at `Q`, from `σ`, after `d` blocks. -/
structure CInv (p : Prm) (σ : State) (Q : BitVec 32) (m d : Nat) (t : State) : Prop where
  abs : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt σ.mem (State.addr Q) d) σ t
  r4 : t.gpr .r4 = Q + BitVec.ofNat 32 (16 * d)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - 16 * d)

theorem CInv.src {p : Prm} {σ t : State} {Q : BitVec 32} {m d : Nat} (I : CInv p σ Q m d t)
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) :
    Src p t (Q + BitVec.ofNat 32 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
  (hQ.slice (by omega_arith) (by omega_arith)).of_eq I.abs.rd I.abs.wr

theorem CInv.zero {p : Prm} {σ : State} (E : Env p σ) {Q : BitVec 32} {m : Nat} (h4 : σ.gpr .r4 = Q)
    (h5 : σ.gpr .r5 = BitVec.ofNat 32 m) : CInv p σ Q m 0 σ :=
  ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
    by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero]⟩

/-- A chunk, in the chunks. -/
theorem CInv.step {p : Prm} (L : Lay p) {σ t t' : State} {Q : BitVec 32} {m d : Nat}
    (hQ : Src p σ Q (16 * (m / 16))) (hd : d < m / 16) (I : CInv p σ Q m d t)
    (C : ChunkPost p (Q + BitVec.ofNat 32 (16 * d)) (m - 16 * d) (min ((m - 16 * d) / 16) 64) t t') :
    CInv p σ Q m (d + min (m / 16 - d) 64) t' ∧
      t'.z = decide (m / 16 - (d + min (m / 16 - d) 64) = 0) := by
  obtain hk : min ((m - 16 * d) / 16) 64 = min (m / 16 - d) 64 := by congr 1; omega_arith
  rw [hk] at C
  obtain hs := hQ.slice (a := 16 * d) (k := 16 * min (m / 16 - d) 64) (by omega_arith) (by omega_arith)
  obtain ea := hQ.addr (j := 16 * d) (by omega_arith)
  obtain C' := Absorbed.of_chunk C
  rw [elemsAt_frame I.abs.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.y
      · exact hs.rev
      · exact hs.stk.symm) (by omega_arith), ea] at C'
  refine ⟨⟨by rw [elemsAt_add]; exact Absorbed.trans (absR_H L) I.abs C', by rw [C.r4, add32_ofNat_assoc, Nat.mul_add],
    by rw [C.r5]; congr 1; omega_arith⟩, by rw [C.z]; congr 1; apply propext; omega_arith⟩

/-- The whole blocks: chunks until fewer than 16 bytes are left. -/
theorem chunks_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ : Src p t Q (16 * (m / 16))) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa (.loop chunk .ne) t fun t' =>
      Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t' ∧
      t'.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.loop (M := isa) (body := chunk) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p t Q m d t') ?_
    (m / 16 - 0) t ⟨0, rfl, by omega_arith, CInv.zero E h4 h5⟩
  rintro k t' ⟨d, rfl, hd, I⟩
  refine WP.mono (chunk_ok L I.abs.env (by omega_arith) (by omega_arith) (I.src hQ hd) I.r4 I.r5) fun t'' C => ?_
  obtain ⟨I', z⟩ := I.step L hQ hd C
  obtain ev := eval_ne' z
  by_cases he : d + min (m / 16 - d) 64 = m / 16
  · left
    refine ⟨ev.trans (by simp; omega_arith), he ▸ I'.abs, by rw [I'.r4, he], by rw [I'.r5, he]; congr 1; omega_arith⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), m / 16 - (d + min (m / 16 - d) 64), by omega_arith, d + min (m / 16 - d) 64, rfl,
      by omega_arith, I'⟩

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 176` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the stack arguments `aad_len` and `len`; `tagIn` turns
POLYVAL's result into the tag input (`tagIn_ok`). `polyval_ok`: the tag
input of RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.Arm (below add_ofNat_zero add_ofNat_assoc add32_ofNat_assoc covers_left covers_prefix
  covers_off eval_eq' z_cmp ofNat_sub32 ofNat_add32 toNat32 mem_store gpr_store sp_store rd_store wr_store z_store
  mem_subFlags z_subFlags gpr_subFlags sp_subFlags rd_subFlags wr_subFlags LoopPre LoopOut copyLoop_ok
  length_bytesAt)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero4 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  obtain hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.Arm.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega_arith, Proof.AesGcm.Arm.bytesAt_add,
    Proof.AesGcm.Arm.bytesAt_writeBytes_self _ _ _ (by omega_arith),
    Proof.AesGcm.Arm.bytesAt_frame (Proof.AesGcm.Arm.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega_arith)) (by omega_arith)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The block at `W + 176` as a chunk's source. -/
theorem srcB {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s (p.W + BitVec.ofNat 32 176) 16 := by
  have ww := L.ww
  refine ⟨?_, by rw [L.wN (by decide)]; omega_arith, ?_, ?_, ?_⟩ <;> rw [L.wA (by decide)]
  · exact P.wCR (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.bw' (by decide)

/-- One chunk of the 16 bytes at `W + 176`: their field element absorbed. -/
theorem chunkB_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (h4 : t.gpr .r4 = p.W + BitVec.ofNat 32 176) (h5 : t.gpr .r5 = BitVec.ofNat 32 16) :
    WP isa chunk t (Absorbed p (absR (State.addr p.W) p.SP)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 176) 16)] t) :=
  WP.mono (chunk_ok L E (m := 16) (by decide) (by decide) (srcB L E.perm) h4 h5) fun t' C => by
    obtain A := Absorbed.of_chunk C
    simpa [elemsAt, L.wA (show 176 < 3760 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 176`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  r4 : t₃.gpr .r4 = p.W + BitVec.ofNat 32 176
  r5 : t₃.gpr .r5 = BitVec.ofNat 32 16
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 176) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTailPre t (TailPre p (State.addr P) r t) := by
  have hw := L.ww
  obtain w₀ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, r1₁, r2₁, r3₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (Impl.AesGcm.Arm.zero16 bO ++ ([.mov .r1 (.reg .r4), Impl.AesGcm.Arm.addI .r2 .r11 bO,
        .mov .r3 (.reg .r5)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (State.addr p.W + BitVec.ofNat 64 176) ∧ t₁.gpr .r1 = P ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r3 = BitVec.ofNat 32 r ∧ Others [.r0, .r1, .r2, .r3] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · simp [gpr_setReg, h4]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg, h5]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain dB : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr (p.W + BitVec.ofNat 32 176), r⟩ := by
    rw [L.wA (by decide)]
    exact (hd.sub_right (Lay.wSub (show 176 + 16 ≤ 3760 by decide))).sub_right (Region.sub_prefix (by omega_arith))
  obtain lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 176) r :=
    ⟨r1₁, r2₁, r3₁, by omega_arith, by omega_arith, hf, by rw [L.wN (by decide)]; omega_arith, by rw [rd₁, wr₁]; exact hc,
      by rw [L.wA (by decide)]; exact covers_prefix (E₁.perm.wC (show 176 + 16 ≤ 3760 by decide)) (by omega_arith), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, O⟩ => ?_)
  obtain E₂ : Env p t₂ := E₁.keep (fun q hq => O.other q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide)) O.sp O.rd O.wr
  rw [L.wA (by decide)] at hm₂
  -- The data is outside the zeroed block.
  obtain hd₁ : bytesAt t₁.mem (State.addr P) r = bytesAt t.mem (State.addr P) r := by
    rw [hm₁]
    exact Proof.AesGcm.Arm.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  obtain hb₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
      bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    obtain hl := length_bytesAt t.mem (State.addr P) r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega_arith), hl]
  obtain f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).trans
      ((Proof.AesGcm.Arm.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    by simp only [rd_setReg]; rw [O.rd, rd₁], by simp only [wr_setReg]; rw [O.wr, wr₁],
    by simp [gpr_setReg, E₂.r11], by simp [gpr_setReg],
    by simp only [mem_setReg]; exact f₂, by simp only [mem_setReg]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTail t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hf hd h4 h5) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok L T.env T.r4 T.r5) fun t₄ C => ?_
  rw [T.bytes] at C
  obtain dHY : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region)], ∀ d, d + 16 ≤ 176 →
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.Arm.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    Proof.AesGcm.Arm.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]


/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  obtain hs := Proof.AesGcm.Arm.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at hs
  obtain hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `Z` says whether there are any. -/
theorem absMid_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m)
    (hz : t.z = decide (m / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop chunk .ne)) t fun t₂ =>
      Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t₂ ∧
        t₂.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t₂.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h4, h0, Nat.mul_zero, add_ofNat_zero], by rw [h5]; congr 1; omega_arith⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok L E hm (by omega_arith) (hQ.take (by omega_arith)) h4 h5

theorem absorb_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ : Src p t Q m) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa absorb t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (State.addr Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ := wholeLeft_ok hm h5
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (absMid_ok L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h4])
    (by rw [ho₁ _ (by decide), h5]) z₁) fun t₂ ⟨P₂, r4₂, r5₂⟩ => ?_)
  rw [m₁] at P₂
  obtain P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (m % 16 = 0) ∧ Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain P₃ : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t₃ :=
    ⟨P₂'.env.of_others ho₃ sp₃ rd₃ wr₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (absR_sub _ _))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    obtain hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)
    obtain ea := hQ.addr (j := 16 * (m / 16)) (by omega_arith)
    obtain dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
        ⟨State.addr p.W, 3760⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega_arith))
    refine WP.mono (absTail_ok L P₃.env (by omega_arith) (by omega_arith) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [ho₃ _ (by simp), r4₂]) (by rw [ho₃ _ (by simp), r5₂])) fun t₄ T => ?_
    obtain e := Proof.AesGcm.Arm.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega_arith)
    rw [e, ea] at T
    exact AbsPost.trans L (P₃.sub (absR_sub _ _)) T


/-! ## The lengths, and the tag input -/

/-- The stack arguments are apart from what absorbing writes. -/
theorem absorbR_args {p : Prm} (L : Lay p) : ∀ r ∈ absorbR (State.addr p.W) p.SP, (argR p.SP).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.args_w' (by decide)
  · exact L.args_w' (by decide)
  · exact L.args_w' (by decide)
  · exact L.args_below

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa lens t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  obtain w₀ := E.perm.wW (show 176 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 180 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 184 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 188 + 4 ≤ 3760 by decide)
  obtain a₀ := E.perm.argR' L (k := 0) (by decide)
  obtain a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = Proof.Cmac.store4 t.mem (State.addr p.W + BitVec.ofNat 64 176) (BitVec.ofNat 32 p.al <<< 3)
        (BitVec.ofNat 32 p.al >>> 29) (BitVec.ofNat 32 p.n <<< 3) (BitVec.ofNat 32 p.n >>> 29) ∧
      t₁.gpr .r4 = p.W + BitVec.ofNat 32 176 ∧ t₁.gpr .r5 = BitVec.ofNat 32 16 ∧
      Others [.r0, .r1, .r2, .r4, .r5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock]; srun [E.r11, E.sp, L.wA, a₀, a₈, A.a0, A.a8, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4,
        add_ofNat_assoc, Nat.reduceAdd]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  obtain f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (chunkB_ok L E₁ r4₁ r5₁) fun t₂ C => ?_
  obtain hb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 176) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    obtain ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    obtain en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat32 L.al_lt] at ea
    rw [toNat32 L.n_lt] at en
    rw [hm₁, Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  obtain dHY : ∀ d, d + 16 ≤ 176 → ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁],
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.Arm.blockAt_frame f₁ (dHY 64 (by decide)),
    Proof.AesGcm.Arm.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96)
    (rev (m.readW (W + BitVec.ofNat 64 92) 32) ^^^ m.readW N 32)
    (rev (m.readW (W + BitVec.ofNat 64 88) 32) ^^^ m.readW (N + BitVec.ofNat 64 4) 32)
    (rev (m.readW (W + BitVec.ofNat 64 84) 32) ^^^ m.readW (N + BitVec.ofNat 64 8) 32)
    ((rev (m.readW (W + BitVec.ofNat 64 80) 32) <<< 1) >>> 1)

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  obtain e := GcmSiv.Words32.tagOf_words (rev (m.readW (W + BitVec.ofNat 64 92) 32))
    (rev (m.readW (W + BitVec.ofNat 64 88) 32)) (rev (m.readW (W + BitVec.ofNat 64 84) 32))
    (rev (m.readW (W + BitVec.ofNat 64 80) 32)) (m.readW N 32) (m.readW (N + BitVec.ofNat 64 4) 32)
    (m.readW (N + BitVec.ofNat 64 8) 32)
  rw [tagInMem, Proof.Cmac.bytesAt_store4, Proof.Gcm.Arm.blockAt_rev, Proof.Gcm.Arm.w4,
    GcmSiv.Words32.toBytes_append4, show (12 : Nat) = 4 + 4 + 4 from rfl, Proof.Cmac.bytesAt_add,
    Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]
  simp only [add_ofNat_assoc, Nat.reduceAdd]
  rw [e]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem tagIn_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = tagInMem t.mem (State.addr p.W) (State.addr p.N) ∧
      Others [.r0, .r1, .r2, .r3, .r12] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain r₀ := E.perm.wR (show 80 + 4 ≤ 3760 by decide)
  obtain r₁ := E.perm.wR (show 84 + 4 ≤ 3760 by decide)
  obtain r₂ := E.perm.wR (show 88 + 4 ≤ 3760 by decide)
  obtain r₃ := E.perm.wR (show 92 + 4 ≤ 3760 by decide)
  obtain w₀ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  obtain w₁ := E.perm.wW (show 100 + 4 ≤ 3760 by decide)
  obtain w₂ := E.perm.wW (show 104 + 4 ≤ 3760 by decide)
  obtain w₃ := E.perm.wW (show 108 + 4 ≤ 3760 by decide)
  obtain n₀ : InRegions (t.rd ++ t.wr) (State.addr p.N) 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  obtain n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  obtain n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn]; srun [E.r10, E.r11, add_ofNat_zero, L.nA, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃,
    n₀, n₄, n₈], ?_, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, tagInMem, Proof.Cmac.store4,
    add_ofNat_assoc, Nat.reduceAdd]

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) (SP : BitVec 32) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absorbR W SP

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR (State.addr p.W) p.SP) t.mem t'.mem
  out : bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem (State.addr p.N) 12)
      (bytesAt t.mem (State.addr p.D) p.n) (bytesAt t.mem (State.addr p.A) p.al)

/-- The additional data, as a chunk's source. -/
theorem srcA {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s p.A p.al :=
  ⟨P.aad, L.aw, L.a_w' (by decide), L.a_w' (by decide), L.ba⟩

/-- The data, as a chunk's source. -/
theorem srcD {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s p.D p.n :=
  ⟨covers_left P.d, L.dw, L.d_w' (by decide), L.d_w' (by decide), L.bd⟩

theorem polyval_ok [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (hG : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0) :
    WP isa polyval t (PolyPost p t) := by
  obtain a₀ := E.perm.argR' L (k := 0) (by decide)
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by srun [E.sp, a₀, A.a0], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok L (E.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.al_lt
    (srcA L (E.perm.of_eq (by rfl) (by rfl))) L.a_w (by simp [gpr_setReg, E.r7]) (by simp [gpr_setReg])) fun t₂ P₂ => ?_)
  simp only [mem_setReg] at P₂
  obtain P₂' := P₂.of_eq (t := t) rfl rfl rfl
  obtain A₂ : Args p t₂.mem := A.frame L P₂.frame (absorbR_args L)
  -- The data.
  obtain a₄ := P₂.env.perm.argR' L (k := 4) (by decide)
  obtain a₈ := P₂.env.perm.argR' L (k := 8) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by srun [P₂.env.sp, a₄, a₈, A₂.a4, A₂.a8], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok L (P₂.env.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.n_lt
    (srcD L (P₂.env.perm.of_eq (by rfl) (by rfl))) L.d_w (by simp [gpr_setReg]) (by simp [gpr_setReg])) fun t₄ P₄ => ?_)
  simp only [mem_setReg] at P₄
  rw [Proof.AesGcm.Arm.bytesAt_frame P₂.frame (absorbR_buf L.d_w L.bd) (by have := L.n_lt; omega_arith)] at P₄
  obtain P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  obtain A₄ : Args p t₄.mem := A₂.frame L P₄.frame (absorbR_args L)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok L P₂₄.env A₄) fun t₅ P₅ => ?_)
  obtain P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok L P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.of_others ho₆ sp₆ rd₆ wr₆, by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr],
    ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    obtain nN : bytesAt t₅.mem (State.addr p.N) 12 = bytesAt t.mem (State.addr p.N) 12 :=
      Proof.AesGcm.Arm.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_setReg]

end VG.Proof.AesGcmSiv.Arm

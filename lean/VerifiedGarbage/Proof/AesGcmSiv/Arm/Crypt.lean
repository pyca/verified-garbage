import VerifiedGarbage.Proof.AesGcmSiv.Arm.Tag

/-!
# AES-GCM-SIV on ARMv7: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 176` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below covers_cons covers_nil covers_append' covers_off
  covers_left covers_prefix add_ofNat_assoc add_ofNat_zero add32_ofNat_assoc eval_eq' eval_ne' z_cmp ofNat_sub32
  ofNat_add32 toNat32 mem_store gpr_store sp_store rd_store wr_store z_store mem_subFlags z_subFlags gpr_subFlags
  sp_subFlags rd_subFlags wr_subFlags LoopPre LoopOut xorLoop_ok xorBytes length_bytesAt)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega) (by omega)) hc

/-- What counter mode writes: the counter block, its copy, the block at
`W + 176`, `vg_aes_ctr32`'s working space, the data and the stack below
`SP`. -/
abbrev cryR (W D : Addr) (n : Nat) (SP : BitVec 32) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 176, 16⟩, ⟨W + BitVec.ofNat 64 1712, 2048⟩, ⟨D, n⟩, below SP]

/-- Block `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) :
    State.addr (p.D + BitVec.ofNat 32 j) = State.addr p.D + BitVec.ofNat 64 j :=
  addr_add (by have := L.dw; omega)

theorem Lay.dN {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j := by
  have := L.dw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0)
  ctr : CtrSt (State.addr p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat}
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr)) t = some t₁ ∧
      t₁.mem = copyMem t.mem (State.addr p.W) ∧
      t₁.gpr .r0 = p.W + BitVec.ofNat 32 192 ∧ t₁.gpr .r1 = BitVec.ofNat 32 p.R ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .r12 = BitVec.ofNat 32 1 ∧ t₁.gpr .lr = p.W + BitVec.ofNat 32 1712 ∧
      Others [.r0, .r1, .r2, .r3, .r12, .lr] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  have r₁ := E.perm.wR (show 100 + 4 ≤ 3760 by decide)
  have r₂ := E.perm.wR (show 104 + 4 ≤ 3760 by decide)
  have r₃ := E.perm.wR (show 108 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 112 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 116 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 120 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 124 + 4 ≤ 3760 by decide)
  refine ⟨_, by simp only [copy16, ctrArgs]; srun [E.r8, E.r11, L.wA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4, copyMem,
      add_ofNat_assoc, Nat.reduceAdd]
  all_goals simp [gpr_setReg, E.r8, E.r11, h4]

/-- The arguments of a block's call, as `vg_aes_ctr32` needs them. -/
theorem blkCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (r0 : t₁.gpr .r0 = p.W + BitVec.ofNat 32 192) (r1 : t₁.gpr .r1 = BitVec.ofNat 32 p.R)
    (r2 : t₁.gpr .r2 = p.W + BitVec.ofNat 32 112) (r3 : t₁.gpr .r3 = p.D + BitVec.ofNat 32 (16 * j))
    (r12 : t₁.gpr .r12 = BitVec.ofNat 32 1) (lr : t₁.gpr .lr = p.W + BitVec.ofNat 32 1712) :
    CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
      (p.W + BitVec.ofNat 32 1712) p.R 1 := by
  have hn := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine ⟨r0, r1, r2, r3, r12, lr, L.rounds3, by rw [E₁.sp]; exact L.sp8, by rw [L.wN (by decide)]; omega,
    by rw [L.wN (by decide)]; omega, by rw [L.dN (by omega)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega),
      L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one]
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 192 + 240 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3760 by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact dQ.sub_right (Lay.wSub (by decide))
  · exact L.bw' (by decide)
  · exact L.bw' (by decide)
  · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  · exact L.bw' (by decide)
  · exact E₁.perm.wCR (by decide)
  · exact covers_cons (E₁.perm.wC (by decide)) (covers_cons (covers_off E₁.perm.d (by omega) (by omega))
      (covers_cons (E₁.perm.wC (by decide)) covers_nil))

/-- The code after a block's call. -/
theorem blkPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = t.mem.writeW (State.addr p.W + BitVec.ofNat 64 96)
        (t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1) ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) ∧
      t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) ∧ Others [.r0, .r4, .r5, .r12] t t' ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn := L.n_lt
  have c₀ := E.perm.wR (show 96 + 4 ≤ 3760 by decide)
  have c₁ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  have e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [ofNat_sub32 (by omega) (by omega), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega]
  refine ⟨_, by simp only [blockNext, wholeLeft]; srun [E.r11, L.wA, h4, h5, c₀, c₁], ?_, ?_, ?_, ?_, by others_tac,
    by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags]
  · simp [gpr_setReg, add32_ofNat_assoc, Nat.mul_succ]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, e5]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, e5, ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega)]
    rw [z_cmp (by omega) (by decide)]

theorem cryptBlock_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)) (C : CtrSt (State.addr p.W) icb j t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptBlock t (BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L E h4
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have cc := blkCall L E₁ hj r0 r1 r2 r3 r12 lr
  -- What the copy changed.
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call cc) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [L.wA (show 192 < 3760 by decide), L.wA (show 112 < 3760 by decide), L.dA (show 16 * j < p.n by omega),
    L.wA (show 1712 < 3760 by decide), E₁.sp, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 192) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h5]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩, ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨State.addr p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 1712, 2048⟩, below p.SP],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  have w₂ : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (State.addr p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 100) 12 =
      bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.Arm.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (State.addr p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain ⟨t₃, run₃, hm₃, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L E₂ hj h4₂ h5₂
  refine WP.of_runBlock ⟨t₃, run₃, E₂.of_others ho₃ sp₃ rd₃ wr₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁],
    r4₃, r5₃, z₃, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hm₃, Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), r₂, C.rest]
  · rw [hm₃, Proof.AesGcm.Arm.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt (by omega)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [hm₃]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains _ (Nat.le_refl _) (by decide) (by decide))


/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : Prm} (L : Lay p) :
    ∀ r ∈ cryR (State.addr p.W) (State.addr p.D) p.n p.SP,
      (⟨State.addr p.W + BitVec.ofNat 64 192, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) m m') :
    Spec.GcmSiv.ctxCiph m' (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph m (State.addr p.W + BitVec.ofNat 64 192) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  r4 : t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b)
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : CtrSt (State.addr p.W) icb b t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem blocks_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (h4 : t.gpr .r4 = p.D) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.n)
    (C : CtrSt (State.addr p.W) icb 0 t.mem) (hx : bytesAt t.mem (State.addr p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa (.loop cryptBlock .ne) t (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [h4, Nat.mul_zero, add_ofNat_zero], by rw [h5, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok L P.env hxl (j := j) (by omega) P.r4 P.r5 P.ctr P.data hc') fun t'' Q => ?_
  have P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.r4, Q.r5, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := eval_ne' Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem

theorem cryptTail_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) (C : CtrSt (State.addr p.W) icb b t.mem)
    (hx : bytesAt t.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R = ciph) :
    WP isa cryptTail t (TailPost p ciph icb x t) := by
  have hn' := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (tag_ok L E (o := 176) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ tagR (State.addr p.W) p.SP 176, (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  have hx₂ : bytesAt t₂.mem (State.addr p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.Arm.bytesAt_frame fT dT (by omega), hx]
  have hks : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 176) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * b) := by rw [T.r4, h4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 r := by rw [T.r5, h5]
  obtain ⟨t₃, run₃, r1₃, r2₃, r3₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] t₂ = some t₃ ∧
      t₃.gpr .r1 = p.W + BitVec.ofNat 32 176 ∧ t₃.gpr .r2 = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .r3 = BitVec.ofNat 32 r ∧ Others [.r1, .r2, .r3] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl, by rfl⟩
    · simp [gpr_setReg, T.env.r11]
    · simp [gpr_setReg, h4₂]
    · simp [gpr_setReg, h5₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨State.addr p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have lp : LoopPre t₃ (p.W + BitVec.ofNat 32 176) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨r1₃, r2₃, r3₃, by omega, by omega, by rw [L.wN (by decide)]; omega, by rw [L.dN (by omega)]; omega,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.wA (by decide)]
      exact covers_prefix (T.env.perm.wCR (show 176 + 16 ≤ 3760 by decide)) (by omega)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega) (by omega)
    · rw [eD, L.wA (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 176 + 16 ≤ 3760 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, O⟩ => ?_
  rw [m₃, eD, L.wA (by decide)] at hm₄
  have hl : (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r).length
      = r := by simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.Arm.writeBytes_frame' t₂.mem (q := State.addr p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => by
      have h1 : q ≠ .r1 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h2 : q ≠ .r2 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h3 : q ≠ .r3 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h0 : q ≠ .r0 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      have h12 : q ≠ .r12 := by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [O.other q h0 h1 h2 h3 h12, ho₃ q (by simp [h1, h2, h3])])
      (by rw [O.sp, sp₃]) (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]),
    by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.Arm.bytesAt_writeBytes_self t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * b)) (State.addr p.W + BitVec.ofNat 64 176) r)
        (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (State.addr p.W + BitVec.ofNat 64 176) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega) (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR (State.addr p.W) (State.addr p.D) p.n p.SP) t.mem t'.mem
  data : bytesAt t'.mem (State.addr p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW W 32) (m.readW (W + BitVec.ofNat 64 4) 32)
    (m.readW (W + BitVec.ofNat 64 8) 32) (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = headMem t.mem (State.addr p.W) ∧
      t₁.gpr .r4 = p.D ∧ t₁.gpr .r5 = BitVec.ofNat 32 p.n ∧ t₁.z = decide (p.n / 16 = 0) ∧
      Others [.r0, .r1, .r2, .r3, .r4, .r5, .r12] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have rT₀ : InRegions (t.rd ++ t.wr) (State.addr p.W) 4 := by simpa using E.perm.wR (show 0 + 4 ≤ 3760 by decide)
  have rT₁ := E.perm.wR (show 4 + 4 ≤ 3760 by decide)
  have rT₂ := E.perm.wR (show 8 + 4 ≤ 3760 by decide)
  have rT₃ := E.perm.wR (show 12 + 4 ≤ 3760 by decide)
  have w₀ := E.perm.wW (show 96 + 4 ≤ 3760 by decide)
  have w₁ := E.perm.wW (show 100 + 4 ≤ 3760 by decide)
  have w₂ := E.perm.wW (show 104 + 4 ≤ 3760 by decide)
  have w₃ := E.perm.wW (show 108 + 4 ≤ 3760 by decide)
  have a₄ := E.perm.argR' L (k := 4) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  refine ⟨_, by simp only [cryptHead, wholeLeft]; srun [E.r11, E.sp, add_ofNat_zero, L.wA, rT₀, rT₁, rT₂, rT₃, w₀,
    w₁, w₂, w₃, a₄, a₈, A.a4, A.a8], ?_, ?_, ?_, ?_, by others_tac, by rfl, by rfl, by rfl⟩
  · simp only [mem_setReg, mem_store, mem_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, headMem,
      Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ofNat_lsr32 L.n_lt]
    rw [z_cmp (by have := L.n_lt; omega) (by decide)]

theorem crypt_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa crypt t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E A
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem (State.addr p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have dD : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨State.addr p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem (State.addr p.D) p.n = bytesAt t.mem (State.addr p.D) p.n :=
    Proof.AesGcm.Arm.bytesAt_frame f₁ dD (by omega)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
      Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.Arm.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hicb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16) := by
    rw [hm₁, headMem, Proof.Cmac.bytesAt_store4, ← GcmSiv.Words32.initialCounter_words, Proof.Cmac.le4_readW,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (State.addr p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : CtrSt (State.addr p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have fC : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩ : Region)],
      ∃ q' ∈ cryR (State.addr p.W) (State.addr p.D) p.n p.SP, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t₁
      (BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (State.addr p.W) 16)) (bytesAt t.mem (State.addr p.D) p.n)
        (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [r4₁, Nat.mul_zero, add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok L E₁ hxl (by omega) r4₁ r5₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have r5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [B.r5]; congr 1; omega
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (p.n % 16 = 0) ∧ Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env p t₃ := B.env.of_others ho₃ sp₃ rd₃ wr₃
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact (f₁.sub fC).trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (State.addr p.W + BitVec.ofNat 64 192) p.R =
        Spec.GcmSiv.ctxCiph t.mem (State.addr p.W + BitVec.ofNat 64 192) p.R := by
      rw [m₃, ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_ok L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      (by rw [ho₃ _ (by simp), B.r4]) (by rw [ho₃ _ (by simp), r5₂]) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      ((f₁.sub fC).trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.Arm

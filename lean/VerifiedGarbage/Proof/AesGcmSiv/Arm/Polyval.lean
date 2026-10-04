import VerifiedGarbage.Proof.AesGcmSiv.Arm.Absorb

/-!
# AES-GCM-SIV on ARMv7: POLYVAL and the tag input (`absorb`, `polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`), from the stack arguments `aad_len` and `len`; `tagIn` turns
POLYVAL's result into the tag input (`tagIn_ok`). `polyval_ok`: the tag
input of RFC 8452 §4, with POLYVAL as GHASH with the key `H · x`
(`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

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
  have hz := Proof.Cmac.zero4_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.Arm.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.Arm.bytesAt_add,
    Proof.AesGcm.Arm.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.Arm.bytesAt_frame (Proof.AesGcm.Arm.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s (p.W + BitVec.ofNat 32 224) 16 := by
  have ww := L.ww
  refine ⟨?_, by rw [L.wN (by decide)]; omega, ?_, ?_, ?_⟩ <;> rw [L.wA (by decide)]
  · exact P.wCR (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.bw' (by decide)

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (h4 : t.gpr .r4 = p.W + BitVec.ofNat 32 224) (h5 : t.gpr .r5 = BitVec.ofNat 32 16) :
    WP isa chunk t (Absorbed p (absR (State.addr p.W) p.SP)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (chunk_ok L E (m := 16) (by decide) (by decide) (srcB L E.perm) h4 h5) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt, L.wA (show 224 < 4096 by decide)] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  r4 : t₃.gpr .r4 = p.W + BitVec.ofNat 32 224
  r5 : t₃.gpr .r5 = BitVec.ofNat 32 16
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (State.addr p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTailPre t (TailPre p (State.addr P) r t) := by
  have hw := L.ww
  have w₀ := E.perm.wW (show 224 + 4 ≤ 4096 by decide)
  have w₁ := E.perm.wW (show 228 + 4 ≤ 4096 by decide)
  have w₂ := E.perm.wW (show 232 + 4 ≤ 4096 by decide)
  have w₃ := E.perm.wW (show 236 + 4 ≤ 4096 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, r1₁, r2₁, r3₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (Impl.AesGcm.Arm.zero16 bO ++ ([.mov .r1 (.reg .r4), Impl.AesGcm.Arm.addI .r2 .r11 bO,
        .mov .r3 (.reg .r5)] : List Instr)) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 t.mem (State.addr p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .r1 = P ∧
      t₁.gpr .r2 = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .r3 = BitVec.ofNat 32 r ∧ Others [.r0, .r1, .r2, .r3] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [Impl.AesGcm.Arm.zero16]; srun [E.r11, L.wA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · simp [gpr_setReg, h4]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg, h5]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have dB : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr (p.W + BitVec.ofNat 32 224), r⟩ := by
    rw [L.wA (by decide)]
    exact (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 4096 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 32 224) r :=
    ⟨r1₁, r2₁, r3₁, by omega, by omega, hf, by rw [L.wN (by decide)]; omega, by rw [rd₁, wr₁]; exact hc,
      by rw [L.wA (by decide)]; exact covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 4096 by decide)) (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ lp) fun t₂ ⟨hm₂, O⟩ => ?_)
  have E₂ : Env p t₂ := E₁.keep (fun q hq => O.other q (by
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
  have hd₁ : bytesAt t₁.mem (State.addr P) r = bytesAt t.mem (State.addr P) r := by
    rw [hm₁]
    exact Proof.AesGcm.Arm.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (State.addr p.W + BitVec.ofNat 64 224) 16 =
      bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem (State.addr P) r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega), hl]
  have f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).trans
      ((Proof.AesGcm.Arm.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    by simp only [rd_setReg]; rw [O.rd, rd₁], by simp only [wr_setReg]; rw [O.wr, wr₁],
    by simp [gpr_setReg, E₂.r11], by simp [gpr_setReg],
    by simp only [mem_setReg]; exact f₂, by simp only [mem_setReg]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : BitVec 32} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨State.addr P, r⟩] (t.rd ++ t.wr)) (hf : P.toNat + r ≤ 2 ^ 32)
    (hd : (⟨State.addr P, r⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩) (h4 : t.gpr .r4 = P)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa absTail t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr P) r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hf hd h4 h5) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok L T.env T.r4 T.r5) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 224, 16⟩ : Region)], ∀ d, d + 16 ≤ 224 →
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
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
  have hs := Proof.AesGcm.Arm.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `Z` says whether there are any. -/
theorem absMid_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat}
    (hm : m < 2 ^ 32) (hQ : Src p t Q m) (h4 : t.gpr .r4 = Q) (h5 : t.gpr .r5 = BitVec.ofNat 32 m)
    (hz : t.z = decide (m / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop chunk .ne)) t fun t₂ =>
      Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t₂ ∧
        t₂.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ t₂.gpr .r5 = BitVec.ofNat 32 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h4, h0, Nat.mul_zero, add_ofNat_zero], by rw [h5]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok L E hm (by omega) (hQ.take (by omega)) h4 h5

theorem absorb_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ : Src p t Q m) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 4096⟩) (h4 : t.gpr .r4 = Q)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 m) :
    WP isa absorb t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem (State.addr Q) m))) t) := by
  obtain ⟨t₁, run₁, z₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ := wholeLeft_ok hm h5
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (absMid_ok L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h4])
    (by rw [ho₁ _ (by decide), h5]) z₁) fun t₂ ⟨P₂, r4₂, r5₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  obtain ⟨t₃, run₃, z₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa [.cmp .r5 (Impl.AesGcm.Arm.imm 0)] t₂ = some t₃ ∧
      t₃.z = decide (m % 16 = 0) ∧ Others [] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [r5₂], ?_, fun r _ => by rfl, by rfl, by rfl, by rfl, by rfl⟩
    simp only [z_subFlags]
    rw [z_cmp (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have P₃ : Absorbed p (absR (State.addr p.W) p.SP) (elemsAt t.mem (State.addr Q) (m / 16)) t t₃ :=
    ⟨P₂'.env.of_others ho₃ sp₃ rd₃ wr₃, rd₃.trans P₂'.rd, wr₃.trans P₂'.wr, m₃ ▸ P₂'.frame, by rw [m₃]; exact P₂'.out⟩
  refine WP.ite (decide (m % 16 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₃.sub (absR_sub _ _))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
    have ea := hQ.addr (j := 16 * (m / 16)) (by omega)
    have dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
        ⟨State.addr p.W, 4096⟩ := by
      rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega))
    refine WP.mono (absTail_ok L P₃.env (by omega) (by omega) (by rw [P₃.rd, P₃.wr]; exact hs.rd) hs.wrap dT
      (by rw [ho₃ _ (by simp), r4₂]) (by rw [ho₃ _ (by simp), r5₂])) fun t₄ T => ?_
    have e := Proof.AesGcm.Arm.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.stk.symm) (by omega)
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
theorem lens_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa lens t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  have w₀ := E.perm.wW (show 224 + 4 ≤ 4096 by decide)
  have w₁ := E.perm.wW (show 228 + 4 ≤ 4096 by decide)
  have w₂ := E.perm.wW (show 232 + 4 ≤ 4096 by decide)
  have w₃ := E.perm.wW (show 236 + 4 ≤ 4096 by decide)
  have a₀ := E.perm.argR' L (k := 0) (by decide)
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain ⟨t₁, run₁, hm₁, r4₁, r5₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = Proof.Cmac.store4 t.mem (State.addr p.W + BitVec.ofNat 64 224) (BitVec.ofNat 32 p.al <<< 3)
        (BitVec.ofNat 32 p.al >>> 29) (BitVec.ofNat 32 p.n <<< 3) (BitVec.ofNat 32 p.n >>> 29) ∧
      t₁.gpr .r4 = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .r5 = BitVec.ofNat 32 16 ∧
      Others [.r0, .r1, .r2, .r4, .r5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock]; srun [E.r11, E.sp, L.wA, a₀, a₈, A.a0, A.a8, w₀, w₁, w₂, w₃], ?_, ?_, ?_,
      by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, Proof.Cmac.store4,
        add_ofNat_assoc, Nat.reduceAdd]
    · simp [gpr_setReg, E.r11]
    · simp [gpr_setReg]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
  have f₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (chunkB_ok L E₁ r4₁ r5₁) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (State.addr p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    have ea := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.al)
    have en := GcmSiv.Words32.le64_words (BitVec.ofNat 32 p.n)
    rw [toNat32 L.al_lt] at ea
    rw [toNat32 L.n_lt] at en
    rw [hm₁, Proof.Cmac.bytesAt_store4, ea, en, List.append_assoc]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 224 → ∀ q ∈ [(⟨State.addr p.W + BitVec.ofNat 64 224, 16⟩ : Region)],
      (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
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
  have e := GcmSiv.Words32.tagOf_words (rev (m.readW (W + BitVec.ofNat 64 92) 32))
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
  have r₀ := E.perm.wR (show 80 + 4 ≤ 4096 by decide)
  have r₁ := E.perm.wR (show 84 + 4 ≤ 4096 by decide)
  have r₂ := E.perm.wR (show 88 + 4 ≤ 4096 by decide)
  have r₃ := E.perm.wR (show 92 + 4 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 96 + 4 ≤ 4096 by decide)
  have w₁ := E.perm.wW (show 100 + 4 ≤ 4096 by decide)
  have w₂ := E.perm.wW (show 104 + 4 ≤ 4096 by decide)
  have w₃ := E.perm.wW (show 108 + 4 ≤ 4096 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) (State.addr p.N) 4 := by simpa using E.perm.nR (d := 0) (k := 4) (by decide)
  have n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
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

theorem polyval_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (hG : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (State.addr p.W + BitVec.ofNat 64 80) = 0) :
    WP isa polyval t (PolyPost p t) := by
  have a₀ := E.perm.argR' L (k := 0) (by decide)
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by srun [E.sp, a₀, A.a0], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok L (E.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.al_lt
    (srcA L (E.perm.of_eq (by rfl) (by rfl))) L.a_w (by simp [gpr_setReg, E.r7]) (by simp [gpr_setReg])) fun t₂ P₂ => ?_)
  simp only [mem_setReg] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  have A₂ : Args p t₂.mem := A.frame L P₂.frame (absorbR_args L)
  -- The data.
  have a₄ := P₂.env.perm.argR' L (k := 4) (by decide)
  have a₈ := P₂.env.perm.argR' L (k := 8) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by srun [P₂.env.sp, a₄, a₈, A₂.a4, A₂.a8], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok L (P₂.env.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) (by rfl) (by rfl) (by rfl)) L.n_lt
    (srcD L (P₂.env.perm.of_eq (by rfl) (by rfl))) L.d_w (by simp [gpr_setReg]) (by simp [gpr_setReg])) fun t₄ P₄ => ?_)
  simp only [mem_setReg] at P₄
  rw [Proof.AesGcm.Arm.bytesAt_frame P₂.frame (absorbR_buf L.d_w L.bd) (by have := L.n_lt; omega)] at P₄
  have P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  have A₄ : Args p t₄.mem := A₂.frame L P₄.frame (absorbR_args L)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok L P₂₄.env A₄) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok L P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.of_others ho₆ sp₆ rd₆ wr₆, by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr],
    ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem (State.addr p.N) 12 = bytesAt t.mem (State.addr p.N) 12 :=
      Proof.AesGcm.Arm.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w L.bn) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_setReg]

end VG.Proof.AesGcmSiv.Arm

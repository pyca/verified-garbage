import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Absorb

/-!
# AES-GCM-SIV on AArch64: POLYVAL and the tag input (`polyval`)

Untrusted: everything here is checked by Lean. `absorb` absorbs a string
padded with zeros (`absorb_ok`): its whole blocks by chunks, its last bytes
copied over a zero block at `W + 224` and absorbed as one more chunk
(`absTail_ok`); `lensBlock` puts the lengths block there for one more
(`lens_ok`); `tagIn` turns POLYVAL's result into the tag input
(`tagIn_ok`). `polyval_ok`: the tag input of RFC 8452 §4, with POLYVAL as
GHASH with the key `H · x` (`Proof.GcmSiv.Words.tagInputG`), at `W + 96`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Proof.AesGcm.AArch64 (GcmImpl ofNat_add_ofNat in_off toNat_ofNat_of_lt covers_off covers_left
  ofNat_sub lsr_ofNat eval_zero add_ofNat_assoc Others LoopPre copyLoop_ok loopRegs length_bytesAt)

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  have hz := Proof.Cmac.zero2_bytes m c
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.AArch64.bytesAt_add] at hz
  rw [show 16 = xs.length + (16 - xs.length) by omega, Proof.AesGcm.AArch64.bytesAt_add,
    Proof.AesGcm.AArch64.bytesAt_writeBytes_self _ _ _ (by omega),
    Proof.AesGcm.AArch64.bytesAt_frame (Proof.AesGcm.AArch64.writeBytes_frame' _ rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base c (Nat.le_refl _) (by omega)) (by omega)]
  refine congrArg (xs ++ ·) ?_
  have := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at this
  rw [this, Nat.add_sub_cancel_left]
  simp [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

theorem zero2_eq (m : Mem) (W : Addr) :
    (m.writeW (W + BitVec.ofNat 64 224) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 232) (0 : BitVec 64) =
      Proof.Cmac.zero2 m (W + BitVec.ofNat 64 224) := by
  rw [Proof.Cmac.zero2, add_ofNat_assoc]

/-- The block at `W + 224` as a chunk's source. -/
theorem srcB {p : Prm} (L : Lay p) {s : State} (P : Perm p s) : Src p s (p.W + BitVec.ofNat 64 224) 16 where
  rd := P.wCR (by decide)
  lt := by decide
  wrap := by rw [L.toNat_W (by decide)]; have := L.ww; omega
  y := L.w_w (.inr (by decide)) (by decide) (by decide)
  rev := L.w_w (.inl (by decide)) (by decide) (by decide)

/-- One chunk of the 16 bytes at `W + 224`: their field element absorbed. -/
theorem chunkB_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (h27 : t.gpr .x27 = p.W + BitVec.ofNat 64 224) (h28 : t.gpr .x28 = BitVec.ofNat 64 16) :
    WP isa (chunk v.callees) t (Absorbed p (absR p.W)
      [Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 224) 16)] t) :=
  WP.mono (chunk_ok v L E (m := 16) (by decide) (by decide) (srcB L E.perm) h27 h28) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 224`, as the
bytes to absorb. -/
structure TailPre (p : Prm) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  env : Env p t₃
  rd : t₃.rd = t.rd
  wr : t₃.wr = t.wr
  x27 : t₃.gpr .x27 = p.W + BitVec.ofNat 64 224
  x28 : t₃.gpr .x28 = BitVec.ofNat 64 16
  frame : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, 4096⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa absTailPre t (TailPre p P r t) := by
  have hw := L.ww
  have w₀ := E.perm.wW (show 224 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 4096 by decide)
  -- The block zeroed, and the copy's arguments.
  obtain ⟨t₁, run₁, hm₁, x11₁, x12₁, x13₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State,
      runBlock isa (zero16 bO ++ [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27,
        Impl.AesGcm.AArch64.mov .x13 .x28]) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero2 t.mem (p.W + BitVec.ofNat 64 224) ∧ t₁.gpr .x11 = p.W + BitVec.ofNat 64 224 ∧
      t₁.gpr .x12 = P ∧ t₁.gpr .x13 = BitVec.ofNat 64 r ∧ Others [.x9, .x11, .x12, .x13] t t₁ ∧
      t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [zero16]; grun [E.x19, w₀, w₈], ?_, ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl)⟩
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, movz0, ← zero2_eq]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, h27]
    · simp [gpr_write, h28]
  unfold absTailPre
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dB : (⟨P, r⟩ : Region).Disjoint ⟨p.W + BitVec.ofNat 64 224, r⟩ :=
    (hd.sub_right (Lay.wSub (show 224 + 16 ≤ 4096 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₁ P (p.W + BitVec.ofNat 64 224) r :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hc, Proof.AesGcm.AArch64.covers_prefix (E₁.perm.wC (show 224 + 16 ≤ 4096 by decide))
      (by omega), dB⟩
  refine WP.seq (WP.mono (copyLoop_ok t₁ x12₁ x11₁ x13₁ (by omega) lp) fun t₂ ⟨hm₂, _, _, ho₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env p t₂ := E₁.keep (fun q hq => ho₂ q (by
    simp only [envRegs, loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  -- The data is outside the zeroed block.
  have hd₁ : bytesAt t₁.mem P r = bytesAt t.mem P r := by
    rw [hm₁]
    exact Proof.AesGcm.AArch64.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := length_bytesAt t.mem P r
    rw [hm₂, hd₁, hm₁, pad_bytes _ _ _ (by omega), hl]
  have f₂ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact (Proof.Cmac.frame_store2 _ _ _).trans
      ((Proof.AesGcm.AArch64.writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  exact ⟨E₂.keep (fun q hq => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [rd₂, rd₁], by simp only [wr_write]; rw [wr₂, wr₁],
    by simp [gpr_write, E₂.x19], by simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)],
    by simp only [mem_write]; exact f₂, by simp only [mem_write]; exact hb₂⟩

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨p.W, 4096⟩) (h27 : t.gpr .x27 = P) (h28 : t.gpr .x28 = BitVec.ofNat 64 r) :
    WP isa (absTail v.callees) t
      (AbsPost p [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  refine WP.seq (WP.mono (absTailPre_ok L E hr1 hr hc hd h27 h28) fun t₃ T => ?_)
  refine WP.mono (chunkB_ok v L T.env T.x27 T.x28) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)], ∀ d, d + 16 ≤ 224 →
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, T.rd], by rw [C.wr, T.wr],
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.AesGcm.AArch64.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, length_bytesAt, hs, List.take_left' hl, List.drop_left' hl, GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `x9` holds their number. -/
theorem absMid_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (hQ : Src p t Q m) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m)
    (h9 : t.gpr .x9 = BitVec.ofNat 64 (m / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (chunk v.callees) (.nonzero .x .x9))) t fun t₂ =>
      Absorbed p (absR p.W) (elemsAt t.mem Q (m / 16)) t t₂ ∧
        t₂.gpr .x27 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t₂.gpr .x28 = BitVec.ofNat 64 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (eval_zero h9 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨E, rfl, rfl, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h27, h0, Nat.mul_zero, BitVec.add_zero], by rw [h28]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_ok v L E hm (by omega) (hQ.take (by omega)) h27 h28

/-- `absorb`'s first block. -/
theorem absHead_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (.block [.lsr .x .x9 .x28 4]) t fun t₁ => t₁.gpr .x9 = BitVec.ofNat 64 (m / 16) ∧
      Others [.x9] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
  WP.run ⟨_, by grun [], rfl⟩ fun t₁ ht₁ => by
    subst ht₁
    exact ⟨by simp [gpr_write, h28, lsr_ofNat _ _ hm], by others_tac, rfl, rfl, rfl, rfl⟩

theorem absorb_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {Q : Addr} {m : Nat}
    (hc : Covers [⟨Q, m⟩] (t.rd ++ t.wr)) (hm : m < 2 ^ 64) (hw : Q.toNat + m ≤ 2 ^ 64)
    (hd : (⟨Q, m⟩ : Region).Disjoint ⟨p.W, 4096⟩) (h27 : t.gpr .x27 = Q) (h28 : t.gpr .x28 = BitVec.ofNat 64 m) :
    WP isa (absorb v.callees) t (AbsPost p (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q m))) t) := by
  have hQ : Src p t Q m := Src.ofW L hc hm hw hd
  refine WP.seq (WP.mono (absHead_ok hm h28) fun t₁ ⟨x9₁, ho₁, m₁, sp₁, rd₁, wr₁⟩ => ?_)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  refine WP.seq (WP.mono (absMid_ok v L E₁ hm (hQ.of_eq rd₁ wr₁) (by rw [ho₁ _ (by decide), h27])
    (by rw [ho₁ _ (by decide), h28]) x9₁) fun t₂ ⟨P₂, x27₂, x28₂⟩ => ?_)
  rw [m₁] at P₂
  have P₂' := P₂.of_eq m₁ rd₁ wr₁
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (m % 16 = 0)) (eval_zero x28₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₂'.sub (absR_sub p.W))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega)
    have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨p.W, 4096⟩ :=
      hd.sub_left (Offset.sub_base Q (by omega))
    refine WP.mono (absTail_ok v L P₂'.env (by omega) (by omega) (by rw [P₂'.rd, P₂'.wr]; exact hs.rd) dT x27₂ x28₂)
      fun t₃ T => ?_
    have e := Proof.AesGcm.AArch64.bytesAt_frame P₂'.frame (fun r hr => dT.sub_right ?_) (by omega)
    · rw [e] at T
      exact AbsPost.trans L (P₂'.sub (absR_sub p.W)) T
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

/-! ## The lengths, and the tag input -/

theorem le64_word (x : Nat) : Spec.GcmSiv.le64 x = Proof.Cmac.le8 (BitVec.ofNat 64 x) := GcmSiv.le64_le8 x

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (lens v.callees) t (AbsPost p
      [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))] t) := by
  have w₀ := E.perm.wW (show 224 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 232 + 8 ≤ 4096 by decide)
  obtain ⟨t₁, run₁, hm₁, x27₁, x28₁, ho₁, sp₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa lensBlock t = some t₁ ∧
      t₁.mem = (t.mem.writeW (p.W + BitVec.ofNat 64 224) (BitVec.ofNat 64 (8 * p.al))).writeW
        (p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) (BitVec.ofNat 64 (8 * p.n)) ∧
      t₁.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t₁.gpr .x28 = BitVec.ofNat 64 16 ∧
      Others [.x9, .x27, .x28] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by simp only [lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl),
      (by rfl)⟩
    · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, Mem.writeW, BitVec.setWidth_eq,
        add_ofNat_assoc, ofNat_lsl, E.x24, E.x26]
      rw [Nat.mul_comm p.al, Nat.mul_comm p.n]
    · simp [gpr_write, E.x19]
    · simp [gpr_write, movz_lit (show 16 < 2 ^ 16 by decide)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env p t₁ := E.keep (fun q hq => ho₁ q (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.mono (chunkB_ok v L E₁ x27₁ x28₁) fun t₂ C => ?_
  have hb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 224) 16 =
      Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, le64_word, le64_word]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 224 → ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 224, 16⟩ : Region)],
      (⟨p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨C.env, by rw [C.rd, rd₁], by rw [C.wr, wr₁],
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 64 (by decide)),
    Proof.AesGcm.AArch64.blockAt_frame f₁ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  let lo := rev64 (m.readW (W + BitVec.ofNat 64 88) 64) ^^^ m.readW N 64
  let hi := ((rev64 (m.readW (W + BitVec.ofNat 64 80) 64) ^^^ (m.readW (N + BitVec.ofNat 64 8) 32).setWidth 64)
    <<< 1) >>> 1
  (m.writeW (W + BitVec.ofNat 64 96) lo).writeW (W + BitVec.ofNat 64 104) hi

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  rw [tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
    Proof.Cmac.bytesAt_store2, ← Proof.Gcm.AArch64.blockAt_rev, BitVec.add_zero, add_ofNat_assoc,
    GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words, GcmSiv.Words.shl_shr_one]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) := by
  rw [tagInMem, show W + BitVec.ofNat 64 104 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]]
  exact Proof.Cmac.frame_store2 _ _ _

theorem tagIn_ok {p : Prm} {t : State} (E : Env p t) :
    ∃ t' : State, runBlock isa tagIn t = some t' ∧ t'.mem = tagInMem t.mem p.W p.N ∧
      Others [.x9, .x10, .x11] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have r₀ := E.perm.wR (show 80 + 8 ≤ 4096 by decide)
  have r₈ := E.perm.wR (show 88 + 8 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 4096 by decide)
  have n₀ : InRegions (t.rd ++ t.wr) p.N 8 := by simpa using E.perm.nR (d := 0) (k := 8) (by decide)
  have n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  refine ⟨_, by simp only [tagIn]; grun [E.x19, E.x20, BitVec.add_zero, r₀, r₈, w₀, w₈, n₀, n₈], ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, tagInMem, Mem.writeW, BitVec.setWidth_eq,
    read8_readW, read4_readW]

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absorbR W

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (polyR p.W) t.mem t'.mem
  out : bytesAt t'.mem (p.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem p.N 12) (bytesAt t.mem p.D p.n)
      (bytesAt t.mem p.A p.al)

theorem polyval_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    (hG : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (p.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (p.W + BitVec.ofNat 64 80) = 0) :
    WP isa (polyval v.callees) t (PolyPost p t) := by
  -- The additional data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((E.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact E.perm.aad) L.al_lt L.aw L.a_w
    (by simp [gpr_write, E.x23]) (by simp [gpr_write, E.x24])) fun t₂ P₂ => ?_)
  simp only [mem_write] at P₂
  have P₂' := P₂.of_eq (t := t) rfl rfl rfl
  -- The data.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  refine WP.seq (WP.mono (absorb_ok v L ((P₂.env.write (by decide) _).write (by decide) _) (by simp only [rd_write, wr_write]; exact covers_left P₂.env.perm.d)
    L.n_lt L.dw L.d_w (by simp [gpr_write, P₂.env.x25]) (by simp [gpr_write, P₂.env.x26])) fun t₄ P₄ => ?_)
  simp only [mem_write] at P₄
  rw [Proof.AesGcm.AArch64.bytesAt_frame P₂.frame (absorbR_buf L.d_w) (by have := L.n_lt; omega)] at P₄
  have P₂₄ := AbsPost.trans L P₂' (P₄.of_eq rfl rfl rfl)
  -- The lengths.
  refine WP.seq (WP.mono (lens_ok v L P₂₄.env) fun t₅ P₅ => ?_)
  have P₂₅ := AbsPost.trans L P₂₄ P₅
  -- The tag input.
  obtain ⟨t₆, run₆, hm₆, ho₆, sp₆, rd₆, wr₆⟩ := tagIn_ok P₂₅.env
  refine WP.of_runBlock ⟨t₆, run₆, P₂₅.env.keep (fun q hq => ho₆ q (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆,
    by rw [rd₆, P₂₅.rd], by rw [wr₆, P₂₅.wr], ?_, ?_⟩
  · refine (P₂₅.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₆]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₅.mem p.N 12 = bytesAt t.mem p.N 12 :=
      Proof.AesGcm.AArch64.bytesAt_frame P₂₅.frame (absorbR_buf L.n_w) (by decide)
    rw [hm₆, tagInMem_bytes, nN, P₂₅.out, hG, hY, tagInputG, length_bytesAt, length_bytesAt,
      GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * p.al) ++ Spec.GcmSiv.le64 (8 * p.n))
        (by simp [Spec.GcmSiv.le64])]
    simp only [mem_write]

end VG.Proof.AesGcmSiv.AArch64

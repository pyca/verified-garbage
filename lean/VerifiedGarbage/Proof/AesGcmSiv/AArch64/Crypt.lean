import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Tag
import VerifiedGarbage.Proof.GcmSiv.Ctr

/-!
# AES-GCM-SIV on AArch64: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 224` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcmSiv.AArch64
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.AArch64 (GcmImpl CtrCall CtrPost ctr_call covers_cons covers_nil covers_append covers_off
  covers_left add_ofNat_assoc ofNat_sub lsr_ofNat eval_zero eval_nonzero toNat_ofNat_of_lt Others LoopPre
  xorLoop_ok loopRegs xorBytes length_bytesAt)

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
`W + 224`, `vg_aes_ctr32`'s working space and the data. -/
abbrev cryR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 224, 16⟩, ⟨W + BitVec.ofNat 64 1760, 2048⟩, ⟨D, n⟩]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = p.D + BitVec.ofNat 64 (16 * (j + 1))
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * (j + 1))
  x9 : t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (j + 1)) / 16)
  ctr : CtrSt p.W icb (j + 1) t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR p.W p.D p.n) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : Prm} {t : State} (E : Env p t) {j : Nat}
    (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j)) :
    ∃ t₁ : State, runBlock isa (copy16 cbO ccO ++ ctrArgs ++ [Impl.AesGcm.AArch64.mov .x3 .x27]) t = some t₁ ∧
      t₁.mem = copyMem t.mem p.W ∧
      t₁.gpr .x0 = p.W + BitVec.ofNat 64 240 ∧ t₁.gpr .x1 = BitVec.ofNat 64 p.R ∧
      t₁.gpr .x2 = p.W + BitVec.ofNat 64 112 ∧ t₁.gpr .x3 = p.D + BitVec.ofNat 64 (16 * j) ∧
      t₁.gpr .x4 = BitVec.ofNat 64 1 ∧ t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760 ∧
      Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have r₀ := E.perm.wR (show 96 + 8 ≤ 3808 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [copy16, ctrArgs]; grun [E.x19, E.x22, r₀, r₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 112) 8 v).read (p.W + BitVec.ofNat 64 104) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 104) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [copyMem]
    simp only [mem_write, sep, Mem.writeW, BitVec.setWidth_eq, read8_readW]
  all_goals simp [gpr_write, E.x19, E.x22, h27]

theorem setWidth_rt32' (v : BitVec 32) : (BitVec.setWidth 32 (BitVec.setWidth 64 v) : BitVec 32) = v :=
  setWidth_rt32 v

/-- The arguments of a block's call, as `vg_aes_ctr32` needs them. -/
theorem blkCall {p : Prm} (L : Lay p) {t₁ : State} (E₁ : Env p t₁) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (x0 : t₁.gpr .x0 = p.W + BitVec.ofNat 64 240) (x1 : t₁.gpr .x1 = BitVec.ofNat 64 p.R)
    (x2 : t₁.gpr .x2 = p.W + BitVec.ofNat 64 112) (x3 : t₁.gpr .x3 = p.D + BitVec.ofNat 64 (16 * j))
    (x4 : t₁.gpr .x4 = BitVec.ofNat 64 1) (x5 : t₁.gpr .x5 = p.W + BitVec.ofNat 64 1760) :
    CtrCall t₁ (p.W + BitVec.ofNat 64 240) (p.W + BitVec.ofNat 64 112) (p.D + BitVec.ofNat 64 (16 * j))
      (p.W + BitVec.ofNat 64 1760) p.R 1 :=
  have hn := L.n_lt
  have hdw := L.dw
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    rounds := L.rounds3
    wrap := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * j) (by omega)]
      have : p.D.toNat + 16 * j < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt this]; omega
    n_lt := by decide
    kc := L.w_w (.inr (by decide)) (by decide) (by decide)
    kd := (dQ.sub_right (Lay.wSub (show 240 + 240 ≤ 3808 by decide))).symm
    ks := L.w_w (.inl (by decide)) (by decide) (by decide)
    cd := (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3808 by decide))).symm
    cs := L.w_w (.inl (by decide)) (by decide) (by decide)
    ds := dQ.sub_right (Lay.wSub (by decide))
    reads := covers_append (covers_cons (E₁.perm.wCR (by decide)) covers_nil)
      (covers_cons (E₁.perm.wCR (by decide)) (covers_cons (covers_left (covers_off E₁.perm.d (by omega) hn))
        (covers_cons (E₁.perm.wCR (by decide)) covers_nil)))
    writes := covers_cons (E₁.perm.wC (by decide)) (covers_cons (covers_off E₁.perm.d (by omega) hn)
        (covers_cons (E₁.perm.wC (by decide)) covers_nil)) }

theorem cryptBlock_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j))
    (h28 : t.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j)) (C : CtrSt p.W icb j t.mem)
    (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (cryptBlock v.callees) t (BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, x0, x1, x2, x3, x4, x5, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok E h27
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  have cc := blkCall L E₁ hj x0 x1 x2 x3 x4 x5
  -- What the copy changed.
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  have dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hx₁ : bytesAt t₁.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (by omega), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [Nat.mul_one] at fc
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (p.W + BitVec.ofNat 64 240) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x p.D (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) hn (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 3808 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 3808 by decide)
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), h28]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨p.W + BitVec.ofNat 64 112, 16⟩, ⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨p.W + BitVec.ofNat 64 1760, 2048⟩] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (cryR p.W p.D p.n) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
    · exact ⟨⟨p.D, p.n⟩, by simp, Offset.sub_base p.D (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨p.W + BitVec.ofNat 64 1760, 2048⟩], (⟨p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  have w₂ : t₂.mem.readW (p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.AArch64.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨p.W + BitVec.ofNat 64 96, 4⟩] t₂.mem
      (t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.run ⟨_, by grun [E₂.x19, c₀, c₁, h27₂, h28₂], rfl⟩ fun t₃ ht₃ => ?_
  subst ht₃
  have hmem : ∀ v : BitVec 32, t₂.mem.write (p.W + BitVec.ofNat 64 96) 4 v =
      t₂.mem.writeW (p.W + BitVec.ofNat 64 96) v := fun v => by
    simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  refine ⟨E₂.keep (fun r hr => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
    by simp only [rd_write]; rw [P.rd, rd₁], by simp only [wr_write]; rw [P.wr, wr₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h27₂, add_ofNat_assoc]
    congr 2
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega)]; congr 1
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h28₂]
    rw [ofNat_sub (by omega) (by omega), lsr_ofNat _ _ (by omega)]; congr 2
  · simp only [mem_write, setWidth_rt32]
    refine ⟨?_, ?_⟩
    · rw [hmem, Mem.readW_writeW_self32, read4_readW, w₂, C.word]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      omega
    · rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide), r₂, C.rest]
  · simp only [mem_write]
    rw [hmem, Proof.AesGcm.AArch64.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt hn), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · simp only [mem_write]
    rw [hmem]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains p.W (Nat.le_refl _) (by decide) (by decide))

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : Prm} (L : Lay p) :
    ∀ r ∈ cryR p.W p.D p.n, (⟨p.W + BitVec.ofNat 64 240, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

theorem ciph_cryR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR p.W p.D p.n) m m') :
    Spec.GcmSiv.ctxCiph m' (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.ctxCiph m (p.W + BitVec.ofNat 64 240) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  x27 : t'.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b)
  x28 : t'.gpr .x28 = BitVec.ofNat 64 (p.n - 16 * b)
  ctr : CtrSt p.W icb b t'.mem
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR p.W p.D p.n) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (h27 : t.gpr .x27 = p.D) (h28 : t.gpr .x28 = BitVec.ofNat 64 p.n)
    (C : CtrSt p.W icb 0 t.mem) (hx : bytesAt t.mem p.D p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (.loop (cryptBlock v.callees) (.nonzero .x .x9)) t (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .nonzero .x .x9)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [h27, Nat.mul_zero, BitVec.add_zero], by rw [h28, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (p.W + BitVec.ofNat 64 240) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega) P.x27 P.x28 P.ctr P.data hc') fun t'' Q => ?_
  have P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.x27, Q.x28, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := eval_nonzero Q.x9 (by have := L.n_lt; omega)
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
  data : bytesAt t'.mem p.D p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (cryR p.W p.D p.n) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h27 : t.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b))
    (h28 : t.gpr .x28 = BitVec.ofNat 64 r) (C : CtrSt p.W icb b t.mem)
    (hx : bytesAt t.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R = ciph) :
    WP isa (cryptTail v.callees) t (TailPost p ciph icb x t) := by
  have hn' := L.n_lt
  refine WP.seq (WP.mono (tag_ok v L E (o := 224) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ tagR p.W 224, (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact L.d_w' (by decide)
  have hx₂ : bytesAt t₂.mem p.D p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame fT dT (Nat.le_of_lt hn'), hx]
  have hks : bytesAt t₂.mem (p.W + BitVec.ofNat 64 224) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h27₂ : t₂.gpr .x27 = p.D + BitVec.ofNat 64 (16 * b) := by rw [T.x27, h27]
  have h28₂ : t₂.gpr .x28 = BitVec.ofNat 64 r := by rw [T.x28, h28]
  obtain ⟨t₃, run₃, x11₃, x12₃, x13₃, ho₃, m₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [Impl.AesGcm.AArch64.ptr .x11 .x19 bO, Impl.AesGcm.AArch64.mov .x12 .x27, Impl.AesGcm.AArch64.mov .x13 .x28]
        t₂ = some t₃ ∧
      t₃.gpr .x11 = p.W + BitVec.ofNat 64 224 ∧ t₃.gpr .x12 = p.D + BitVec.ofNat 64 (16 * b) ∧
      t₃.gpr .x13 = BitVec.ofNat 64 r ∧ Others [.x11, .x12, .x13] t₂ t₃ ∧ t₃.mem = t₂.mem ∧ t₃.sp = t₂.sp ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by grun [], ?_, ?_, ?_, by others_tac, (by rfl), (by rfl), (by rfl), (by rfl)⟩
    · simp [gpr_write, T.env.x19]
    · simp [gpr_write, h27₂]
    · simp [gpr_write, h28₂]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have dQ : (⟨p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨p.W, 3808⟩ :=
    L.d_w.sub_left (Offset.sub_base p.D (by omega))
  have lp : LoopPre t₃ (p.W + BitVec.ofNat 64 224) (p.D + BitVec.ofNat 64 (16 * b)) r := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [rd₃, wr₃]
      exact Proof.AesGcm.AArch64.covers_prefix (T.env.perm.wCR (show 224 + 16 ≤ 3808 by decide)) (by omega)
    · rw [wr₃]; exact covers_off T.env.perm.d (by omega) hn'
    · exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 3808 by decide))).sub_right (Region.sub_prefix (by omega))).symm
  refine WP.mono (xorLoop_ok t₃ x11₃ x12₃ x13₃ (by omega) lp) fun t₄ ⟨hm₄, ho₄, sp₄, rd₄, wr₄⟩ => ?_
  rw [m₃] at hm₄
  have hl : (xorBytes t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) (p.W + BitVec.ofNat 64 224) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.AArch64.writeBytes_frame' t₂.mem (q := p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => by
      rw [ho₄ q (by
        simp only [envRegs, loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ho₃ q (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)])
      (by rw [sp₄, sp₃]) (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃]),
    by rw [rd₄, rd₃, T.rd], by rw [wr₄, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.AArch64.bytesAt_writeBytes_self t₂.mem (p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (p.D + BitVec.ofNat 64 (16 * b)) (p.W + BitVec.ofNat 64 224) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (p.W + BitVec.ofNat 64 224) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x p.D (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn') (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.D, p.n⟩, by simp, Offset.sub_base p.D (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p.W p.D p.n) t.mem t'.mem
  data : bytesAt t'.mem p.D p.n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 96) (m.readW W 64)).writeW (W + BitVec.ofNat 64 104)
    (m.readW (W + BitVec.ofNat 64 8) 64 ||| 0x8000000000000000#64)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = headMem t.mem p.W ∧
      t₁.gpr .x27 = p.D ∧ t₁.gpr .x28 = BitVec.ofNat 64 p.n ∧ t₁.gpr .x9 = BitVec.ofNat 64 (p.n / 16) ∧
      Others [.x9, .x10, .x27, .x28] t t₁ ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have rT₀ : InRegions (t.rd ++ t.wr) p.W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3808 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3808 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3808 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3808 by decide)
  refine ⟨_, by simp only [cryptHead]; grun [E.x19, BitVec.add_zero, rT₀, rT₈, w₀, w₈], ?_, ?_, ?_, ?_,
    by others_tac, (by rfl), (by rfl), (by rfl)⟩
  · have sep : ∀ v : BitVec (8 * 8), (t.mem.write (p.W + BitVec.ofNat 64 96) 8 v).read (p.W + BitVec.ofNat 64 8) 8 =
        t.mem.read (p.W + BitVec.ofNat 64 8) 8 := fun _ =>
      Mem.read_write_sep (Offset.sep p.W (.inl (by decide)) (by decide) (by decide)) (by decide)
    have mz : (BitVec.setWidth 64 (32768 : BitVec 16) <<< 48 : BitVec 64) = 0x8000000000000000#64 := by decide
    rw [headMem]
    simp only [mem_write, sep, mz, Mem.writeW, BitVec.setWidth_eq, read8_readW]
  · simp [gpr_write, E.x25]
  · simp [gpr_write, E.x26]
  · simp [gpr_write, E.x26, lsr_ofNat _ _ L.n_lt]

theorem crypt_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (crypt v.callees) t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n_lt
  obtain ⟨t₁, run₁, hm₁, x27₁, x28₁, x9₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem p.D p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨p.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
      rw [add_ofNat_assoc]]
    exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁.mem p.D p.n = bytesAt t.mem p.D p.n := Proof.AesGcm.AArch64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (p.W + BitVec.ofNat 64 240) p.R =
      Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  have hicb : bytesAt t₁.mem (p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16) := by
    rw [hm₁, headMem, show p.W + BitVec.ofNat 64 104 = p.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by
        rw [add_ofNat_assoc], Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : Env p t₁ := E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have fC : ∀ q ∈ [(⟨p.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR p.W p.D p.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub p.W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock v.callees) (.nonzero .x .x9))) t₁
      (BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) (bytesAt t.mem p.D p.n) (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_zero x9₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [x27₁, Nat.mul_zero, BitVec.add_zero], by rw [x28₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok v L E₁ hxl (by omega) x27₁ x28₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have x28₂ : t₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [B.x28]; congr 1; omega
  refine WP.ite (decide (p.n % 16 = 0)) (eval_zero x28₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨B.env, by rw [B.rd, rd₁], by rw [B.wr, wr₁], (f₁.sub fC).trans B.frame, ?_⟩
    rw [B.data, show 16 * (p.n / 16) = p.n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (p.W + BitVec.ofNat 64 240) p.R =
        Spec.GcmSiv.ctxCiph t.mem (p.W + BitVec.ofNat 64 240) p.R := by
      rw [ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_ok v L B.env hxl (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)
      B.x27 x28₂ B.ctr B.data hc₂) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, B.rd, rd₁], by rw [T.wr, B.wr, wr₁], ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.AArch64

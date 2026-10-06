import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Chunk

/-!
# AES-GCM-SIV on x86-64: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set; each block
of the data is encrypted in place by `vg_aes_ctr32` from a copy of it at
`W + 112`, after which its first word is incremented (`cryptBlock_ok`); the
last bytes are XORed with the keystream block, computed at `W + 128`
(`cryptTail_ok`). `crypt_ok`: the data becomes `ctr` of it (RFC 8452 §4).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall CtrPost ctr_call toNat_ofNat_of_lt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What counter mode writes: the counter block, its copy and the block at
`W + 128`, `vg_aes_ctr32`'s working space, the stack below `SP` and the data. -/
abbrev cryR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩, below SP 8,
    ⟨D, n⟩]

/-- The slots, after code that writes only parts of `W` apart from them, the
stack below `SP` and a buffer apart from `W`. -/
theorem Slots.of_frame {W : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {m m' : Mem}
    {rs : List Region} (S : Slots W R N A D al n m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) : Slots W R N A D al n m' := by
  have k (d : Nat) (hd' : 200 ≤ d ∧ d + 8 ≤ 248) :
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    hf.readW (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub W (by omega) (by omega))) (by decide)
  exact ⟨by rw [k 200 (by decide)]; exact S.rounds, by rw [k 208 (by decide)]; exact S.nonce,
    by rw [k 216 (by decide)]; exact S.aad, by rw [k 224 (by decide)]; exact S.alen,
    by rw [k 232 (by decide)]; exact S.data, by rw [k 240 (by decide)]; exact S.len⟩

theorem slots_cryR {K W SP : Addr} (L : Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : Buf K W SP s D n) :
    ∀ r ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {K W SP : Addr} (L : Lay K W SP) {s : State} {D : Addr} {n : Nat} (hD : Buf K W SP s D n) :
    ∀ r ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (hD.w.sub_right (Lay.wSub (by decide))).symm

/-- What a chunk of counter mode leaves, from `t`, up to block `j`. -/
structure ChunkOut (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (b j : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = D + BitVec.ofNat 64 (16 * j)
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - j)
  zf : t'.zf = some (decide (b - j = 0))
  ctr : CtrSt W icb j t'.mem
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * j)
  frame : Frame (cryR W SP D n) t.mem t'.mem

/-- The counter block, after code that writes apart from it. -/
theorem CtrSt.of_frame {W : Addr} {icb : List Byte} {j : Nat} {m m' : Mem} (C : CtrSt W icb j m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint r) : CtrSt W icb j m' :=
  ⟨by rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]; exact C.word,
    by rw [Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => (hd r hr).sub_left
      (by rw [show W + BitVec.ofNat 64 100 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 4 by rw [add_ofNat_assoc]]
          exact Offset.sub_base _ (by decide))) (by decide)]; exact C.rest⟩

theorem cryptChunk_ok (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem)
    (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte}
    (hxl : x.length = n) {b j : Nat} (hb : 16 * b ≤ n) (hj : j < b) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j))
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) (C : CtrSt W icb j t.mem)
    (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (cryptChunk ⟨eb.enc.name, eb.enc.code⟩) t
      (ChunkOut K W SP D n ciph icb x b (j + min 64 (b - j)) t) := by
  have hn := hD.lt
  have hw := L.ww
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  generalize hcd : min 64 (b - j) = c
  unfold cryptChunk ksXor
  have hc1 : 1 ≤ c := by omega
  have hc64 : c ≤ 64 := by omega
  have hjc : 16 * (j + c) ≤ n := by omega
  have hk16 : ∀ i, (GcmSiv.ksBlock ciph icb i).length = 16 := fun i => by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine seq_assoc (WP.seq (WP.mono (chunkHead_wp (b := b) (j := j) (by omega) hbx) fun t₂ H => ?_))
  obtain ⟨r14₂, g₂, m₂, rd₂, wr₂⟩ := H
  rw [hcd] at r14₂
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
  refine WP.seq (WP.mono (ctrGen_ok L E₂ hc1 hc64 r14₂ (by rw [m₂]; exact C)) fun t₃ G => ?_)
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => G.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    G.rd G.wr
  have dG : ∀ {Q : Addr} {k : Nat}, (⟨Q, k⟩ : Region).Disjoint ⟨W, 3816⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 4⟩ : Region), ⟨W + BitVec.ofNat 64 488, 1024⟩], (⟨Q, k⟩ : Region).Disjoint r :=
    fun hQ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hQ.sub_right (Lay.wSub (by decide))
  have S₂ : Slots W R N A D al n t₂.mem := by rw [m₂]; exact S
  have S₃ : Slots W R N A D al n t₃.mem := S₂.of_frame G.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (by omega) (by decide) (by decide))
  have r14₃ : t₃.gpr .r14 = BitVec.ofNat 64 c := by
    rw [G.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), r14₂]
  obtain ⟨t₄, run₄, rdi₄, rsi₄, rdx₄, rcx₄, r8₄, sv₄, m₄, rd₄, wr₄⟩ := ecbArgs_ok E₃ S₃ r14₃
  have E₄ : Env K W SP t₄ := E₃.of_saved sv₄ rd₄ wr₄
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, WP.seq ?_⟩)
  refine WP.mono (Proof.AesOcb.X86_64.blk_call eb.encOk eb.encNosp eb.encDepth
    (bargs L E₄ hR hc64 rdi₄ rsi₄ rdx₄ rcx₄ r8₄)) fun t₅ B => ?_
  have E₅ : Env K W SP t₅ := E₄.of_saved B.saved B.rd B.wr
  have fB := B.frame
  rw [E₄.rsp] at fB
  -- The keystream blocks.
  have hc₄ : Spec.GcmSiv.ctxCiph t₄.mem (W + BitVec.ofNat 64 248) R = ciph := by
    rw [m₄, ctxCiph_frame G.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.w_w (by omega) (by decide) (by decide)) hRb, m₂, hc]
  have hks : ∀ k < c, bytesAt t₅.mem (W + BitVec.ofNat 64 (488 + 16 * k)) 16 = GcmSiv.ksBlock ciph icb (j + k) :=
    fun k hk => by
      have := bytesAt_cipher B.out hk
      rw [add_ofNat_assoc] at this
      rw [this, m₄, G.blocks k hk, ← m₄, ← hc₄]
      rfl
  -- The XOR.
  have h15₅ := E₅.r15
  obtain ⟨t₆, run₆, rcx₆, rsi₆, g₆, m₆, rd₆, wr₆⟩ : ∃ t₆, runBlock isa
      (([.mov .rcx (.reg .r14)] : List Instr) ++ ptr .rsi .r15 revO) t₅ = some t₆ ∧
      t₆.gpr .rcx = BitVec.ofNat 64 c ∧ t₆.gpr .rsi = W + BitVec.ofNat 64 488 ∧
      (∀ r, r ≠ .rcx → r ≠ .rsi → t₆.gpr r = t₅.gpr r) ∧ t₆.mem = t₅.mem ∧ t₆.rd = t₅.rd ∧ t₆.wr = t₅.wr := by
    have r14₅ : t₅.gpr .r14 = BitVec.ofNat 64 c := by rw [B.saved _ (by decide), sv₄ _ (by decide), r14₃]
    refine ⟨_, by srun [h15₅, r14₅], ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₅, r14₅]; done)
    · intro r h₁ h₂; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₆ : Env K W SP t₆ := E₅.keep (fun r hr => g₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₆ wr₆
  have rd₀₆ : t₆.rd = t.rd := by rw [rd₆, B.rd, rd₄, G.rd, rd₂]
  have wr₀₆ : t₆.wr = t.wr := by rw [wr₆, B.wr, wr₄, G.wr, wr₂]
  have h12₆ : t₆.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by
    rw [g₆ _ (by decide) (by decide), B.saved _ (by decide), sv₄ _ (by decide),
      G.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), h12]
  -- What the pieces before the XOR wrote: parts of `W` and the stack.
  have f₂₃ : Frame [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩,
      below SP 8] t₂.mem t₃.mem := G.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by simp, fun _ h => h⟩
  have f₄₅ : Frame [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩,
      below SP 8] t₄.mem t₅.mem := fB.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 488, 1024⟩, by simp, Offset.sub W (by decide) (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have fW : Frame [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 488, 1024⟩, ⟨W + BitVec.ofNat 64 1768, 2048⟩,
      below SP 8] t.mem t₆.mem := by
    rw [m₆, ← m₂]; rw [m₄] at f₄₅; exact f₂₃.trans f₄₅
  have hx₆ : bytesAt t₆.mem D n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fW (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hD.w.sub_right (Lay.wSub (by decide))
      · exact hD.w.sub_right (Lay.wSub (by decide))
      · exact hD.w.sub_right (Lay.wSub (by decide))
      · exact hD.stk.symm) (Nat.le_of_lt hn), hx]
  have hD₆ : Buf K W SP t₆ D n := hD.of_eq rd₀₆ wr₀₆
  refine WP.seq (WP.seq (WP.of_runBlock ⟨t₆, run₆, ?_⟩))
  refine WP.mono (xorLoop_ok L E₆ hD₆ (by rw [wr₀₆]; exact hDw) hxl hk16 hc1 hc64 hjc
    (fun k hk => by rw [m₆]; exact hks k hk)
    ⟨by rw [h12₆, Nat.add_zero], by rw [rsi₆, Nat.mul_zero, Nat.add_zero], by rw [rcx₆, Nat.sub_zero],
      by rw [Nat.add_zero]; exact hx₆, Frame.refl _ _, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩) fun t₇ X => ?_
  have rbx₇ : t₇.gpr .rbx = BitVec.ofNat 64 (b - j) := by
    rw [X.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide),
      B.saved _ (by decide), sv₄ _ (by decide), G.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), hbx]
  have r14₇ : t₇.gpr .r14 = BitVec.ofNat 64 c := by
    rw [X.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide),
      B.saved _ (by decide), sv₄ _ (by decide), r14₃]
  refine WP.of_runBlock ⟨_, by srun [rbx₇, r14₇], ?_⟩
  have E₇ : Env K W SP t₇ := E₆.keep (fun r hr => X.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    X.rd X.wr
  have dC : ∀ r ∈ [(⟨D + BitVec.ofNat 64 (16 * j), 16 * c⟩ : Region)],
      (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hD.w.sub_left (Offset.sub_base D (by omega))).sub_right (Lay.wSub (by decide))).symm
  refine ⟨E₇.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq]) rfl rfl,
    by simp only [rd_setReg, rd_arithFlags]; rw [X.rd, rd₀₆],
    by simp only [wr_setReg, wr_arithFlags]; rw [X.wr, wr₀₆], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq]
    rw [X.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide),
      B.saved _ (by decide), sv₄ _ (by decide), G.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide)]
  · simp only [gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq]
    exact X.r12
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · simp only [zf_setReg, zf_arithFlags]
    rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · simp only [mem_setReg, mem_arithFlags]
    refine (G.ctr.of_frame (by rw [← m₄]; exact fB) fun r hr => ?_).of_frame (by rw [← m₆]; exact X.frame) dC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (by omega) (by decide) (by omega)
    · exact L.w_w (by omega) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  · simp only [mem_setReg, mem_arithFlags]
    exact X.data
  · simp only [mem_setReg, mem_arithFlags]
    exact (fW.mono (by simp)).trans (X.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩)

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (b : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = D + BitVec.ofNat 64 (16 * b)
  ctr : CtrSt W icb b t'.mem
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR W SP D n) t.mem t'.mem

theorem blocks_ok (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b : Nat}
    (hb : 16 * b ≤ n) (hb1 : 1 ≤ b) (h12 : t.gpr .r12 = D) (hbx : t.gpr .rbx = BitVec.ofNat 64 b)
    (C : CtrSt W icb 0 t.mem) (hx : bytesAt t.mem D n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (.loop (cryptChunk ⟨eb.enc.name, eb.enc.code⟩) .ne) t (BlocksPost K W SP D n ciph icb x b t) := by
  refine WP.loop (M := isa) (body := cryptChunk ⟨eb.enc.name, eb.enc.code⟩) (c := .ne)
    (fun (m : Nat) (t' : State) => ∃ j, m = b - j ∧ j < b ∧ BlocksPost K W SP D n ciph icb x j t t' ∧
      t'.gpr .rbx = BitVec.ofNat 64 (b - j)) ?_ (b - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, rfl, by rw [h12, Nat.mul_zero, BitVec.add_zero], C,
      by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩, by rw [hbx, Nat.sub_zero]⟩
  rintro m t' ⟨j, rfl, hj, P, hbx'⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R = ciph := by
    rw [ctxCiph_frame P.frame (key_cryR L hD) (by rcases hR with h | h <;> subst h <;> decide), hc]
  refine WP.mono (cryptChunk_ok eb L hR P.env (S.of_frame P.frame (slots_cryR L hD)) (hD.of_eq P.rd P.wr)
    (by rw [P.wr]; exact hDw) hxl hb hj P.r12 hbx' P.ctr P.data hc') fun t'' Q => ?_
  have P' : BlocksPost K W SP D n ciph icb x (j + min 64 (b - j)) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.rbp.trans P.rbp, Q.r12, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  by_cases he : b - (j + min 64 (b - j)) = 0
  · left
    have hjb : j + min 64 (b - j) = b := by omega
    exact ⟨(eval_ne Q.zf).trans (by simp [he]), hjb ▸ P'⟩
  · right
    exact ⟨(eval_ne Q.zf).trans (by simp [he]), b - (j + min 64 (b - j)), by omega, j + min 64 (b - j), rfl,
      by omega, P', Q.rbx⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x n
  frame : Frame (cryR W SP D n) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b r : Nat}
    (hn : n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b))
    (hbp : t.gpr .rbp = BitVec.ofNat 64 r) (C : CtrSt W icb b t.mem)
    (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (cryptTail v.callees) t (TailPost K W SP D n ciph icb x t) := by
  have hn' := hD.lt
  refine seq_assoc ?_
  show WP isa (.seq (tag v.callees 128) _) t _
  refine WP.seq (WP.mono (tag_ok v L hR E S (o := 128) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  have dT : ∀ q ∈ tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.w.sub_right (Lay.wSub (by decide))
    · exact hD.stk.symm
  have hx₂ : bytesAt t₂.mem D n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fT dT (Nat.le_of_lt hn'), hx]
  have hks : bytesAt t₂.mem (W + BitVec.ofNat 64 128) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  have h15₂ := T.env.r15
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * b) := by rw [T.saved _ (by decide), h12]
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 r := by rw [T.saved _ (by decide), hbp]
  obtain ⟨t₃, run₃, rdi₃, rsi₃, rcx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 bO ++ ([.mov .rcx (.reg .rbp)] : List Instr)) t₂ =
        some t₃ ∧
      t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * b) ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 128 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 r ∧ (∀ q, q ≠ .rdi → q ≠ .rsi → q ≠ .rcx → t₃.gpr q = t₂.gpr q) ∧
      t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15₂, h12₂, hbp₂]; done)
    · intro q h₁ h₂ h₃; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have lp : Proof.AesGcm.X86_64.LoopPre t₃ (W + BitVec.ofNat 64 128) (D + BitVec.ofNat 64 (16 * b)) r :=
    ⟨rsi₃, rdi₃, rcx₃, hr1, by omega, by rw [hrd₃, hwr₃]; exact T.env.perm.wCR (by omega),
      by rw [hwr₃, T.wr]; exact Proof.AesGcm.X86_64.covers_off hDw (by omega) hn',
      ((hD.w.sub_left (Offset.sub_base D (show 16 * b + r ≤ n by omega))).sub_right (Lay.wSub (by omega))).symm⟩
  refine WP.mono (Proof.AesGcm.X86_64.xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  rw [hm₃] at hm₄
  have hl : (Proof.AesGcm.X86_64.xorBytes t₂.mem (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 128) r).length = r := by
    simp [Proof.AesGcm.X86_64.xorBytes, Proof.Cmac.bytesAt_length]
  have fw := Proof.AesGcm.X86_64.writeBytes_frame' t₂.mem (q := D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.env.keep (fun q hq => ?_) (by rw [hrd₄, hrd₃]) (by rw [hwr₄, hwr₃]),
    by rw [hrd₄, hrd₃, T.rd], by rw [hwr₄, hwr₃, T.wr], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;>
      rw [hg₄ _ (by decide) (by decide) (by decide), hg₃ _ (by decide) (by decide) (by decide)]
  · have hb' : bytesAt t₄.mem (D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₂.mem (D + BitVec.ofNat 64 (16 * b))
        (Proof.AesGcm.X86_64.xorBytes t₂.mem (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 128) r) (by omega)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (W + BitVec.ofNat 64 128) r (16 - r)
      rw [show r + (16 - r) = 16 by omega, hks] at hs
      rw [hm₄, e, Proof.AesGcm.X86_64.xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x D (i := b) (n := r) (by omega) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn') (by omega)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR W SP D n) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)

/-- The start of `crypt`: the counter block from the tag, and the data's
whole blocks and last bytes. -/
theorem cryptHead_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) :
    ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.reg .rbp),
        .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)] t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 96) (t.mem.readW W 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8)
        (t.mem.readW (W + BitVec.ofNat 64 8) 64 ||| 0x8000000000000000#64) ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rT₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [h15, rT₀, rT₈, rD, rL, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, add_ofNat_assoc]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sD]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL, hand]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
      Proof.AesGcm.X86_64.shr4 _ hn]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, sL, Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
  · intro r hr h₁ h₂ h₃; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    any_goals exact absurd rfl h₁
    any_goals exact absurd rfl h₂
    any_goals exact absurd rfl h₃
    all_goals simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem crypt_ok (v : GcmImpl) (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) :
    WP isa (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩) t (CryptPost K W SP R D n t) := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rT₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hbx₁, hzf₁, hg₁, hrd₁, hwr₁⟩ := cryptHead_ok L E S hD
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have f₁ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hx₁ : bytesAt t₁.mem D n = bytesAt t.mem D n := Proof.AesGcm.X86_64.bytesAt_frame f₁ dD (Nat.le_of_lt hn)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide)
  have hicb : bytesAt t₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
      ← Proof.Cmac.bytesAt_split]
  have h4 := Proof.Cmac.bytesAt_add t₁.mem (W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  have C₀ : CtrSt W (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have S₁ := S.of_frame f₁ (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have fC : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR W SP D n, Region.Sub q q' := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (cryptChunk ⟨eb.enc.name, eb.enc.code⟩) .ne)) t₁
      (BlocksPost K W SP D n (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (n / 16) t₁) := by
    refine WP.ite (decide (n / 16 = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, rfl, by rw [h12₁, Nat.mul_zero, BitVec.add_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok eb L hR E₁ S₁ (hD.of_eq hrd₁ hwr₁) (by rw [hwr₁]; exact hDw) hxl (by omega) (by omega) h12₁
        hbx₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := B.rbp.trans hbp₁
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, hbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := B.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [hrd₃, B.rd, hrd₁], by rw [hwr₃, B.wr, hwr₁],
      by rw [hm₃]; exact (f₁.sub fC).trans B.frame, ?_⟩
    rw [hm₃, B.data, show 16 * (n / 16) = n by omega, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    have F₃ : Frame (cryR W SP D n) t₁.mem t₃.mem := by rw [hm₃]; exact B.frame
    have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
      rw [ctxCiph_frame F₃ (key_cryR L hD) (by rcases hR with h | h <;> subst h <;> decide), hc₁]
    refine WP.mono (cryptTail_ok v L hR E₃ (S₁.of_frame F₃ (slots_cryR L hD))
      (hD.of_eq (by rw [hrd₃, B.rd, hrd₁]) (by rw [hwr₃, B.wr, hwr₁])) (by rw [hwr₃, B.wr, hwr₁]; exact hDw) hxl
      (b := n / 16) (r := n % 16) (by omega) (by omega) (by omega) (by rw [hg₃, B.r12]) (by rw [hg₃, hbp₂])
      (by rw [hm₃]; exact B.ctr) (by rw [hm₃]; exact B.data) hc₃) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, hrd₃, B.rd, hrd₁], by rw [T.wr, hwr₃, B.wr, hwr₁],
      ((f₁.sub fC).trans F₃).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.X86_64

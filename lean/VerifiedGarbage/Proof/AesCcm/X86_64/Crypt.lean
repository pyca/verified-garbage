import VerifiedGarbage.Proof.AesCcm.X86_64.Chunk

/-!
# AES-CCM on x86-64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre xorLoop_ok xorBytes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `r12`, `rbx` and `r14` for the first chunk. -/
theorem ctrHeadBlk_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) s fun s₁ =>
      CtrInv K W SP s R nonce D n 0 s₁ ∧ s₁.zf = some (decide (n / 16 = 0)) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hn64 := C.buf.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, hm₁, h12, hbx, h14, hzf, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
        .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .r14 = BitVec.ofNat 64 1 ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, shr4 n hn64]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl,
        shr4 n hn64, and_self_beq (show n / 16 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, ⟨E.keep hg hrd hwr, hrd, hwr, by rw [h12, Nat.mul_zero, BitVec.add_zero],
    by rw [hbx, Nat.sub_zero], h14, Nat.zero_le _, by rw [hm₁]; exact Frame.refl _ _, rfl, by rw [hm₁]⟩, hzf⟩

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop (ctrChunk v.callee) .ne))) s
      (CtrInv K W SP s R nonce D n (n / 16)) := by
  refine WP.seq (WP.mono (ctrHeadBlk_ok C E S) fun s₁ ⟨I₀, hzf⟩ => ?_)
  refine WP.ite _ (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    exact WP.of_runBlock ⟨s₁, rfl, by rw [h0]; exact I₀⟩
  · have h0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = n / 16 - b ∧ b < n / 16 ∧ CtrInv K W SP s R nonce D n b t) ?_
      (n / 16 - 0) s₁ ⟨0, rfl, by omega, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_ok v C I hb) fun t' ⟨k, _, hk1, hkb, I', hz⟩ => ?_
    by_cases he : b + k = n / 16
    · left; exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact I'⟩
    · right; exact ⟨(eval_ne hz).trans (by simp [he]), n / 16 - (b + k), by omega, b + k, rfl, by omega, I'⟩

/-- The arguments of the call for the last bytes: `Ctr₁₊ₙ/₁₆` and a zero
block at `W + 80`. -/
theorem tailSetup_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {nonce : List Byte} {j : Nat}
    (hRo : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : j < 256 ^ (15 - nonce.length)) (h14 : t.gpr .r14 = BitVec.ofNat 64 j) :
    ∃ t', runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
        ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO) t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      t'.gpr .rdi = K ∧ t'.gpr .rsi = BitVec.ofNat 64 R ∧ t'.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t'.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t'.gpr .r8 = BitVec.ofNat 64 1 ∧ t'.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have rR := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨t₁, run₁, hm₁, hsi₁, hax₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rsi = BitVec.ofNat 64 R ∧ t₁.gpr .rax = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain ⟨t₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ := ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) hj hax₁
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have h15₂ := E₂.r15
  have w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  have w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ [.mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 88) (0 : BitVec 64) ∧
      t₃.gpr .rdi = K ∧ t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₃.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t₃.gpr .r8 = BitVec.ofNat 64 1 ∧ t₃.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t₃.gpr r = t.gpr r) ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
    refine ⟨_, by crun [zero16, h15₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₂.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₂ .rsi (by decide) (by decide) (by decide), hsi₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        rw [hg₂ _ (by decide) (by decide) (by decide), hg₁ _ (by decide) (by decide)]
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₂, hrd₁]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₂, hwr₁]
  have e88 : W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  have c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains W (by omega) (by omega) (by decide)
  refine ⟨t₃, ?_, ?_, ?_, ?_, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩
  · simp only [List.append_assoc]
    rw [runBlock_append, run₁, Option.bind_some, runBlock_append, run₂, Option.bind_some]
    simpa only [List.append_assoc] using run₃
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · have fz : Frame [⟨W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
    have dz : ∀ r ∈ [(⟨W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    rw [bytesAt_frame fz dz (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- The last `r = n mod 16` bytes, from `t` after the whole blocks, with `r`
in `rbp`. -/
theorem tail_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {t t₀ : State} (I : CtrInv K W SP s R nonce D n (n / 16) t)
    (hm₀ : t₀.mem = t.mem) (hg₀ : ∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r)
    (hbp : t₀.gpr .rbp = BitVec.ofNat 64 (n % 16)) (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : n % 16 ≠ 0) :
    WP isa (.seq (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
          ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
          ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO))
      (.seq (callCtr v.callee)
        (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 ksO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop))) t₀
      fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  have E₀ : Env K W SP t₀ := I.env.keep (fun r hr => hg₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₀ hwr₀
  have hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₁, run₁, f₁, hc₁, hz₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ :=
    tailSetup_ok E₀ (by rw [hm₀, C.readW_kept I.frame (by omega), C.ro]) C.h7 C.h13
      (by rw [hm₀, C.bytes_kept I.frame (by omega), C.c0]) (j := 1 + n / 16) (by have := C.hn; omega)
      (by rw [hg₀ _ (by decide), I.r14])
  have E₁ : Env K W SP t₁ := E₀.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The keystream block.
  have hq := srcW (s := t₁) L E₁.perm (t := 80) (k := 16 * 1) (by decide)
  have hqc : (⟨W + BitVec.ofNat 64 80, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    L.w_w (.inr (by decide)) (by decide) (by decide)
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 80, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (ctr_call v (cargs L E₁ C.rounds (c := 64) (by decide) hq hqc hqk
    (E₁.perm.wC (d := 80) (n := 16 * 1) (by decide)) hdi hsi hdx hcx hr8 hr9)) fun t₂ h => ?_)
  have E₂ : Env K W SP t₂ := E₁.of_saved h.saved h.rd h.wr
  have h15₂ := E₂.r15
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by rw [h.saved _ (by decide), hg₁ _ (by simp), hbp]
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [h.saved _ (by decide), hg₁ _ (by simp), hg₀ _ (by decide), I.r12]
  obtain ⟨t₃, run₃, hm₃, hdi₃, hsi₃, hcx₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r15 ksO ++ [.mov .rcx (.reg .rbp)]) t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 (n % 16) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := E₂.keep hg₃ hrd₃ hwr₃
  have rd₃ : t₃.rd = s.rd := by rw [hrd₃, h.rd, hrd₁, hrd₀, I.rd]
  have wr₃ : t₃.wr = s.wr := by rw [hwr₃, h.wr, hwr₁, hwr₀, I.wr]
  have hS := C.buf.slice (a := 16 * (n / 16)) (k := n % 16) (by omega)
  have lp : LoopPre t₃ (W + BitVec.ofNat 64 80) (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    ⟨hsi₃, hdi₃, hcx₃, by omega, by omega, covers_left (E₃.perm.wC (d := 80) (n := n % 16) (by omega)),
      by rw [wr₃]; exact covers_off C.dw (by omega) hn64, (hS.w.sub_right (Lay.wSub (by omega))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  -- What the tail wrote.
  have hsp : t₁.gpr .rsp = SP := E₁.rsp
  have cT : Frame [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8] t.mem t₃.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have sep : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8], (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    have hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact (hB.stk.sub_left (below8_sub SP)).symm
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (W + BitVec.ofNat 64 80) (n % 16) :=
    ⟨_, rfl⟩
  rw [← hxs] at hm₄
  have hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
  have fw : Frame [⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.keep (fun r hr => hg₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₄ hwr₄, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below SP 16, by simp, below8_sub SP⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
  · -- The bytes.
    have h₁ : bytesAt t₃.mem D (16 * (n / 16)) = bytesAt t.mem D (16 * (n / 16)) := by
      have := bytesAt_frame cT (sep (a := 0) (l := 16 * (n / 16)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
      rw [bytesAt_frame cT (sep (by omega)) (by omega), show n % 16 = n - 16 * (n / 16) by omega, I.rest]
    have f₁' : Frame (ctrR W SP D n) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem K R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt t₃.mem (W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem K R (Spec.Ccm.ctrBlock nonce (1 + n / 16)) := by
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + n / 16) (by have := C.h13; omega) (fun i hi => by
        rw [show i = 0 by omega, Nat.add_zero]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, C.ciph_kept f₁', xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem K R) nonce (1 + n / 16)
      (d := bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega)
    rw [hm₄, bytesAt_writeBytes_at t₃.mem D xs (by rw [hxl]; omega) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega), List.append_nil,
      ← bytesAt_prefix t₃.mem D (show 16 * (n / 16) ≤ n by omega), h₁, I.done, hxs, xorBytes, h₂,
      bytesAt_prefix t₃.mem (W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega), hks, ht']
    conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (n / 16)]

/-- `rbp = n mod 16`, and ZF set when there are no last bytes. -/
theorem ctrB3_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {n : Nat}
    (hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n) (hn64 : n < 2 ^ 64) :
    WP isa (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)]) t
      fun t₀ => t₀.mem = t.mem ∧ t₀.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
        (∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r) ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  have h15 := E.r15
  have rl := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  refine WP.of_runBlock ⟨_, by crun [h15, rl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, and15',
      toNat_ofNat_of_lt hn64]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, and15',
      toNat_ofNat_of_lt hn64, and_self_beq (show n % 16 < 2 ^ 64 by omega)]
  · intro r h₁; simp only [gpr_setReg, gpr_arithFlags, h₁, ite_false]
  all_goals rfl

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (ctr v.callee) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine seq_assoc (WP.seq (WP.mono (ctrHead_ok v C E S) fun t I => ?_))
  have hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    rw [C.readW_kept I.frame (by omega)]; exact S.len
  refine WP.seq (WP.mono (ctrB3_ok I.env hl hn64) fun t₀ ⟨hm₀, hbp, hzf, hg₀, hrd₀, hwr₀⟩ => ?_)
  refine WP.ite _ (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, I.env.keep (fun r hr => hg₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₀ hwr₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega] at hd
    rw [hm₀, hd]
  · exact tail_ok v C I hm₀ hg₀ hbp hrd₀ hwr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.X86_64

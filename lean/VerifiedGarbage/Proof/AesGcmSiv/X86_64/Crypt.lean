import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Tag
import VerifiedGarbage.Proof.GcmSiv.Ctr

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

/-- What counter mode writes: the counter block, its copy and the block at
`W + 128`, `vg_aes_ctr32`'s working space, the stack below `SP` and the data. -/
abbrev cryR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 2048, 2048⟩, below SP 8, ⟨D, n⟩]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (b j : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  rbp : t'.gpr .rbp = t.gpr .rbp
  r12 : t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1))
  rbx : t'.gpr .rbx = BitVec.ofNat 64 (b - (j + 1))
  zf : t'.zf = some (decide (b - (j + 1) = 0))
  ctr : CtrSt W icb (j + 1) t'.mem
  data : bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR W SP D n) t.mem t'.mem

theorem cryptBlock_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {b j : Nat}
    (hb : 16 * b ≤ n) (hj : j < b) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j))
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) (C : CtrSt W icb j t.mem)
    (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 512) R = ciph) :
    WP isa (cryptBlock v.callees) t (BlockPost K W SP D n ciph icb x b j t) := by
  have h15 := E.r15
  have hw := L.ww
  have hn := hD.lt
  have rR := S.rounds
  have rR' := E.perm.wR (show 272 + 8 ≤ 4096 by decide)
  have r₀ := E.perm.wR (show 96 + 8 ≤ 4096 by decide)
  have r₈ := E.perm.wR (show 104 + 8 ≤ 4096 by decide)
  have w₀ := E.perm.wW (show 112 + 8 ≤ 4096 by decide)
  have w₈ := E.perm.wW (show 120 + 8 ≤ 4096 by decide)
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr)) t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 112) (t.mem.readW (W + BitVec.ofNat 64 96) 64)).writeW
        (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (t.mem.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 112 ∧ t₁.gpr .rcx = D + BitVec.ofNat 64 (16 * j) ∧
      t₁.gpr .r8 = BitVec.ofNat 64 1 ∧ t₁.gpr .r9 = W + BitVec.ofNat 64 2048 ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [copy16, ctrArgs, h15, rR, rR', r₀, r₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, add_ofNat_assoc]
    all_goals try (simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15, rR, h12]; done)
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  have hQ : Buf K W SP t₁ (D + BitVec.ofNat 64 (16 * j)) (16 * 1) := (hD.slice (by omega)).of_eq hrd₁ hwr₁
  have cc : CtrCall t₁ (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 112) (D + BitVec.ofNat 64 (16 * j))
      (W + BitVec.ofNat 64 2048) R 1 :=
    cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide) (srcBuf hQ) (hQ.w.sub_right (Lay.wSub (by decide)))
      (hQ.w.sub_right (Lay.wSub (show 512 + 240 ≤ 4096 by decide))).symm
      (by rw [hwr₁]; exact Proof.AesGcm.X86_64.covers_off hDw (by omega) hn) rdi rsi rdx rcx r8 r9
  -- What the copy changed.
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hcb : bytesAt t₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split,
      C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 512) R = ciph := by
    rw [ctxCiph_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), hc]
  have hx₁ : bytesAt t₁.mem D n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₁ dD hn.le, hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp, Nat.mul_one] at fc
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith R (bytesAt t₁.mem (W + BitVec.ofNat 64 512) (16 * (R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (W + BitVec.ofNat 64 512) R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₂.mem D n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x D (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) hn (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
    · exact .inl rfl
    · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
    · exact .inr hD.stk.symm
  have E₂ : Env K W SP t₂ := E₁.of_saved P.saved P.rd P.wr
  have h15₂ := E₂.r15
  have c₀ := E₂.perm.wR (show 96 + 4 ≤ 4096 by decide)
  have c₁ := E₂.perm.wW (show 96 + 4 ≤ 4096 by decide)
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by rw [P.saved _ (by decide), hg₁ _ (by decide), h12]
  have hbx₂ : t₂.gpr .rbx = BitVec.ofNat 64 (b - j) := by rw [P.saved _ (by decide), hg₁ _ (by decide), hbx]
  have sw : ∀ y : BitVec 32, (BitVec.setWidth 32 (BitVec.setWidth 64 y) : BitVec 32) = y := fun y => by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨D + BitVec.ofNat 64 (16 * j), 16⟩, ⟨W + BitVec.ofNat 64 2048, 2048⟩,
      below SP 8] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (cryR W SP D n) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨W + BitVec.ofNat 64 2048, 2048⟩, below SP 8], (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact ((hD.w.sub_left (Offset.sub_base D (show 16 * j + 16 ≤ n by omega))).sub_right
          (Lay.wSub (by omega))).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
  have w₂ : t₂.mem.readW (W + BitVec.ofNat 64 96) 32 = t.mem.readW (W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.X86_64.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  have fw : ∀ v : BitVec 32, Frame [⟨W + BitVec.ofNat 64 96, 4⟩] t₂.mem (t₂.mem.writeW (W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨_, by srun [h15₂, c₀, c₁, h12₂, hbx₂], ?_⟩
  refine ⟨E₂.keep (fun r hr => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_arithFlags, gpr_setReg, mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg,
    wr_arithFlags, wr_setReg, zf_arithFlags, zf_setReg, ite_true, ite_false, reduceCtorEq, sw]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · rw [P.rd, hrd₁]
  · rw [P.wr, hwr₁]
  · rw [P.saved _ (by decide), hg₁ _ (by decide)]
  · rw [add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · refine ⟨?_, ?_⟩
    · rw [Mem.readW_writeW_self32, w₂, C.word]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [Proof.AesGcm.X86_64.bytesAt_frame (fw _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide), r₂, C.rest]
  · rw [Proof.AesGcm.X86_64.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))) hn.le, hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega]
  · exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains W (le_refl _) (by decide) (by omega))

end VG.Proof.AesGcmSiv.X86_64

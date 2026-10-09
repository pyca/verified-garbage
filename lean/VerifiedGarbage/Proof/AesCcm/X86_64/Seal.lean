import VerifiedGarbage.Proof.AesCcm.X86_64.Args
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesCcm.X86_64.Cmp

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `mac y` followed by `tag y`
leaves the MAC of the payload at `D`, encrypted, at `W + y` (`macTag_ok`).
`seal` is `entry`, `Ctr₀` (`ctrs`), the encrypted MAC at `W`, counter mode
over the data (`ctr`), the tag copied to `tag` (`tagOut_ok`) and `restore`
(`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What `mac y` and `tag y` write. -/
abbrev tagR (W SP : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩,
    ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16]

theorem tagR_wR (W SP : Addr) {y : Nat} (hy : y + 16 ≤ 112) : ∀ r ∈ tagR W SP y, ∃ r' ∈ wR W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The MAC of the payload at `D`, encrypted with `CIPH_K(Ctr₀)`, at `W + y`. -/
theorem macTag_ok (v : UpdateImpl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf K W SP s A al) (hD : Buf K W SP s D n) {Q : State → Prop}
    (hk : ∀ s', Env K W SP s' → s'.rd = s.rd → s'.wr = s.wr → Frame (tagR W SP y) s.mem s'.mem →
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 →
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
          (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n))) → Q s') :
    WP isa (.seq (mac v.callee y) (tag v.ctr.callee y)) s Q := by
  have hy16 : y + 16 ≤ 112 := by omega_arith
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> subst h <;> decide
  refine WP.seq (WP.mono (mac_ok v L E S hR hnl h7 h13 ht4 ht16 hte hn hc0 hy hA hD) fun s₁ M => ?_)
  have fy : Frame (tagR W SP y) s.mem s₁.mem := M.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have hRo₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [rounds_kept L hy M.frame]; exact S.rounds
  have hc₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc0]
  refine WP.mono (tag_ok v.ctr L M.env hR hRo₁ (by omega_arith) (by omega_arith) hc₁ hy)
    fun s₂ ⟨E₂, _, rd₂, wr₂, f₂, h₂⟩ => ?_
  refine hk s₂ E₂ (by rw [rd₂, M.rd]) (by rw [wr₂, M.wr]) (fy.trans (f₂.sub fun r hr => ?_)) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), hc₁]
  · rw [h₂, M.out, ctxCiph_frame M.frame (k_macR L (by omega_arith)) hRb]

/-- The return address is outside what the functions write. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega_arith)
  · exact hD

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag `T`, whose
address is at `SP + 24`. -/
theorem tagOut_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTw : Covers [⟨T, tl⟩] s.wr) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa tagOut s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem T (bytesAt s.mem W tl) := by
  have h15 := E.r15
  have hsp := E.rsp
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hcx, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, hsp, hT]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, htl]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have lp : LoopPre s₁ W T tl :=
    ⟨hsi, hdi, hcx, by omega_arith, by omega_arith, covers_left (by simpa using E₁.perm.wC (d := 0) (n := tl) (by omega_arith)),
      by rw [hwr₁]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ⟨E₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂,
    by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], by rw [hm₂, hm₁]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : UpdateImpl) {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (Tb : TagBuf W SP D n T tl) (hTw : Covers [⟨T, tl⟩] s.wr)
    (hTr : (⟨SP, 8⟩ : Region).Disjoint ⟨T, tl⟩) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
        (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have f₂' : Frame (wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  have S₂ := slots_mut L Ar.data.w (f₂'.sub (wR_mut W SP D n)) S₁
  -- The encrypted MAC at `W`.
  refine seq_assoc (WP.seq (macTag_ok v L E₂ S₂ Ar.rounds (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁))
    (Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) fun s₃ E₃ rd₃ wr₃ f₃ c₃ h₃ => ?_))
  have f₁₃ : Frame (wR W SP) s₁.mem s₃.mem := f₂'.trans (f₃.sub (tagR_wR W SP (by decide)))
  have S₃ := slots_mut L Ar.data.w (f₁₃.sub (wR_mut W SP D n)) S₁
  -- Counter mode.
  have C₃ : CtrCtx K W SP s₃ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₃.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, c₃, Ar.data.of_eq (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁)),
      by rw [wr₃, wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.mono (ctr_ok v.ctr C₃ E₃ S₃) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_
  have f₁₄ : Frame (mutR W SP D n) s₁.mem s₄.mem := (f₁₃.sub (wR_mut W SP D n)).trans (f₄.sub (ctrR_mut W SP D n))
  have fall : Frame (entryR W :: mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  -- The tag copied to `T`.
  have hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [argT_kept fall Ar.argsW Ar.argsD, hT]
  have hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀₄, wr₀₄]; exact h
  refine WP.seq (WP.mono (tagOut_ok E₄ (slots_mut L Ar.data.w f₁₄ S₁) Ar.t4 Ar.t16 hT₄ hTr₄
    (by rw [wr₀₄]; exact hTw) Tb.w) fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  have hx : (bytesAt s₄.mem W tl).length = tl := length_bytesAt _ _ _
  have f₅ : Frame [⟨T, tl⟩] s₄.mem s₅.mem := by rw [hm₅]; exact writeBytes_frame' _ hx
  -- `restore`.
  have sv₅ : Saved s₅.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₄ sv₁ p hp]
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f₅.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Tb.w.sub_right (Lay.wSub (by omega_arith))).symm) (by decide)
  obtain ⟨s₆, run₆, hg₆, hm₆, hsp₆, _⟩ := restore_ok E₅ sv₅
  refine WP.of_runBlock ⟨s₆, run₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₆ (.rbx, 112) (by decide)
    · exact hg₆ (.rbp, 120) (by decide)
    · rw [hsp₆, E₅.rsp, hsp]
    · exact hg₆ (.r12, 128) (by decide)
    · exact hg₆ (.r13, 136) (by decide)
    · exact hg₆ (.r14, 144) (by decide)
    · exact hg₆ (.r15, 152) (by decide)
  · rw [hm₆, hsp, f₅.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hTr) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    have c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₂'.sub (wR_mut W SP D n)), hK₁]
    have c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₁₃.sub (wR_mut W SP D n)), hK₁]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_wR Ar.aad f₂', hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₂', hent Ar.data]
    have d₃ : bytesAt s₃.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₁₃, hent Ar.data]
    have w₄ : bytesAt s₄.mem W tl = bytesAt s₃.mem W tl := bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 216) (k := 8) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 384) (k := 2176) (.inl (by have := Ar.t16; omega_arith))
          (by have := Ar.t16; omega_arith) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))).symm) (by have := Ar.t16; omega_arith)
    have d₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n :=
      bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Tb.d.symm) (by have := Ar.data.lt; omega_arith)
    have t₅ : bytesAt s₅.mem T tl = bytesAt s₄.mem W tl := by
      have e := bytesAt_writeBytes_at s₄.mem T (o := 0) (n := tl) (bytesAt s₄.mem W tl) (by rw [hx]; omega_arith)
        (by have := Ar.t16; omega_arith)
      rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
        List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
      rw [hm₅, e]
    have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
    rw [e0] at h₃
    have hY := congrArg List.length h₃
    rw [length_bytesAt, length_xorFrom] at hY
    simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hm₆, d₅, h₄, c₃', d₃, crypt_eq (hBC _)]
    · rw [hm₆, t₅, w₄, bytesAt_prefix s₃.mem W Ar.t16, h₃, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
        ← mac_eq _ _ (by rw [length_bytesAt]; have := Ar.h13; omega_arith), c₂', a₂, d₂]

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp (v : UpdateImpl) {s : State} (h : sealX86_64.pre s) :
    WP isa («seal» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  have A := args_of_seal h
  seal_wp' v A.1.1 A.1.2 A.2.1 A.2.2 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesCcm.X86_64

import VerifiedGarbage.Proof.AesCcm.X86_64.Args
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `mac y` followed by `tag y`
leaves the MAC of the payload at `D`, encrypted, at `W + y` (`macTag_ok`).
`seal` is `entry`, `Ctr₀` (`ctrs`), the encrypted MAC at `W`, counter mode
over the data (`ctr`) and `restore` (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

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
theorem macTag_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    {N A D : Addr} {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13)
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hA : Buf K W SP s A al) (hD : Buf K W SP s D n) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ s', Env K W SP s' → s'.rd = s.rd → s'.wr = s.wr → Frame (tagR W SP y) s.mem s'.mem →
      bytesAt s'.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 →
      bytesAt s'.mem (W + BitVec.ofNat 64 y) 16 = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 0
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem K R) (Spec.Cmac.zeros 16)
          (Spec.Ccm.format tl nonce (bytesAt s.mem A al) (bytesAt s.mem D n))) → WP isa k s' Q) :
    WP isa (.seq (mac v.callee v.suffix y) (.seq (tag v.callee y) k)) s Q := by
  have hy16 : y + 16 ≤ 112 := by omega
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
  refine WP.seq (WP.mono (tag_ok v L M.env hR hRo₁ (by omega) (by omega) hc₁ hy)
    fun s₂ ⟨E₂, _, rd₂, wr₂, f₂, h₂⟩ => ?_)
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
  · rw [h₂, M.out, ctxCiph_frame M.frame (k_macR L (by omega)) hRb]

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
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («seal» v.callee v.suffix) s fun s' => gprPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
        (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem W tl) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  -- `Ctr₀`.
  refine WP.seq (WP.mono (ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have f₂' : Frame (wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  have S₂ := slots_mut L Ar.data.w (f₂'.sub (wR_mut W SP D n)) S₁
  -- The encrypted MAC at `W`.
  refine macTag_ok v L E₂ S₂ Ar.rounds (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn c₂ (y := 0)
    (.inl rfl) (Ar.aad.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)) (Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁))
    fun s₃ E₃ rd₃ wr₃ f₃ c₃ h₃ => ?_
  have f₁₃ : Frame (wR W SP) s₁.mem s₃.mem := f₂'.trans (f₃.sub (tagR_wR W SP (by decide)))
  have S₃ := slots_mut L Ar.data.w (f₁₃.sub (wR_mut W SP D n)) S₁
  -- Counter mode.
  have C₃ : CtrCtx K W SP s₃ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₃.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, c₃, Ar.data.of_eq (rd₃.trans (rd₂.trans rd₁)) (wr₃.trans (wr₂.trans wr₁)),
      by rw [wr₃, wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₃ E₃ S₃) fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  have f₁₄ : Frame (mutR W SP D n) s₁.mem s₄.mem := (f₁₃.sub (wR_mut W SP D n)).trans (f₄.sub (ctrR_mut W SP D n))
  -- `restore`.
  obtain ⟨s₅, run₅, hg₅, hm₅, hsp₅, _⟩ := restore_ok E₄ (saved_mut L Ar.data.w f₁₄ sv₁)
  refine WP.of_runBlock ⟨s₅, run₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₅ (.rbx, 112) (by decide)
    · exact hg₅ (.rbp, 120) (by decide)
    · rw [hsp₅, E₄.rsp, hsp]
    · exact hg₅ (.r12, 128) (by decide)
    · exact hg₅ (.r13, 136) (by decide)
    · exact hg₅ (.r14, 144) (by decide)
    · exact hg₅ (.r15, 152) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₄.mem :=
      (f₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₅, hsp]
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
      · simpa using L.w_w (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 216) (k := 8) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · simpa using L.w_w (a := 0) (n := tl) (d := 384) (k := 2176) (.inl (by have := Ar.t16; omega))
          (by have := Ar.t16; omega) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega))).symm) (by have := Ar.t16; omega)
    have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
    rw [e0] at h₃
    have hY := congrArg List.length h₃
    rw [length_bytesAt, length_xorFrom] at hY
    simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hm₅, h₄, c₃', d₃, crypt_eq (hBC _)]
    · rw [hm₅, w₄, bytesAt_prefix s₃.mem W Ar.t16, h₃, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
        ← mac_eq _ _ (by rw [length_bytesAt]; have := Ar.h13; omega), c₂', a₂, d₂]

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp (v : Ctr32Impl) {s : State} (h : onePre s) :
    WP isa («seal» v.callee v.suffix) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' :=
  seal_wp' v (args_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesCcm.X86_64

import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
import VerifiedGarbage.Proof.AesCcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesCcm.X86_64.Mask

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 96`, then the comparison of its first `t` bytes with the
received tag at `T`, whose address is on the stack, the mask of the data and
`restore` (`openTail_ok`, `open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- The tag length loaded into `rbx`, and the address of the received tag
`T` into `rsi`. -/
theorem loadTag_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8) :
    ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  have rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, hsp, hT]
  · intro r a b; simp [gpr_setReg, a, b]
  all_goals rfl

/-- The comparison of the encrypted MAC at `W + 96` with the received tag at
`T`, and `ok` stored at `W + 224`. -/
theorem openCmp_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.block [.store (at_ .r15 okO) .rax])))) s fun s₄ =>
      Env K W SP s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem ∧
      s₄.mem.readW (W + BitVec.ofNat 64 224) 64 =
        if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0 := by
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := loadTag_ok E S hT hTr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁
  refine WP.seq (WP.mono (recv_ok E₁ hbx₁ ht1 ht16 hsi₁ (by rw [hrd₁, hwr₁]; exact hTc)
      (hTW.sub_right (Lay.wSub (by decide)))) fun s₂ ⟨E₂, hR₂, f₂, hbx₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok L (o := 96) (by decide) E₂ (by rw [hbx₂, hbx₁]) ht1 ht16 (length_bytesAt _ _ _) hR₂)
    fun s₃ ⟨E₃, hax₃, f₃, rd₃, wr₃⟩ => ?_)
  -- `ok` in `W + 224`.
  have h15₃ := E₃.r15
  have wo := E₃.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hm₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.store (at_ .r15 okO) .rax] s₃ = some s₄ ∧
      s₄.mem = s₃.mem.writeW (W + BitVec.ofNat 64 224) (s₃.gpr .rax) ∧ s₄.gpr = s₃.gpr ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr := by
    refine ⟨_, by crun [h15₃, wo], ?_, ?_, ?_, ?_⟩ <;> rfl
  have E₄ : Env K W SP s₄ := E₃.keep (fun r _ => by rw [hg₄]) hrd₄ hwr₄
  have f₄ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₃.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₀₄w : Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem := by
    rw [← hm₁]
    refine ((f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have rd₀₄ : s₄.rd = s.rd := by rw [hrd₄, rd₃, rd₂, hrd₁]
  have wr₀₄ : s₄.wr = s.wr := by rw [hwr₄, wr₃, wr₂, hwr₁]
  have hV : bytesAt s₂.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem (W + BitVec.ofNat 64 96) tl := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide))
      (by omega), hm₁]
  rw [hV, hm₁] at hax₃
  refine WP.of_runBlock ⟨s₄, run₄, E₄, rd₀₄, wr₀₄, f₀₄w, ?_⟩
  rw [hm₄, Mem.readW_writeW_self64, hax₃]

/-- From the encrypted MAC at `W + 96` on: the comparison, the mask and the
restore. -/
theorem openTail_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hD : Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr)
    (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {g : Reg → BitVec 64} (sv : Saved s.mem W g) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++
        restore))))))) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.gpr .rsp = SP ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0) ∧
      bytesAt s'.mem D n =
        (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then bytesAt s.mem D n else zeros n) ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨D, n⟩] s.mem s'.mem := by
  refine seq_assoc4 (WP.seq (WP.mono (openCmp_ok L E S ht1 ht16 hT hTr hTc hTW)
    fun s₄ ⟨E₄, rd₀₄, wr₀₄, f₀₄w, hok'⟩ => ?_))
  have f₀₄ : Frame (mutR W SP D n) s.mem s₄.mem := f₀₄w.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  have S₄ := slots_mut L hD.w f₀₄ S
  obtain ⟨c, hc⟩ : ∃ c, c = decide (bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl) := ⟨_, rfl⟩
  have hok : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [hok', hc]; simp only [decide_eq_true_eq]
  refine WP.seq (WP.mono (mask_ok E₄ S₄ (hD.of_eq rd₀₄ wr₀₄) (by rw [wr₀₄]; exact hDw) hok)
    fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  -- `ok` in `rax`, and the registers back.
  have f₅ : Frame [⟨D, n⟩] s₄.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ (length_mask _ _ _ _)
  have hok₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [f₅.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hD.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), hok]
  have h15₅ := E₅.r15
  have ro := E₅.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₆, run₆, hm₆, hax₆, hg₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₅ = some s₆ ∧
      s₆.mem = s₅.mem ∧ s₆.gpr .rax = (if c then 1 else 0) ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧
      s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by crun [h15₅, ro], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, hok₅]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₆ : Env K W SP s₆ := E₅.keep (fun r hr => hg₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₆ hwr₆
  have f₀₆ : Frame (mutR W SP D n) s.mem s₆.mem := by
    rw [hm₆]; exact f₀₄.trans (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, hax₇⟩ := restore_ok E₆ (saved_mut L hD.w f₀₆ sv)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆, Option.bind_some, run₇], hg₇,
    by rw [hsp₇, E₆.rsp], ?_, ?_, ?_⟩
  · rw [hax₇, hax₆, hc]; simp only [decide_eq_true_eq]
  · have hx : (if c then bytesAt s₄.mem D n else zeros n).length = n := length_mask _ _ _ _
    have e := bytesAt_writeBytes_at s₄.mem D (o := 0) (n := n) (if c then bytesAt s₄.mem D n else zeros n)
      (by rw [hx]; omega) hD.lt
    rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
    have hd₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := bytesAt_frame f₀₄w (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hD.w.sub_right (Lay.wSub (by decide))) (by have := hD.lt; omega)
    rw [hm₇, hm₆, hm₅, e, hc, hd₄]
    simp only [decide_eq_true_eq]
  · rw [hm₇, hm₆]
    exact (f₀₄w.sub fun r hr => ⟨r, by simp at hr ⊢; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : UpdateImpl) {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (Tb : TagBuf W SP D n T tl) (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
          (bytesAt s.mem A al) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
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
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have f₂' : Frame (wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  have S₂ := slots_mut L Ar.data.w (f₂'.sub (wR_mut W SP D n)) S₁
  -- Counter mode: the plaintext.
  have C₂ : CtrCtx K W SP s₂ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₂.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, c₂, Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by rw [wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v.ctr C₂ E₂ S₂) fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₁₃ : Frame (mutR W SP D n) s₁.mem s₃.mem := (f₂'.sub (wR_mut W SP D n)).trans (f₃.sub (ctrR_mut W SP D n))
  have S₃ := slots_mut L Ar.data.w f₁₃ S₁
  have c₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N nl) 0 := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  have rd₁₃ : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  have wr₁₃ : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  -- The encrypted MAC of the plaintext at `W + 96`.
  refine macTag_ok v L E₃ S₃ Ar.rounds (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn c₃ (y := 96)
    (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.of_eq rd₁₃ wr₁₃) fun s₄ E₄ rd₄ wr₄ f₄ _ h₄ => ?_
  have f₁₄ : Frame (mutR W SP D n) s₁.mem s₄.mem :=
    f₁₃.trans ((f₄.sub (tagR_wR W SP (by decide))).sub (wR_mut W SP D n))
  have rd₁₄ : s₄.rd = s.rd := by rw [rd₄, rd₁₃]
  have wr₁₄ : s₄.wr = s.wr := by rw [wr₄, wr₁₃]
  have f₀₄ : Frame (entryR W :: mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [argT_kept f₀₄ Ar.argsW Ar.argsD, hT]
  have hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₁₄, wr₁₄]; exact h
  refine WP.mono (openTail_ok L E₄ (slots_mut L Ar.data.w f₁₄ S₁) (Ar.data.of_eq rd₁₄ wr₁₄)
    (by rw [wr₁₄]; exact Ar.dw) (by have := Ar.t4; omega) Ar.t16 (saved_mut L Ar.data.w f₁₄ sv₁) hT₄ hTr₄
    (by rw [rd₁₄, wr₁₄]; exact hTc) Tb.w)
    fun s₅ ⟨hg₅, hsp₅, hax₅, hd₅, f₅⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₅ (.rbx, 112) (by decide)
    · exact hg₅ (.rbp, 120) (by decide)
    · rw [hsp₅, hsp]
    · exact hg₅ (.r12, 128) (by decide)
    · exact hg₅ (.r13, 136) (by decide)
    · exact hg₅ (.r14, 144) (by decide)
    · exact hg₅ (.r15, 152) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
      f₀₄.trans (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩)
    rw [hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    have c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₂'.sub (wR_mut W SP D n)), hK₁]
    have c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds f₁₃, hK₁]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₂', hent Ar.data]
    have a₃ : bytesAt s₃.mem A al = bytesAt s.mem A al := by rw [buf_mut Ar.aad Ar.ad f₁₃, hent Ar.aad]
    have p₃ : bytesAt s₃.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [h₃, c₂', d₂, crypt_eq (hBC _)]
    have p₄ : bytesAt s₄.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [buf_wR Ar.data (f₄.sub (tagR_wR W SP (by decide))), p₃]
    have hT : bytesAt s₄.mem T tl = bytesAt s.mem T tl := tag_kept Tb Ar.t16 f₀₄
    rw [c₃', a₃, p₃] at h₄
    have hY := congrArg List.length h₄
    rw [length_bytesAt, length_xorFrom] at hY
    have hl : (bytesAt s.mem N nl).length ≤ 15 := by rw [length_bytesAt]; have := Ar.h13; omega
    have hV : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl =
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
          (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))) := by
      rw [bytesAt_prefix s₄.mem _ Ar.t16, h₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16, ← mac_eq _ _ hl]
    have hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))).length = tl := by
      rw [mac_eq _ _ hl, List.length_take, ← hY]; have := Ar.t16; omega
    have key : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl ↔
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
          Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n)) := by
      rw [hV, hT, cryptTag_eq_iff (hBC _) Ar.t16 _ hML (length_bytesAt _ _ _), eq_comm]
    simp only [Spec.Ccm.decryptWith]
    by_cases hk : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))
    · have hk' := key.mpr hk
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte, p₄]⟩
    · have hk' : ¬ bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl := fun e => hk (key.mp e)
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte]⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp (v : UpdateImpl) {s : State} (h : openX86_64.pre s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  have A := args_of_open h
  open_wp' v A.1.1 A.1.2 A.2 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesCcm.X86_64

module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneShot

import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. `J₀` and the additional data
(AES-GCM's `oneAad`), the data encrypted (`oneCrypt`) and the tag of the
ciphertext (`oneTag 0`, `sealRun_ok`), copied to `tag` (AES-GCM's
`tagOut_ok`): GCM-AE (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ tagOut restore oneAad)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH gctr inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk SavedAt blockAt_frame bytesAt_frame ctxH_eq exit_ok ret_kept
  covers_left tagOut_ok padded_eq length_bytesAt)

/-- The argument at `[SP + 16]` (`tag`'s address) stays where it is, outside
`W`, the data and the stack below `SP`. -/
theorem arg16_disj {W D SP : Addr} {n k : Nat} (hk : 2 ≤ k)
    (dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩)
    {r : Region} (hr : r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN)) :
    (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 16, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := by
    rw [show (16 : Nat) = 8 + 8 by rfl, ← VG.Proof.AesGcm.X86_64.add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
  rcases hr with hr | hr | hr
  · exact (dA.sub_left hs).sub_right hr
  · exact (dAD.sub_left hs).sub_right hr
  · exact (Offset.disjoint_below SP (n := stkN) (d := 16) (k := 8) (by decide)).sub_right hr

/-- What `sealRun_ok` leaves, after the entry. -/
abbrev SealRunPost (s₀ : State) (Ctx W SP Np A D : Addr) (nl al n : Nat) (s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
    SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP stkN] s₀.mem s₄.mem ∧
    bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx)
      (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (bytesAt s₀.mem D n) ∧
    bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))

/-- After the entry, `seal` up to the tag at `W`: `oneAad`, `oneCrypt` and
`oneTag 0`. -/
theorem sealRun_ok (v : GcmImpl) {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 3 Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) s₁
      (SealRunPost s₀ Ctx W SP Np A D nl al n) := by
  unfold SealRunPost
  have L := C.lay
  have La := L.lay
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₂ M => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s₀.mem A al = a at M ⊢
  have hd₂ : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  refine WP.seq (WP.mono (oneCrypt_ok L (icb := inc32 (Spec.Gcm.j0 H iv)) (P := 0) rfl M.env M.dat M.len hd₂)
    fun s₃ ⟨cr, hrd₃, hwr₃⟩ => ?_)
  have hc0 : Ctr s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₂.mem Ctx) (inc32 (Spec.Gcm.j0 H iv)) 0 := Proof.Gcm.ctr_zero _ _ _ _ M.cb
  have hC₃ := cr.out hc0
  have f₃ : Frame (oneFrame W D SP n) s₂.mem s₃.mem := crFrame_one cr.frame
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₂.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  have dSt : ∀ d k, d + k ≤ 48 → ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) SP D n,
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hd₂.dw.ok.st.sub_right (Lay.stSub (by omega))).symm
    · exact La.st_st (.inl (by omega)) (by omega) (by decide)
    · exact (L.ks.sub_right (Lay.stSub (by omega))).symm
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame cr.frame fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide)), M.hH]
  have hJ₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [← M.j0]; simpa using blockAt_frame cr.frame (dSt 0 16 (by decide))
  have habs₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H (a ++ zeros (padLen a.length)) :=
    M.abs.congr (blockAt_frame cr.frame (dSt 16 16 (by decide)))
      (bytesAt_frame cr.frame (dSt 32 _ (by omega)) (by omega))
  have hx16 : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [kp 184 (.inl ⟨by decide, by decide⟩), M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hd₃ : DataOk (W + BitVec.ofNat 64 16) W SP s₃ D n :=
    C.data.dw.ok.of_eq (hrd₃.trans M.rd) (hwr₃.trans M.wr)
  refine WP.mono (oneTag_ok v L (o := 0) (.inl rfl) (N := n) hx16 cr.env hH₃
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact M.dat) (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact M.len)
    (by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact M.tlen) hlt hal₃ hd₃ C.dE C.data.dw.ctx)
    fun s₄ ⟨he₄, f₄, hrd₄, hwr₄, _, _, hT⟩ => ?_
  have f₄' : Frame (oneFrame W D SP n) s₃.mem s₄.mem := wFrame_one (.inl rfl) f₄
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx = ctxCiph s₀.mem Ctx := ciph_frame M.frame (dM _ _ La.cw' L.kc)
  have hc₃ : ciphOf s₃.mem Ctx = ctxCiph s₀.mem Ctx := (ciph_frame cr.frame (ctx_crFrame L hd₂)).trans hc₂
  have hp₂ : bytesAt s₂.mem D n = bytesAt s₀.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.stk) (by omega)
  have dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.stk.symm
  have hD₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n := bytesAt_frame f₄ dD (by omega)
  have hT₄ := hT habs₃
  rw [padded_eq, hJ₃, hc₃, ← hD₄, BitVec.add_zero] at hT₄
  refine ⟨he₄, hrd₄.trans (hrd₃.trans M.rd), hwr₄.trans (hwr₃.trans M.wr),
    (M.saved.frame f₃ (saved_oneFrame L C.dE)).frame f₄' (saved_oneFrame L C.dE), ?_,
    by rw [hD₄, hC₃, hc₂, hp₂, Proof.Gcm.gctr_eq], hT₄⟩
  refine (M.frame.sub fun r hr => ?_).trans ((f₃.trans f₄').sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩

/-- `a; (b; ((c; d); e))` from `(a; (b; c)); (d; e)`. -/
theorem WP.reassoc_seal {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) (.seq d e)) s Q) :
    WP isa (.seq a (.seq b (.seq (.seq c d) e))) s Q := by
  obtain ⟨t, s', ex, q⟩ := h
  cases ex with | seq ex₁ ex₂ => cases ex₁ with | seq ea ex₁ => cases ex₁ with | seq eb ec => cases ex₂ with
    | seq ed ee => exact ⟨_, _, .seq ea (.seq eb (.seq (.seq ec ed) ee)), q⟩

/-- `vg_sm4_gcm_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (hp : Proof.Sm4Gcm.sealX86_64.pre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ Proof.Sm4Gcm.sealX86_64.post s s' := by
  obtain ⟨C, hTw, d_td, d_tw, r_t, -⟩ := OneCtx.ofSeal hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hT' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := rfl
  have hwa := C.args 2 (by decide)
  have hta := C.args 1 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rsi = Np at *
  generalize hnl : (s.gpr .rdx).toNat = nl at *
  generalize hA : s.gpr .rcx = A at *
  generalize hal : (s.gpr .r8).toNat = al at *
  generalize hD : s.gpr .r9 = D at *
  generalize hn : (stackArg s 0).toNat = n at *
  generalize hT : stackArg s 1 = T at *
  generalize hW : stackArg s 2 = W at *
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW' hwa) fun s₁ E => ?_)
  refine WP.reassoc_seal (WP.seq (WP.mono (sealRun_ok v C E hNp hnl hal)
    fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => WP.seq ?_))
  -- The tag copied to `tag`.
  have dA : ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP stkN) →
      (⟨SP + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 16) 64 = T := by
    rw [he₄.rsp, f₄.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dA _ (.inl fun _ h => h)
      · exact dA _ (.inr (.inl fun _ h => h))
      · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT']
  obtain ⟨s₅, run₅, hb₅, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 16) he₄.r15 hT₄'
    (by rw [he₄.rsp, hrd₄, hwr₄]; exact hta) he₄.perm.w (by rw [hwr₄]; exact hTw)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have hsv₅ : SavedAt s₅.mem W s := hsv₄.frame f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (d_tw.sub_right (Lay.wSub (by decide))).symm
  have hret : s₅.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₅ (fun r hr => ?_), ret_kept f₄ (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact C.rW
      · exact C.rD
      · exact ret_stk SP
    · simp only [List.mem_singleton] at hr; subst hr; exact r_t
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact d_td.symm) (by omega)
  simp only [Proof.Sm4Gcm.sealX86_64, Proof.Sm4Gcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, Spec.Gcm.encryptWith, hm, hb₅, hT₄, hd₅, hC,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr, length_bytesAt, length_bytesAt]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.Sm4Gcm.X86_64

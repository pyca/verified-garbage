import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamVerifyCT

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.SealBody`. -/
section

/-!
# AES-GCM on x86-64: the body of `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. After `J₀` and the additional
data: the whole blocks encrypted and absorbed (`oneBlocks`), the rest
encrypted (`oneCrypt`), and the tag of the ciphertext (`oneTag 0`):
`sealBody_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The first 48 bytes of the state are outside `crypt`'s frame. -/
theorem st_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n) {d k : Nat}
    (hk : d + k ≤ 48) : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP D n,
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.st.sub_right (Lay.stSub (by omega))).symm
  · exact L.st_st (.inl (by omega)) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

omit L in
/-- A prefix of the data is outside `crypt`'s frame over the rest. -/
theorem pre_crFrame {s : State} {D : Addr} {n k : Nat} (hd : DataOk (W + BitVec.ofNat 64 16) W SP s D n)
    (hk : k ≤ n) : ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP (D + BitVec.ofNat 64 k) (n - k),
      (⟨D, k⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨D, k⟩ ⟨D, n⟩ := Region.sub_prefix hk
  have hlt := hd.lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using Offset.disjoint D (d := 0) (n := k) (e := k) (k := n - k) (.inl (by omega)) (by omega) (by omega)
  · exact (hd.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.stk.sub_right hs).symm

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The body of `seal`: the data encrypted from `icb`, and its tag. -/
theorem sealBody_ok {R : Nat} {D : Addr} {n al : Nat} {H icb : Block} {a : List Byte} {s : State}
    (h : ObPre Ctx W SP R D n s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hcb : blockAt s.mem (cbA W) = icb) (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))) :
    WP isa (.seq (.seq (oneBlocks v.callees.enc) (oneCrypt v.callees)) (oneTag v.callees 0)) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hR := h.rounds.2
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.seq (WP.mono (oneBlocksE_ok L v h) fun s₃ ⟨P, o₁, o₂, o₃⟩ => ?_))
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h P hH hcb habs hxa o₁ o₂
    (Z := bytesAt s₃.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega)
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  have hP : 16 * (n / 16) % 16 = 0 := by omega
  have hdw : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₃ (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    (h.data.of_eq P.rd P.wr).drop (by omega)
  have hlen₃ : s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) (by decide), hal]
  refine WP.mono (oneCrypt_ok v L (icb := icb) hP P.env hR₃ P.dat hlen₃ hdw) fun s₄ ⟨co, rd₄, wr₄⟩ => ?_
  have out₄ := co.out ct₃
  have g₄ := crFrame_one co.frame
  have hDW' := hdw.ok.w
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => g₄.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW' hd)
      (by decide)
  have hH₄ : blockAt s₄.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hdw r hr).sub_left (Lay.ctxSub (by decide))), hH₃]
  have abs₄ : Absorbed s₄.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))) := by
    have hl := Nat.mod_lt (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length
      (show 16 > 0 by decide)
    exact ab₃.congr (blockAt_frame co.frame (VG.Proof.AesGcm.X86_64.st_crFrame L hdw.ok (d := 16) (k := 16) (by decide)))
      (bytesAt_frame co.frame (VG.Proof.AesGcm.X86_64.st_crFrame L hdw.ok (d := 32) (by omega)) (by omega))
  have hX : (a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega
  refine WP.mono (oneTag_ok v L (o := 0) (al := al) (.inl rfl) hX co.env hH₄ co.rounds
    (by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact P.dat)
    (by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₃)
    (by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact P.tlen) hlt
    (by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hal₃) (hdw.ok.of_eq rd₄ wr₄) hDW' hdw.ctx)
    fun s₅ ⟨he₅, f₅, rd₅, wr₅, _, _, hq⟩ => ?_
  have T := hq abs₄
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' (by omega)]
  have dDw : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact h.data.ok.stk.symm
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ dDw (by omega)
  have hp₄ : bytesAt s₄.mem D (16 * (n / 16)) = bytesAt s₃.mem D (16 * (n / 16)) :=
    bytesAt_frame co.frame (VG.Proof.AesGcm.X86_64.pre_crFrame (h.data.ok.of_eq P.rd P.wr) (by omega)) (by omega)
  have hc₄ : ciphOf s₄.mem Ctx R = ciphOf s.mem Ctx R := by rw [ciph_frame co.frame (ctx_crFrame L hdw) hR, hc₃]
  have hJ₄ : blockAt s₄.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) := by
    rw [← hJ₃]; simpa using blockAt_frame co.frame (VG.Proof.AesGcm.X86_64.st_crFrame L hdw.ok (d := 0) (k := 16) (by decide))
  have hC : bytesAt s₅.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) := by
    rw [hd₅, split, split s.mem, hp₄, out₄, hw₃, hc₃, ht₃, Proof.Gcm.xorKs_append, length_bytesAt, Nat.zero_add]
  have eX : a ++ zeros (padLen a.length) ++ bytesAt s₃.mem D (16 * (n / 16)) ++
      bytesAt s₄.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s₅.mem D n := by
    rw [hd₅, split, hp₄, List.append_assoc]
  rw [eX, padded_eq, hc₄, hJ₄, show W + BitVec.ofNat 64 0 = W from BitVec.add_zero W] at T
  exact ⟨he₅, rd₅.trans (rd₄.trans P.rd), wr₅.trans (wr₄.trans P.wr),
    oneB_trans f₃ (oneB_trans (oneFrame_B (by omega) g₄)
      (oneFrame_B (k := 16 * (n / 16)) (by omega) (wFrame_one (o := 0) (.inl rfl) f₅))), hC, T⟩

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Seal`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. `J₀` and the additional data
(`oneAad`), the data encrypted (`oneCrypt`) and the tag of the ciphertext
(`oneTag 0`, `sealRun_ok`), copied to `tag` (`tagOut_ok`): GCM-AE (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

/-- What `seal` and `open` share: `J₀`, the additional data, and their
effects so far, from the entry. -/
structure OneMid (s₀ : State) (Ctx W SP D : Addr) (n : Nat) (H : Block) (iv a : List Byte) (mE : Mem) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r9
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, below SP 8] s₀.mem s.mem
  fr : Frame (wFrame W SP) mE s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem oneR_w {W SP : Addr} : ∃ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Region.Sub (oneR W) r :=
  ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

theorem wFrame_w {W SP : Addr} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame [⟨W, 2560⟩, below SP 8] m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- `oneAad`, after the entry. -/
theorem oneMid_ok (v : GcmImpl) {k : Nat} {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al) :
    WP isa (oneAad v.callees) s₁
      (VG.Proof.AesGcm.X86_64.OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  have hiv : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl := bytesAt_frame E.frame (dW _ _ C.nonce.w) (by have := C.nonce.lt; omega)
  have haa : bytesAt s₁.mem A al = bytesAt s.mem A al := bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega)
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (WP.with_rdwr (oneAad_ok v L E.env hH₁ (by rw [E.r12, hNp])
    (by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr)
    C.dE E.aad hal')) fun s₂ ⟨ao, hrd₂, hwr₂⟩ => ?_
  rw [hiv, haa] at ao
  have f₂ := wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (wFrame_cons ao.frame)
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  refine ⟨ao.env, ao.hH, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact E.rounds.1, E.rounds.2⟩,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact E.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact E.len,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact E.alen, ao.j0, ao.abs, ao.cb,
    E.saved.frame f₂ (saved_oneFrame L C.dE), ?_, ao.frame, hrd₂.trans E.rd, hwr₂.trans E.wr⟩
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.X86_64.oneR_w).trans
    (VG.Proof.AesGcm.X86_64.wFrame_w ao.frame)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

/-- The argument at `[SP + 24]` (`tag`'s address) stays where it is, outside
`W`, the data and the stack below `SP`. -/
theorem arg24_disj {W D SP : Addr} {n k : Nat} (hk : 3 ≤ k)
    (dA : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (dAD : (⟨SP + BitVec.ofNat 64 8, 8 * k⟩ : Region).Disjoint ⟨D, n⟩)
    {r : Region} (hr : r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 24)) :
    (⟨SP + BitVec.ofNat 64 24, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 24, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * k⟩ := by
    rw [show (24 : Nat) = 8 + 16 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega)
  rcases hr with hr | hr | hr
  · exact (dA.sub_left hs).sub_right hr
  · exact (dAD.sub_left hs).sub_right hr
  · exact (Offset.disjoint_below SP (n := 24) (d := 24) (k := 8) (by decide)).sub_right hr

/-- A region disjoint from what `open` writes before it compares the tags,
but for the data: `W` and the stack below `SP`. -/
def OutWS (W SP : Addr) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub (below SP 24) → X.Disjoint r

/-- A region disjoint from `W`, the data and the stack below `SP`. -/
def OutWDS (W D SP : Addr) (n : Nat) (X : Region) : Prop :=
  ∀ r : Region, r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 24) → X.Disjoint r

theorem OutWDS.ws {W D SP : Addr} {n : Nat} {X : Region} (h : VG.Proof.AesGcm.X86_64.OutWDS W D SP n X) : VG.Proof.AesGcm.X86_64.OutWS W SP X :=
  fun r hr => h r (hr.elim .inl fun h => .inr (.inr h))

theorem OutWS.tagFrame {W SP : Addr} {X : Region} (h : VG.Proof.AesGcm.X86_64.OutWS W SP X) {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Lay.wSub ho))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (below_sub (by decide) (by decide)))

theorem OutWDS.oneFrameB {W D SP : Addr} {n : Nat} {X : Region} (h : VG.Proof.AesGcm.X86_64.OutWDS W D SP n X) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrameB W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Region.sub_prefix (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr fun _ h => h))

theorem OutWDS.oneFrame {W D SP : Addr} {n : Nat} {X : Region} (h : VG.Proof.AesGcm.X86_64.OutWDS W D SP n X) :
    ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrame W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Region.sub_prefix (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr (below_sub (by decide) (by decide))))

/-- `OutWDS` for the data from byte `k` on. -/
theorem OutWDS.drop {W D SP : Addr} {n k : Nat} {X : Region} (h : VG.Proof.AesGcm.X86_64.OutWDS W D SP n X) (hk : k ≤ n) :
    VG.Proof.AesGcm.X86_64.OutWDS W (D + BitVec.ofNat 64 k) SP (n - k) X := fun r hr =>
  h r (hr.imp_right fun hr => hr.imp_left fun hs a ha =>
    Offset.sub_base D (d := k) (n := n - k) (k := n) (by omega) a (hs a ha))

/-- The address of `tag`, the argument at `[SP + 24]`, is outside `W`, the
data and the stack below `SP`. -/
theorem OneCtx.arg24 {s : State} {k : Nat} (hk : 3 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ :=
  fun _ hr => VG.Proof.AesGcm.X86_64.arg24_disj hk C.dA C.dAD hr

/-- `a; (b; (c; ((d; e); f)))` from `((a; (b; (c; d))); e); f`. -/
theorem WP.reassoc_seal {a b c d e f : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq (.seq a (.seq b (.seq c d))) e) f) s Q) :
    WP isa (.seq a (.seq b (.seq c (.seq (.seq d e) f)))) s Q := by
  obtain ⟨t, s', ex, q⟩ := h
  cases ex with | seq ex₁ ex₂ => cases ex₁ with | seq ex₁ ee => cases ex₁ with | seq ea ex₁ => cases ex₁ with
    | seq eb ex₁ => cases ex₁ with | seq ec ed => exact ⟨_, _, .seq ea (.seq eb (.seq ec (.seq (.seq ed ee) ex₂))), q⟩

/-- After the entry, `seal` up to the tag at `W`: `oneAad`, `oneBlocks`,
`oneCrypt` and `oneTag 0`. -/
theorem sealRun_ok (v : GcmImpl) {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks v.callees.enc) (.seq (oneCrypt v.callees) (oneTag v.callees 0))))
      s₁ fun s₄ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
        SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s₄.mem ∧
        bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat)
          (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (bytesAt s₀.mem D n) ∧
        bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (VG.Spec.Gcm.ghash (ctxH s₀.mem Ctx)
            (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
          ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) := by
  have L := C.lay
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.oneMid_ok v C E hNp hnl hal) fun s₂ M => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s₀.mem A al = a at M ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ M.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  have hal₂ : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq_assoc (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.X86_64.sealBody_ok v L (icb := inc32 (Spec.Gcm.j0 H iv)) (a := a)
    ⟨M.env, hRo, M.dat, M.len, hd₂, C.t_c, C.t_w, C.t_d, C.sp24⟩ M.hH M.cb hal₂ M.abs))
    fun s₄ ⟨⟨he₄, _, _, f₄, hC, hT₄⟩, hrd₄, hwr₄⟩ => ?_)
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx R = ctxCiph s₀.mem Ctx R :=
    ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₂ : bytesAt s₂.mem D n = bytesAt s₀.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by have := C.data.ok.lt; omega)
  rw [M.j0, hc₂] at hT₄
  refine ⟨he₄, hrd₄.trans M.rd, hwr₄.trans M.wr, M.saved.frame f₄ (saved_oneFrameB L C.dE C.t_w), ?_,
    by rw [hC, hc₂, hp₂, Proof.Gcm.gctr_eq], hT₄⟩
  refine (M.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

/-- `vg_aes_gcm_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.sealX86_64.pre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨C, hTw, d_td, d_tw, r_t⟩ := OneCtx.ofSeal hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s 3 := rfl
  have hT' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hwa := C.args 3 (by decide)
  have hta := C.args 2 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hD : stackArg s 0 = D at *
  generalize hn : (stackArg s 1).toNat = n at *
  generalize hT : stackArg s 2 = T at *
  generalize hW : stackArg s 3 = W at *
  have L := C.lay
  refine WP.seq (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW' hwa) fun s₁ E => ?_)
  refine WP.reassoc_seal (WP.seq (WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.sealRun_ok v C E hNp hnl hal)
    fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => ?_)))
  -- The tag copied to `tag`.
  have dA := C.arg24 (by decide)
  have hT₄' : s₄.mem.readW (s₄.gpr .rsp + BitVec.ofNat 64 24) 64 = T := by
    rw [he₄.rsp, f₄.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dA _ (.inl fun _ h => h)
      · exact dA _ (.inr (.inl fun _ h => h))
      · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT']
  obtain ⟨s₅, run₅, hb₅, f₅, hg₅, hrd₅, hwr₅⟩ := tagOut_ok (b := .rsp) (d := 24) he₄.r15 hT₄'
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
      · exact Offset.base_disjoint_below SP (n := 24) (k := 8) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact r_t
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  have hd₅ : bytesAt s₅.mem D n = bytesAt s₄.mem D n := bytesAt_frame f₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact d_td.symm) (by have := C.data.ok.lt; omega)
  simp only [Proof.AesGcm.sealX86_64, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, Spec.Gcm.encryptWith, hm, hb₅, hT₄, hd₅, hC,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr, length_bytesAt, length_bytesAt]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.OneCT`. -/
section

/-!
# AES-GCM on x86-64: the pieces of `seal` and `open` in two runs

Untrusted: everything here is checked by Lean. What stays in `W` between
the pieces (`OneS`: the rounds, the additional data's address and length,
the data's address and length) is the same in both runs, so each piece
(`oneAad`, `oneCrypt`, `oneTag`) leaks the same, by the fragments'
relations.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- What stays in `W` and the buffers between the pieces of `seal` and `open`. -/
structure OneS (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  dA : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  dD : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  /-- The total length, once `oneBlocks` has kept it. -/
  tlen : ∀ N, T = some N → s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem OneS.frame {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) s.mem s'.mem) : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len,
    h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr, fun N hN => by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen N hN⟩

omit L in
theorem OneS.keep {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.rounds, by rw [hm]; exact h.aad, by rw [hm]; exact h.alen,
    by rw [hm]; exact h.dat, by rw [hm]; exact h.len, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr,
    fun N hN => by rw [hm]; exact h.tlen N hN⟩

omit L in
/-- Two slots of `W` loaded, and a constant. -/
theorem load2_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
        s₁.gpr .rbx = BitVec.ofNat 64 0 := by
  have h15 := h.env.r15
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 o₁)),
      .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)] s = some s₁ ∧ s₁.gpr .r12 = P ∧
      s₁.gpr .rbp = BitVec.ofNat 64 k ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h₁]
    · simp [gpr_setReg, h₂]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, h12, hbp, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)

omit L in
/-- A length's slot, modulo 16, into `rbx`. -/
theorem mod16_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s : State}
    (h : VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s) {o : Nat} {k : Nat} (ho : (o = alenO ∧ k = al) ∨ (o = lenO ∧ k = n)) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 o)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (k % 16) := by
  have he := h.env
  have hk : k < 2 ^ 64 := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [h.dA.lt, h.dD.ok.lt]
  have hand := and15 (BitVec.ofNat 64 k)
  rw [toNat_ofNat_of_lt hk, imm_eq (by decide)] at hand
  have hs : s.mem.readW (W + BitVec.ofNat 64 o) 64 = BitVec.ofNat 64 k := by
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [h.alen, h.len]
  have ro : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o) 8 := by
    rcases ho with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact he.perm.wR (show 184 + 8 ≤ 2560 by decide)
    · exact he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have h15 := he.r15
  obtain ⟨s₁, run₁, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 o)),
      .alu .and .rbx (imm 15)] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (k % 16) ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, ro], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hs, hand]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem w_one {D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') : Frame (VG.Proof.AesGcm.X86_64.oneFrame W D SP n) m m' :=
  wFrame_one (o := 0) (.inl rfl) (wFrame_cons h)

/-- Two runs in `OneS` for the same parameters. -/
abbrev OneS₂ (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s₁ s₂ : State) :
    Prop :=
  VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₂

omit L in
theorem OneS₂.env {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s₁ s₂ : State}
    (h : VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T s₁ s₂) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  env_agree h.1.env h.2.env

/-- The additional data, absorbed and padded. -/
theorem aadRest_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
      (.seq (absorb v.callees 16) (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)])
        (flush v.callees 16)))) (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T) := by
  have hL : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    VG.Proof.AesGcm.X86_64.load2_ok h h.aad h.alen (h.env.perm.wR (show 232 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 184 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = A ∧
    s.gpr .rbp = BitVec.ofNat 64 al ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] A al s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dA, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorb v.callees 16) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (absorb_ok v L (.inr rfl) (ai s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (VG.Proof.AesGcm.X86_64.w_one (absFrame_one o.frame))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := A) (n := al) rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  have hM : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (al % 16) :=
    fun s h => VG.Proof.AesGcm.X86_64.mod16_ok h (.inl ⟨rfl, rfl⟩)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hM hM
  have hF : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s ∧ s.gpr .rbx = BitVec.ofNat 64 (al % 16) →
      WP isa (flush v.callees 16) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (x := List.replicate al 0) ⟨h.1.env, rfl⟩
      (by simpa using h.2))) fun _ ⟨o, hrd, hwr⟩ => h.1.frame L o.env hrd hwr hDW (VG.Proof.AesGcm.X86_64.w_one (tFrame_one o.frame))
  have d := rel_wp ((flush_rel v L (.inr rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (al % 16)) ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (al % 16)))
      (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  exact (RelCT.seq a (RelCT.seq b (RelCT.seq c d))).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `J₀` of the nonce, and the additional data. -/
theorem oneAad_rel {R : Nat} {Np A : Addr} {nl al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = Np ∧ s₁.gpr .rbp = BitVec.ofNat 64 nl ∧
        DataOk (W + BitVec.ofNat 64 16) W SP s₁ Np nl) ∧ (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₂ ∧ s₂.gpr .r12 = Np ∧
        s₂.gpr .rbp = BitVec.ofNat 64 nl ∧ DataOk (W + BitVec.ofNat 64 16) W SP s₂ Np nl))
      (oneAad v.callees) (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T) := by
  have ji : ∀ s, (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) →
      J0In Ctx (W + BitVec.ofNat 64 16) W SP (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) Np nl s :=
    fun s h => ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have hJ : ∀ s, (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) → WP isa (j0 v.callees) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T) :=
    fun s h => WP.mono (WP.with_rdwr (j0_ok v L (ji s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (VG.Proof.AesGcm.X86_64.w_one (j0Frame_one o.frame))
  have a := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      j0_rel v L (H₁ := H₁) (H₂ := H₂) (Np := Np) (n := nl)).mono
      (fun _ _ h => ⟨_, _, ji _ h.1, ji _ h.2⟩) fun _ _ h => h) (fun _ _ h => h) hJ hJ
  exact RelCT.seq a ((VG.Proof.AesGcm.X86_64.aadRest_rel v L hDW).mono (fun _ _ h => h.2) fun _ _ h => h)

/-- The data encrypted or decrypted. -/
theorem oneCrypt_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T) (oneCrypt v.callees) (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n T) := by
  have hL : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    VG.Proof.AesGcm.X86_64.load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let CI : State → Prop := fun s => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ci : ∀ s, CI s → CrIn Ctx (W + BitVec.ofNat 64 16) W SP R 0 0 D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD, h.1.rounds⟩
  have hC : ∀ s, CI s → WP isa (crypt v.callees) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (crypt_ok v L (ci s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (crFrame_one o.frame)
  have b := rel_wp ((crypt_rel v L (R := R) (icb₁ := 0) (icb₂ := 0) (P₁ := 0) (P₂ := 0) (D := D) (n := n) rfl).mono
      (P' := fun s₁ s₂ => True ∧ CI s₁ ∧ CI s₂) (fun _ _ h => ⟨ci _ h.2.1, ci _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hC hC
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The tag of the data (as ciphertext) into `W + o`. -/
theorem oneTag_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {N : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n (some N)) (oneTag v.callees o) fun _ _ => True := by
  have hL : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    VG.Proof.AesGcm.X86_64.load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD.ok, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorb v.callees 16) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N)) := fun s h =>
    WP.mono (WP.with_rdwr (absorb_ok v L (.inr rfl) (ai s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (VG.Proof.AesGcm.X86_64.w_one (absFrame_one o.frame))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  have hM : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .rbx (.mem (at_ .r15 lenO)),
      .alu .and .rbx (imm 15)]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) :=
    fun s h => VG.Proof.AesGcm.X86_64.mod16_ok h (.inr ⟨rfl, rfl⟩)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n (some N) s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hM hM
  have hF : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s ∧ s.gpr .rbx = BitVec.ofNat 64 (n % 16) →
      WP isa (flush v.callees 16) s (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N)) := fun s h =>
    WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (x := List.replicate n 0) ⟨h.1.env, rfl⟩
      (by simpa using h.2))) fun _ ⟨o, hrd, hwr⟩ => h.1.frame L o.env hrd hwr hDW (VG.Proof.AesGcm.X86_64.w_one (tFrame_one o.frame))
  have d := rel_wp ((flush_rel v L (.inr rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16)) ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (n % 16)))
      (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  -- The lengths, for `tag`.
  have hT : ∀ s, VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))]) s fun s₁ => VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N := fun s h => by
    have q₁ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have q₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have h15 := h.env.r15
    obtain ⟨s₁, run₁, hbx, hbp, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧
        s₁.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.alen]
      · simp [gpr_setReg, h.tlen N rfl]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx, hbp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ VG.Proof.AesGcm.X86_64.OneS₂ Ctx W SP R A al D n (some N) s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hT hT
  have t := (tag_rel v L (R := R) ho).mono (P' := fun (s₁ s₂ : State) => True ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N) ∧
      (VG.Proof.AesGcm.X86_64.OneS Ctx W SP R A al D n (some N) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 al ∧ s₂.gpr .rbp = BitVec.ofNat 64 N))
    (fun _ _ h => ⟨⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩, h.2.1.1.rounds, h.2.2.1.rounds⟩) fun _ _ h => h
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d (RelCT.seq e t))))

end

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Undo`. -/
section

/-!
# AES-GCM on x86-64: `oneUndo`

Untrusted: everything here is checked by Lean. When the tag is wrong, `open`
encrypts again the whole blocks `oneBlocks` decrypted, with `vg_aes_ctr32`
from the counter block at the state's start (`oneUndo_ok`), which `tag` left
there.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)

/-- The blocks of `oneUndo`. -/
abbrev undoB1 : List Instr :=
  [.mov .rax (.mem (at_ .r15 tlenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15),
    .alu .sub .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 dataO)), .alu .sub .rcx (.reg .rax),
    .shift .shr .rax 4, .mov .r8 (.reg .rax), .alu .test .rax (.reg .rax)]
abbrev undoB2 : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] : List Instr) ++
    ptr .r9 .r15 scrO

theorem oneUndo_eq (c : Callees) : oneUndo c = .seq (.block VG.Proof.AesGcm.X86_64.undoB1) (.ite .e (.block [])
    (.seq (.block VG.Proof.AesGcm.X86_64.undoB2) (.call c.ctr.name c.ctr.code))) := rfl

/-- What `oneUndo` writes: the counter block, the whole blocks, the working
space and the stack. -/
abbrev undoFrame (W SP D : Addr) (q : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16 * q⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8]

section
variable {Ctx W SP : Addr}

/-- The data's start and its number of whole blocks. -/
theorem undo1_ok {D : Addr} {n : Nat} (hn : n < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))) :
    WP isa (.block VG.Proof.AesGcm.X86_64.undoB1) s fun s₁ => s₁.gpr .rcx = D ∧ s₁.gpr .r8 = BitVec.ofNat 64 (n / 16) ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have e15 := and15 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [ofNat_sub (Nat.mod_le _ _) hn]; congr 1; omega
  have ed : D + BitVec.ofNat 64 (16 * (n / 16)) - BitVec.ofNat 64 (16 * (n / 16)) = D := BitVec.add_sub_cancel _ _
  have h4 := shr4 (16 * (n / 16)) (by omega)
  rw [show 16 * (n / 16) / 16 = n / 16 by omega] at h4
  have hz := and_self_beq (show n / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, htl, hdat, e15, esub, ed, h4], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, ed]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, h4, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

variable (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The arguments of `oneUndo`'s call of `vg_aes_ctr32`. -/
theorem undo2_ok {R : Nat} {D : Addr} {n : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hR : RoundsAt s.mem W R) (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (hcx : s.gpr .rcx = D)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 (n / 16)) :
    WP isa (.block VG.Proof.AesGcm.X86_64.undoB2) s fun s₂ => CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have h13 := he.r13; have h14 := he.r14; have h15 := he.r15
  have r₃ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have hR₁ : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R := hR.1
  obtain ⟨s₂, run₂, hdi, hsi, hdx, h9, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa VG.Proof.AesGcm.X86_64.undoB2 s = some s₂ ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 16 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [h13, h14, h15, r₃, hR₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, h13]
    · simp [gpr_setReg, gpr_arithFlags, h15, hR₁]
    · simp [gpr_setReg, gpr_arithFlags, h14]
    · simp [gpr_setReg, gpr_arithFlags, h15, imm_eq, scrO]
    · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  have hq : 16 * (n / 16) ≤ n := by omega
  have hdq := (hd.of_eq hrd₂ hwr₂).take hq
  have hS : (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  have kc : (⟨Ctx, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16, 16⟩ := by
    simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide))
  have cd : (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint ⟨D, 16 * (n / 16)⟩ := by
    have := hdq.ok.st.sub_right (Lay.stSub (St := W + BitVec.ofNat 64 16) (d := 0) (n := 16) (by decide))
    simpa using this.symm
  have hcall : CtrCall s₂ Ctx (W + BitVec.ofNat 64 16) D (W + BitVec.ofNat 64 512) R (n / 16) := by
    refine ⟨hdi, hsi, hdx, by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hcx,
      by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide)]; exact h8, h9, hR.2,
      by have := hd.ok.wrap; omega, kc, hdq.ctx.sub_left (Region.sub_prefix (show 240 ≤ 256 by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      cd, hS, hdq.ok.w.sub_right (Lay.wSub (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
    · rw [hk]; simpa using L.stk_st (a := 0) (n := 16) (by decide)
    · rw [hk]; exact hdq.ok.stk
    · rw [hk]; exact L.stk_w (by decide)
    · refine covers_cons ?_ (covers_cons ?_ (covers_cons hdq.ok.rd (covers_left (he₂.perm.wC (by decide)))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using covers_left (he₂.perm.stC (d := 0) (n := 16) (by decide))
    · exact covers_cons (by simpa using he₂.perm.stC (d := 0) (n := 16) (by decide))
        (covers_cons hdq.wr (he₂.perm.wC (by decide)))
  exact ⟨hcall, he₂, hm₂, hrd₂, hwr₂⟩

/-- `oneUndo`: counter mode over the whole blocks of the data, from the
counter block at the state's start. -/
theorem oneUndo_ok (c : Callees) (v : Proof.Aes.X86_64.Ctr32Impl) (hc : c.ctr = ⟨v.callee.name, v.callee.code⟩)
    {R : Nat} {D : Addr} {n : Nat} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)))
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) :
    WP isa (oneUndo c) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesGcm.X86_64.undoFrame W SP D (n / 16)) s.mem s'.mem ∧
      blocksAt s'.mem D (n / 16) = ctr32 (ciphOf s.mem Ctx R) (blockAt s.mem (W + BitVec.ofNat 64 16))
        (blocksAt s.mem D (n / 16)) ∧
      blockAt s'.mem (W + BitVec.ofNat 64 16) =
        Nat.repeat Spec.Gcm.inc32 (n / 16) (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
  have hn := hd.ok.lt
  rw [VG.Proof.AesGcm.X86_64.oneUndo_eq]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.undo1_ok hn he htl hdat) fun s₁ ⟨hcx, h8, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨he₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [hz, m₁]; rfl
    · rw [hz, m₁]; rfl
  · simp only [decide_eq_false_iff_not] at hz
    refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.undo2_ok L he₁ ⟨by rw [m₁]; exact hR.1, hR.2⟩ (hd.of_eq rd₁ wr₁) hcx h8)
      fun s₂ ⟨hcall, he₂, hm₂, hrd₂, hwr₂⟩ => ?_)
    have hk := he₂.rsp
    rw [hc]
    refine WP.mono (ctr_call v hcall) fun s₃ g => ?_
    refine ⟨he₂.of_saved g.saved g.rd g.wr, g.rd.trans (hrd₂.trans rd₁), g.wr.trans (hwr₂.trans wr₁), ?_, ?_, ?_⟩
    · rw [← m₁, ← hm₂, ← hk]; exact g.frame
    · rw [g.out, hm₂, m₁]
    · rw [g.ctr, hm₂, m₁]
end

theorem undo_B {W D SP : Addr} {n : Nat} {m m' : Mem} (h : Frame (VG.Proof.AesGcm.X86_64.undoFrame W SP D (n / 16)) m m') :
    Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W, 128⟩, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩

end VG.Proof.AesGcm.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.X86_64.Open`. -/
section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. A tag length §5.2.1.2 does
not allow gives 0. Any other: `J₀` and the additional data (`oneAad`), the
whole blocks decrypted and absorbed (`oneBlocks`), the tag of the ciphertext
(`oneTag 112`), the received tag, read from `tag`, padded (`recv`) and
compared (`cmp 112`),
and if they match the rest decrypted (`oneCrypt`), and if not the whole
blocks encrypted again (`oneUndo`): GCM-AD (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `OneEntry`, after code that writes only the tag length's slot. -/
theorem OneEntry.keep {s₀ s s' : State} {A D : Addr} {n : Nat} (E : OneEntry s₀ Ctx W SP A D n s)
    (hg : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneEntry s₀ Ctx W SP A D n s' := by
  have kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  refine ⟨E.env.keep (fun r hr => ?_) hrd hwr, ⟨by rw [kp 176 (.inl (by decide)) (by decide)]; exact E.rounds.1,
    E.rounds.2⟩, by rw [kp 232 (.inr (by decide)) (by decide)]; exact E.aad,
    by rw [kp 184 (.inl (by decide)) (by decide)]; exact E.alen, by rw [kp 200 (.inl (by decide)) (by decide)]; exact E.dat,
    by rw [kp 208 (.inl (by decide)) (by decide)]; exact E.len, by rw [hg _ (by simp)]; exact E.r12,
    by rw [hg _ (by simp)]; exact E.rbp, by rw [hg _ (by simp)]; exact E.rsp,
    E.saved.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
    E.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩), hrd.trans E.rd, hwr.trans E.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by simp)

end

/-- The entry of `open`, and the tag length kept at `W + 224`. -/
theorem openEntry_ok {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 5 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .r8 = A)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W) :
    WP isa (.block (oneEntry 40 ++ ([.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx] : List Instr))) s
      fun s₁ => OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 3 ∧
        s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 3 ∧ Frame [oneR W] s.mem s₁.mem := by
  have L := C.lay
  have a₄ := C.args 4 (by decide)
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW a₄) fun s₁ E => ?_)
  have a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [E.rd, E.wr]; exact C.args 3 (by omega)
  have ht : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = stackArg s 3 := by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 32, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 5⟩ := by
        rw [show (32 : Nat) = 8 + 24 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    rfl
  have w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 32)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 3 ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 3) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₃, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, ht]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, ht]
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₂, run₂, E.keep L (fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hrd₂ hwr₂ f₂, hbx₂,
    by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  exact E.frame.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem ite_ofNat (p : Prop) [Decidable p] :
    (if p then 1 else 0 : BitVec 64) = BitVec.ofNat 64 (if p then 1 else 0) := by split <;> rfl

/-- After the comparison, from `s`: `k` is 1 if the tag of the ciphertext `T`
matches the received one, and 0 if not, in ZF and at `W + 216`; the counter
block kept, and the first one (after `J₀ = J`) at the state's start. -/
structure OpenMid (Ctx W SP : Addr) (J : Block) (k : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  frame : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cb : blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)
  zf : s'.zf = some (decide (k = 0))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  j : blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 J

/-- After the comparison, from `s` after `oneAad`: `k` is 1 if the tags match
and 0 if not, the whole blocks `X` decrypted from the counter block after
`J₀ = J`, the counter after them, and what `oneEnd` needs. -/
structure OpenFront (Ctx W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (J : Block) (X : List Byte) (k : Nat)
    (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  frame : Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  rounds : RoundsAt s'.mem W R
  tlen : s'.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s'.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16))
  len : s'.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16))
  zf : s'.zf = some (decide (k = 0))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k
  j : blockAt s'.mem (W + BitVec.ofNat 64 16) = inc32 J
  cb : blockAt s'.mem (cbA W) = Nat.repeat inc32 (n / 16) (inc32 J)
  whole : bytesAt s'.mem D (16 * (n / 16)) = xorKs (ciphOf s'.mem Ctx R) (inc32 J) 0 X
  tail : bytesAt s'.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
    bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
  ciph : ciphOf s'.mem Ctx R = ciphOf s.mem Ctx R

/-- The tag of the ciphertext (`x`, absorbed, then the `n` bytes at `D`, of `N`
in all), compared with the received one. -/
theorem openCheckA_ok {R t : Nat} {D : Addr} {n N al : Nat} {H J : Block} {x : List Byte}
    (hx16 : x.length % 16 = 0) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hN₁ : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (habs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x)
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J) {Tp : Addr}
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : VG.Proof.AesGcm.X86_64.OutWS W SP ⟨Tp, t⟩)
    (oA : VG.Proof.AesGcm.X86_64.OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv
      (.seq (cmp uO)
        (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))) s
      (VG.Proof.AesGcm.X86_64.OpenMid Ctx W SP J (if (toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (x ++ bytesAt s.mem D n ++
          zeros (padLen (x ++ bytesAt s.mem D n).length))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R J)).take t = bytesAt s.mem Tp t then 1 else 0) s) := by
  have hlt := hd.ok.lt
  have hR' := hR.2
  -- The tag.
  refine WP.seq (WP.mono (oneTag_ok v L (o := 112) (al := al) (.inr rfl) hx16 he hH hR hdat hlen hN₁ hN hal hd.ok hDW
    hd.ctx) fun s₃ ⟨he₃, f₃, hrd₃, hwr₃, hcb₃, hj₃, hq⟩ => ?_)
  have hT₃ := hq habs
  rw [hj] at hT₃
  generalize hT : toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (x ++ bytesAt s.mem D n ++
    zeros (padLen (x ++ bytesAt s.mem D n).length)))) [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R J) = T
    at hT₃ ⊢
  have f₃' := wFrame_one (D := D) (n := n) (.inr rfl) f₃
  have kp₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => f₃'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd')
      (by decide)
  have hTp₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t :=
    bytesAt_frame f₃ (oT.tagFrame (o := 112) (by decide)) (by omega)
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [f₃.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (oA.tagFrame (o := 112) (by decide))
      (by decide), hTa]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kp₃ 224 (.inr ⟨by decide, by decide⟩)]; exact htl
  have q₁ := he₃.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have q₂ : InRegions (s₃.rd ++ s₃.wr) (SP + BitVec.ofNat 64 24) 8 := by rw [hrd₃, hwr₃]; exact hTar
  obtain ⟨s₄, run₄, hbx₄, hsi₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s₃ = some s₄ ∧ s₄.gpr .rbx = BitVec.ofNat 64 t ∧ s₄.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [he₃.r15, he₃.rsp, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₃]
    · simp [gpr_setReg, hTa₃]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide)) hrd₄ hwr₄
  -- The received tag, padded.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok he₄ hbx₄ h1 h16 hsi₄
    (by rw [hrd₄, hrd₃, hwr₄, hwr₃]; exact hTr) (oT _ (.inl (Lay.wSub (by decide))))))
    fun s₅ ⟨⟨he₅, hr₅, f₅, hbx₅⟩, hrd₅, hwr₅⟩ => ?_)
  rw [hbx₄] at hbx₅
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (o := 112) (.inr rfl) he₅ hbx₅ h1 h16 (length_bytesAt _ _ _) hr₅))
    fun s₆ ⟨⟨he₆, hax₆, f₆⟩, hrd₆, hwr₆⟩ => ?_)
  have d256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hU : bytesAt s₅.mem (W + BitVec.ofNat 64 112) t = T.take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₅ d256 (by decide), hm₄, hT₃]
  rw [hU, hm₄, hTp₃, VG.Proof.AesGcm.X86_64.ite_ofNat] at hax₆
  generalize hk : (if T.take t = bytesAt s.mem Tp t then 1 else 0) = k at hax₆
  have hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  have w₇ := he₆.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₇, run₇, hz₇, hg₇, hm₇, hrd₇, hwr₇⟩ : ∃ s₇, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₆ = some s₇ ∧ s₇.zf = some (decide (k = 0)) ∧ (∀ r, s₇.gpr r = s₆.gpr r) ∧
      s₇.mem = s₆.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by xrun [he₆.r15, w₇], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₆, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₆]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇ := he₆.keep (fun r _ => hg₇ r) hrd₇ hwr₇
  have g₇ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩]
      s₃.mem s₇.mem := by
    have g₅ := f₅.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have g₆ := f₆.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    rw [hm₄] at g₅
    rw [hm₇]
    exact (g₅.trans g₆).writeW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  have f₇ : Frame (wFrame W SP) s₃.mem s₇.mem := g₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  have F₇ : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s₇.mem := f₃.trans (wFrame_cons f₇)
  have hcb₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [add_ofNat_assoc]
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)), hcb₃]
  have hj₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = inc32 J := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)), hj₃, hj]
  have hrd₇' : s₇.rd = s.rd := hrd₇.trans (hrd₆.trans (hrd₅.trans (hrd₄.trans hrd₃)))
  have hwr₇' : s₇.wr = s.wr := hwr₇.trans (hwr₆.trans (hwr₅.trans (hwr₄.trans hwr₃)))
  have hax₇ : s₇.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₇, Mem.readW_writeW_self64]
  subst hk hT
  exact ⟨he₇, F₇, hrd₇', hwr₇', hcb₇, hz₇, hax₇, hj₇⟩

omit L in
theorem WP.seq6 {a b c d e f T : Prog isa} {s : State} {P Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq c (.seq d (.seq e f))))) s P) (k : ∀ s', P s' → WP isa T s' Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f T)))))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq5 h k)

/-- After the comparison: the rest decrypted if the tags match (`k ≠ 0`), and
the whole blocks (`X` before `oneBlocks`) encrypted again if not, and the
result. -/
theorem openEnd_ok {R n k : Nat} {D : Addr} {J : Block} {X : List Byte} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D + BitVec.ofNat 64 (16 * (n / 16)))
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)))
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (hz : s.zf = some (decide (k = 0))) (hax : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = inc32 J)
    (hcb : blockAt s.mem (cbA W) = Nat.repeat inc32 (n / 16) (inc32 J))
    (hw : bytesAt s.mem D (16 * (n / 16)) = xorKs (ciphOf s.mem Ctx R) (inc32 J) 0 X) :
    WP isa (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees)) (.block [.mov .rax (.mem (at_ .r15 auxO))])) s
      fun s' => Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s'.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rax = BitVec.ofNat 64 k ∧
        bytesAt s'.mem D n = if k = 0 then X ++ bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
          else xorKs (ciphOf s.mem Ctx R) (inc32 J) 0
            (X ++ bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))) := by
  have hlt := hd.ok.lt
  have hD := hd.ok.w
  have hq : 16 * (n / 16) ≤ n := by omega
  have hXl : X.length = 16 * (n / 16) := by
    have := congrArg List.length hw; rw [length_bytesAt, Proof.Gcm.length_xorKs] at this; omega
  have hdw := hd.drop hq
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' hq]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧
      Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s₈.mem ∧ s₈.rd = s.rd ∧ s₈.wr = s.wr ∧
      s₈.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      bytesAt s₈.mem D n = if k = 0 then X ++ bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
        else xorKs (ciphOf s.mem Ctx R) (inc32 J) 0
          (X ++ bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))))
    (WP.ite (decide (k = 0)) (eval_e hz) (fun ht => ?_) (fun hf => ?_)) fun s₈ h₈ => ?_)
  · -- The tags differ: the whole blocks encrypted again.
    have h0 : k = 0 := by simpa using ht
    refine WP.mono (VG.Proof.AesGcm.X86_64.oneUndo_ok L v.callees v.ctr rfl he hR htl hdat hd) fun s₈ ⟨he₈, rd₈, wr₈, f₈, o₈, c₈⟩ =>
      ⟨he₈, VG.Proof.AesGcm.X86_64.undo_B f₈, rd₈, wr₈, ?_, ?_⟩
    · rw [f₈.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact ((hD.sub_left (Region.sub_prefix hq)).sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
    · simp only [h0, ↓reduceIte]
      have cw := Proof.Gcm.ctr_whole (ks := W + BitVec.ofNat 64 16) (icb := inc32 J) (n := 0)
        ⟨hj, fun h => absurd rfl h⟩ rfl o₈ c₈
      have ht₈ : bytesAt s₈.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        refine bytesAt_frame f₈ (fun r hr => ?_) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using hdw.ok.st.sub_right (Lay.stSub (St := W + BitVec.ofNat 64 16) (d := 0) (n := 16) (by decide))
        · simpa using Offset.disjoint D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (e := 0) (k := 16 * (n / 16))
            (.inr (by omega)) (by omega) (by omega)
        · exact hdw.ok.w.sub_right (Lay.wSub (by decide))
        · exact hdw.ok.stk.symm
      rw [split s₈.mem, cw.1, hw, ← Proof.Gcm.gctr_eq, ← Proof.Gcm.gctr_eq, Proof.Gcm.gctr_gctr, ht₈]
  · -- The tags match: the rest decrypted.
    have h0 : k ≠ 0 := by simpa using hf
    refine WP.mono (oneCrypt_ok v L (icb := inc32 J) (P := 16 * (n / 16)) (by omega) he hR hdat hlen hdw)
      fun s₈ ⟨co, rd₈, wr₈⟩ => ⟨co.env, oneFrame_B hq (crFrame_one co.frame), rd₈, wr₈, ?_, ?_⟩
    · rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hdw.ok.w.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
    · simp only [h0, ↓reduceIte]
      have out := co.out ⟨by rw [hcb]; congr 1; omega, fun h => absurd (by omega) h⟩
      rw [split s₈.mem, bytesAt_frame co.frame (VG.Proof.AesGcm.X86_64.pre_crFrame hd.ok hq) (by omega), hw, out,
        Proof.Gcm.xorKs_append, hXl, Nat.zero_add]
  obtain ⟨he₈, f₈, hrd₈, hwr₈, hax₈, hD₈⟩ := h₈
  have q₉ := he₈.perm.wR (show 216 + 8 ≤ 2560 by decide)
  refine WP.run (Q := fun s₉ => s₉.gpr .rax = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rax → s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr)
    ⟨_, by xrun [he₈.r15, q₉], by simp [gpr_setReg, hax₈], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
    fun s₉ ⟨hax₉, hg₉, hm₉, hrd₉, hwr₉⟩ => ?_
  exact ⟨he₈.keep (fun r hr => hg₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₉ hwr₉, by rw [hm₉]; exact f₈,
    by rw [hrd₉, hrd₈], by rw [hwr₉, hwr₈], hax₉, by rw [hm₉]; exact hD₈⟩

/-- After `oneAad`: the whole blocks decrypted and absorbed, and the tag of the
ciphertext compared with the received one. -/
theorem openFront_ok {R t : Nat} {D : Addr} {n al : Nat} {H J : Block} {a : List Byte} {s : State}
    (h : ObPre Ctx W SP R D n s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J) (hcb : blockAt s.mem (cbA W) = inc32 J) {Tp : Addr}
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨Tp, t⟩)
    (oA : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv
      (.seq (cmp uO)
        (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))) s
      (VG.Proof.AesGcm.X86_64.OpenFront Ctx W SP R D n J (bytesAt s.mem D (16 * (n / 16)))
        (if (toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (padded a (bytesAt s.mem D n))))
          [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R J)).take t = bytesAt s.mem Tp t then 1 else 0) s) := by
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hR := h.rounds.2
  have hq : 16 * (n / 16) ≤ n := by omega
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (oneBlocksD_ok L v h) fun s₃ ⟨P, o₁, o₂, o₃⟩ => ?_)
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h P hH hcb habs hxa o₁ o₂
    (Z := bytesAt s.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega)
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' hq]
  have hdw := (h.data.of_eq P.rd P.wr).drop hq
  have hlen₃ : s₃.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 (n - 16 * (n / 16)) := by
    rw [P.len]; congr 1; omega
  have kp₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrameB L hD h.t_w hd)
      (by decide)
  have hT₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t := bytesAt_frame f₃ oT.oneFrameB (by omega)
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp := by
    rw [f₃.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) oA.oneFrameB (by decide), hTa]
  have hX : (a ++ zeros (padLen a.length) ++ bytesAt s.mem D (16 * (n / 16))).length % 16 = 0 := by
    rw [List.length_append, length_bytesAt]; omega
  refine WP.mono (VG.Proof.AesGcm.X86_64.openCheckA_ok v L (x := a ++ zeros (padLen a.length) ++ bytesAt s.mem D (16 * (n / 16))) (N := n)
    hX P.env hH₃ hR₃ P.dat hlen₃ P.tlen hlt (by rw [kp₃ 184 (.inl ⟨by decide, by decide⟩)]; exact hal)
    (by rw [kp₃ 224 (.inr ⟨by decide, by decide⟩)]; exact htl) h1 h16 hdw hdw.ok.w ab₃ (hJ₃.trans hj) hTa₃
    (by rw [P.rd, P.wr]; exact hTar) (by rw [P.rd, P.wr]; exact hTr) oT.ws oA.ws) fun s₇ M => ?_
  have eT : a ++ zeros (padLen a.length) ++ bytesAt s.mem D (16 * (n / 16)) ++
      bytesAt s₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      a ++ zeros (padLen a.length) ++ bytesAt s.mem D n := by
    rw [ht₃, List.append_assoc, ← split]
  rw [eT, padded_eq, hc₃, hT₃] at M
  have F₇' := wFrame_one (D := D + BitVec.ofNat 64 (16 * (n / 16))) (n := n - 16 * (n / 16)) (.inr rfl) M.frame
  have kp₇ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => F₇'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L hdw.ok.w hd') (by decide)
  have dC : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  have dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact hD.sub_right (Lay.wSub (by decide))
    · exact h.data.ok.stk.symm
  have hc₇ : ciphOf s₇.mem Ctx R = ciphOf s₃.mem Ctx R := ciph_frame M.frame dC hR
  have hp₇ : bytesAt s₇.mem D (16 * (n / 16)) = bytesAt s₃.mem D (16 * (n / 16)) :=
    bytesAt_frame M.frame (fun r hr => (dD r hr).sub_left (Region.sub_prefix hq)) (by omega)
  have ht₇ : bytesAt s₇.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
      bytesAt s₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    bytesAt_frame M.frame (fun r hr => (dD r hr).sub_left (Offset.sub_base D (by omega))) (by omega)
  exact ⟨M.env, oneB_trans f₃ (oneFrame_B hq F₇'), M.rd.trans P.rd, M.wr.trans P.wr,
    ⟨by rw [kp₇ 176 (.inl ⟨by decide, by decide⟩)]; exact hR₃.1, hR⟩,
    by rw [kp₇ 192 (.inl ⟨by decide, by decide⟩)]; exact P.tlen,
    by rw [kp₇ 200 (.inl ⟨by decide, by decide⟩)]; exact P.dat,
    by rw [kp₇ 208 (.inl ⟨by decide, by decide⟩)]; exact hlen₃, M.zf, M.aux, M.j,
    by rw [M.cb, ct₃.1]; congr 1; omega, by rw [hp₇, hw₃, hc₇, hc₃], ht₇.trans ht₃, hc₇.trans hc₃⟩

/-- After `oneAad`: the whole blocks decrypted and absorbed, the tag of the
ciphertext compared with the received one, and the data decrypted if they
match, or kept if not. -/
theorem openBody_ok {R t : Nat} {D : Addr} {n al : Nat} {H J : Block} {a : List Byte} {s : State}
    (h : ObPre Ctx W SP R D n s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J) (hcb : blockAt s.mem (cbA W) = inc32 J) {Tp : Addr}
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨Tp, t⟩)
    (oA : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    WP isa (.seq (oneBlocks v.callees.dec) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (oneUndo v.callees) (oneCrypt v.callees))
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (VG.Proof.AesGcm.X86_64.oneFrameB W D SP n) s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧
      let T := toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (padded a (bytesAt s.mem D n))))
        [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R J)
      s'.gpr .rax = BitVec.ofNat 64 (if T.take t = bytesAt s.mem Tp t then 1 else 0) ∧
      bytesAt s'.mem D n = if T.take t = bytesAt s.mem Tp t then xorKs (ciphOf s.mem Ctx R) (inc32 J) 0 (bytesAt s.mem D n)
        else bytesAt s.mem D n := by
  have hq : 16 * (n / 16) ≤ n := by omega
  have split : ∀ m : Mem, bytesAt m D n =
      bytesAt m D (16 * (n / 16)) ++ bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) :=
    fun m => by rw [← bytesAt_add, Nat.add_sub_cancel' hq]
  refine WP.seq6 (VG.Proof.AesGcm.X86_64.openFront_ok v L h hH hal htl h1 h16 habs hj hcb hTa hTar hTr oT oA) fun s₇ F => ?_
  generalize hT : toBytes (ghashFrom H (VG.Spec.Gcm.ghash H (blocks (padded a (bytesAt s.mem D n))))
    [ofBytes (lensBlock al n)] ^^^ ciphOf s.mem Ctx R J) = T at F ⊢
  generalize hk : (if T.take t = bytesAt s.mem Tp t then 1 else 0) = k at F
  refine WP.mono (VG.Proof.AesGcm.X86_64.openEnd_ok v L F.env F.rounds F.tlen F.dat F.len (h.data.of_eq F.rd F.wr) F.zf F.aux F.j F.cb
    F.whole) fun s' ⟨he', f', rd', wr', ax', d'⟩ => ⟨he', oneB_trans F.frame f', rd'.trans F.rd, wr'.trans F.wr,
      by rw [ax', ← hk], ?_⟩
  rw [d', F.tail, ← split, F.ciph]
  by_cases hc : T.take t = bytesAt s.mem Tp t
  · simp only [hc, ↓reduceIte] at hk ⊢; subst hk; simp
  · simp only [hc, ↓reduceIte] at hk ⊢; subst hk; simp

end

/-- The result of `open`, from the parts. -/
abbrev OpenRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0 ∧ bytesAt s.mem D n = c

/-- `vg_aes_gcm_open`. -/
theorem open_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.openX86_64.pre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  have hW' : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 = stackArg s 4 := rfl
  have hTa : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := rfl
  have hTar := C.args 2 (by decide)
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hD : stackArg s 0 = D at *
  generalize hn : (stackArg s 1).toNat = n at *
  generalize hT : stackArg s 2 = T at *
  generalize hW : stackArg s 4 = W at *
  have L := C.lay
  generalize hR : (s.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.openEntry_ok C hCtx hSP hA hD hn hW') fun s₁ ⟨E, hbx₁, htl₁, fE⟩ => ?_)
  generalize ht : (stackArg s 3).toNat = t at hTr d_td d_tw t_t ⊢
  have oT : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨T, t⟩ := fun r hr =>
    hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have oA : VG.Proof.AesGcm.X86_64.OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ := fun r hr => VG.Proof.AesGcm.X86_64.arg24_disj (by decide) C.dA C.dAD hr
  have hbx₁' : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hbx₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₁' : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [htl₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁' (ht ▸ (stackArg s 3).isLt)) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  have E₂ : OneEntry s Ctx W SP A D n s₂ := E.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  have dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  have dDR : ∀ r ∈ [oneR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have hlt := C.data.ok.lt
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧
      s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧
      VG.Proof.AesGcm.X86_64.OpenRes (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al)
        (bytesAt s.mem T t) D n s₅)
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₂) (fun hbad => ?_) (fun hok => ?_)) fun s₅ h₅ => ?_)
  · -- A length §5.2.1.2 does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₅ => s₅.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₅.gpr r = s₂.gpr r) ∧ s₅.mem = s₂.mem ∧
        s₅.rd = s₂.rd ∧ s₅.wr = s₂.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₅ ⟨hax, hg₅, hm₅, hrd₅, hwr₅⟩ => ?_
    refine ⟨E₂.env.keep (fun r hr => hg₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅, by rw [hm₅]; exact E₂.saved, ?_, ?_⟩
    · rw [hm₅, k₂.mem, ret_kept fE dR]
    · simp only [VG.Proof.AesGcm.X86_64.OpenRes, Spec.Gcm.openResult, hbad', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hax, by rw [hm₅, k₂.mem, bytesAt_frame fE dDR (by omega)]⟩
  · -- An allowed length.
    have hok' : Spec.Gcm.tagLenOk t = true := by simpa using hok
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok'
      omega
    refine WP.seq (WP.mono (VG.Proof.AesGcm.X86_64.oneMid_ok v C E₂ hNp hnl hal) fun s₃ M => ?_)
    generalize hH : ctxH s.mem Ctx = H at M
    generalize hiv : bytesAt s.mem Np nl = iv at M
    generalize ha : bytesAt s.mem A al = a at M
    have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
      rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hal' : a.length = al := by rw [← ha, length_bytesAt]
    have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
      rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm) (by decide), k₂.mem, htl₁']
    have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by
      rw [M.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact oA _ (.inl fun _ h => h)
        · exact oA _ (.inr (.inr (below_sub (by decide) (by decide))))) (by decide), hTa]
    refine WP.mono (VG.Proof.AesGcm.X86_64.openBody_ok v L (al := al) ⟨M.env, hR ▸ M.rounds, M.dat, M.len, C.data.of_eq M.rd M.wr, C.t_c,
      C.t_w, C.t_d, C.sp24⟩ M.hH hal₃ htl₃ hb.1 hb.2 M.abs M.j0 M.cb hTa₃ (by rw [M.rd, M.wr]; exact hTar)
      (by rw [M.rd, M.wr]; exact hTr) oT oA) fun s₄ ⟨he₄, f₄, _, _, hax₄, hD₄⟩ => ?_
    rw [← hal'] at hax₄ hD₄
    -- From the entry to `s₃`.
    have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
        ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
      intro p k h₁ h₂ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.symm
    have hc₃ : ciphOf s₃.mem Ctx R = ctxCiph s.mem Ctx R := ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
    have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
      bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by omega)
    have hw₃ : bytesAt s₃.mem T t = bytesAt s.mem T t := bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oT _ (.inl fun _ h => h)
      · exact oT _ (.inr (.inr (below_sub (by decide) (by decide))))) (by omega)
    have dRet : ∀ r ∈ VG.Proof.AesGcm.X86_64.oneFrameB W D SP n, (⟨SP, 8⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact C.rW.sub_right (Region.sub_prefix (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rD
      · exact Offset.base_disjoint_below SP (n := 24) (k := 8) (by decide)
    refine ⟨he₄, M.saved.frame f₄ (saved_oneFrameB L C.dE C.t_w), ?_, ?_⟩
    · rw [ret_kept f₄ dRet, ret_kept M.frame (fun r hr => ?_)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact C.rW
      · exact ret_below SP
    · rw [hc₃, hp₃, hw₃] at hax₄
      rw [hc₃, hp₃, hw₃, ← Proof.Gcm.gctr_eq] at hD₄
      simp only [VG.Proof.AesGcm.X86_64.OpenRes, Spec.Gcm.openResult, hok', ↓reduceIte, Spec.Gcm.decryptWith,
        Proof.Gcm.fullTag_eq, length_bytesAt, ← Proof.Gcm.gctr_eq]
      split at hax₄
      · next e => simp only [e, ↓reduceIte] at hD₄ ⊢; exact ⟨hax₄, hD₄⟩
      · next e => simp only [e, ↓reduceIte] at hD₄ ⊢; exact ⟨hax₄, hD₄⟩
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨hg, hm, hax⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.openX86_64, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hT, hR, ht]
  simp only [VG.Proof.AesGcm.X86_64.OpenRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩

end VG.Proof.AesGcm.X86_64

end

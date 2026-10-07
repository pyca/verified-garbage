import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody

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
      (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₁.mem) := by
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
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact oneR_w).trans
    (wFrame_w ao.frame)

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

theorem OutWDS.ws {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) : OutWS W SP X :=
  fun r hr => h r (hr.elim .inl fun h => .inr (.inr h))

theorem OutWS.tagFrame {W SP : Addr} {X : Region} (h : OutWS W SP X) {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ (⟨W + BitVec.ofNat 64 o, 16⟩ :: wFrame W SP), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Lay.wSub ho))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (below_sub (by decide) (by decide)))

theorem OutWDS.oneFrameB {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) :
    ∀ r ∈ oneFrameB W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Region.sub_prefix (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr fun _ h => h))

theorem OutWDS.oneFrame {W D SP : Addr} {n : Nat} {X : Region} (h : OutWDS W D SP n X) :
    ∀ r ∈ oneFrame W D SP n, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h _ (.inl (Region.sub_prefix (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inl (Lay.wSub (by decide)))
  · exact h _ (.inr (.inl fun _ h => h))
  · exact h _ (.inr (.inr (below_sub (by decide) (by decide))))

/-- `OutWDS` for the data from byte `k` on. -/
theorem OutWDS.drop {W D SP : Addr} {n k : Nat} {X : Region} (h : OutWDS W D SP n X) (hk : k ≤ n) :
    OutWDS W (D + BitVec.ofNat 64 k) SP (n - k) X := fun r hr =>
  h r (hr.imp_right fun hr => hr.imp_left fun hs a ha =>
    Offset.sub_base D (d := k) (n := n - k) (k := n) (by omega) a (hs a ha))

/-- The address of `tag`, the argument at `[SP + 24]`, is outside `W`, the
data and the stack below `SP`. -/
theorem OneCtx.arg24 {s : State} {k : Nat} (hk : 3 ≤ k) {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ :=
  fun _ hr => arg24_disj hk C.dA C.dAD hr

/-- After the entry, `seal` up to the tag at `W`: `oneAad`, `oneBlocks`,
`oneCrypt` and `oneTag 0`. -/
theorem sealRun_ok (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (.seq (oneCrypt v.callees) (oneTag v.callees 0))))
      s₁ fun s₄ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
        SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s₄.mem ∧
        bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat)
          (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (bytesAt s₀.mem D n) ∧
        bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
            (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
          ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) := by
  have L := C.lay
  generalize hR : (s₀.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₂ M => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s₀.mem A al = a at M ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ M.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  have hal₂ : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have X₂ := X.keep M.rd M.wr M.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  refine WP.seq_assoc (WP.mono (WP.with_rdwr (sealBody_ok v L B (icb := inc32 (Spec.Gcm.j0 H iv)) (a := a)
    ⟨M.env, hRo, M.dat, M.len, hd₂, C.t_c, C.t_w, C.t_d, C.sp24, X₂⟩ M.hH M.cb hal₂ M.abs))
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

/-- `x; (a; (b; (c; ((d; e); f))))` from `x; ((a; (b; (c; d))); (e; f))`. -/
theorem WP.reassoc_seal' {x a b c d e f : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq x (.seq (.seq a (.seq b (.seq c d))) (.seq e f))) s Q) :
    WP isa (.seq x (.seq a (.seq b (.seq c (.seq (.seq d e) f))))) s Q := by
  obtain ⟨t, s', ex, q⟩ := h
  cases ex with | seq ex ex₁ => cases ex₁ with | seq ex₁ ex₂ => cases ex₁ with | seq ea ex₁ => cases ex₁ with
    | seq eb ex₁ => cases ex₁ with | seq ec ed => cases ex₂ with | seq ee ef =>
      exact ⟨_, _, .seq ex (.seq ea (.seq eb (.seq ec (.seq (.seq ed ee) ef)))), q⟩

/-- What `sealRun_ok` leaves, after the entry. -/
abbrev SealRunPost (s₀ : State) (Ctx W SP Np A D : Addr) (nl al n : Nat) (s₄ : State) : Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ ∧ s₄.rd = s₀.rd ∧ s₄.wr = s₀.wr ∧
    SavedAt s₄.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s₄.mem ∧
    bytesAt s₄.mem D n = gctr (ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat)
      (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl))) (bytesAt s₀.mem D n) ∧
    bytesAt s₄.mem W 16 = toBytes (ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (padded (bytesAt s₀.mem A al) (bytesAt s₄.mem D n)))) [ofBytes (lensBlock al n)] ^^^
      ctxCiph s₀.mem Ctx (s₀.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)))

/-- `seal` with any code `mid` after the entry that leaves what `sealRun_ok`
does: the tag copied to `tag`, then the exit. -/
theorem sealM_of {M : Gcm.X86_64.Stitch.CtxMode} {mid : Prog isa} {s : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s)
    (hmid : ∀ {Ctx W SP Np A D : Addr} {nl al n : Nat} {s₁ : State}, OneCtx s 4 Ctx W SP Np A D nl al n →
      CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s → OneEntry s Ctx W SP A D n s₁ →
      s.gpr .rdx = Np → (s.gpr .rcx).toNat = nl → (s.gpr .r9).toNat = al →
      WP isa mid s₁ (SealRunPost s Ctx W SP Np A D nl al n)) :
    WP isa (.seq (.block (oneEntry 32)) (.seq mid (.seq (.block (tagOut (at_ .rsp 24))) (.block restore)))) s
      fun s' => gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  have X := CtxExt.ofSeal hp.1 hp.2
  obtain ⟨C, hTw, d_td, d_tw, r_t⟩ := OneCtx.ofSeal hp.1 M.ge
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
  refine WP.seq (WP.mono (hmid C X E rfl rfl rfl) fun s₄ ⟨he₄, hrd₄, hwr₄, hsv₄, f₄, hC, hT₄⟩ => WP.seq ?_)
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

/-- `vg_aes_gcm_seal`, for a key context of kind `M`. -/
theorem sealM_wp (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa («seal» (v.withBlk B)) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  WP.reassoc_seal' (sealM_of hp fun C X E hNp hnl hal => sealRun_ok v B C X E hNp hnl hal)

/-- `vg_aes_gcm_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.sealX86_64.pre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  sealM_wp v v.blkB ⟨hp, trivial⟩

end VG.Proof.AesGcm.X86_64

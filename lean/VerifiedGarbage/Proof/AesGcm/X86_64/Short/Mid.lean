import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bytes
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.J0

/-!
# AES-GCM's short path on x86-64: what the steps keep

Untrusted: everything here is checked by Lean. `SM`: after `J₀` and the
counts, what every later step of the short path keeps: the registers holding
the key context, the state and `W`, the scalars kept in `W`, `J₀`, the
additional data, the saved registers, and what has been written since the
entry (`W`, the data and the stack below `SP`). The steps write only `T`
(`W`'s first 16 bytes, the tag) and `W + 512` … `W + 2048` (`G`, `K` and the
powers), and the data (`SM.keep`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The regions the steps after the counts write: in `W` (the tags, the
tags compared and the result of the comparison, `G`, `K` and the powers),
and the data. -/
abbrev Wk (W D : Addr) (n : Nat) (r : Region) : Prop :=
  r.Sub ⟨W, 16⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 512, 1536⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 112, 16⟩ ∨
    r.Sub ⟨W + BitVec.ofNat 64 216, 8⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 240, 32⟩

/-- After `J₀` and the counts. -/
structure SM (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  r176 : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R
  r184 : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  r200 : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  r208 : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r224 : s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl
  r232 : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  r272 : s.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 (nb16 al)
  r280 : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 (nb16 n)
  r288 : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * grp al n)
  r296 : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 (4 * grp al n - (nb16 al + nb16 n + 1))
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = J
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem wk_disj {W D : Addr} {n d k : Nat} (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (h₁ : 16 ≤ d)
    (h₂ : d + k ≤ 512) (h₃ : d + k ≤ 112 ∨ 128 ≤ d) (h₄ : d + k ≤ 216 ∨ 224 ≤ d) (h₅ : d + k ≤ 240 ∨ 272 ≤ d)
    {r : Region} (hr : Wk W D n r) : (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  rcases hr with hr | hr | hr | hr | hr | hr
  · refine Region.Disjoint.sub_right ?_ hr
    have := Offset.disjoint W (d := d) (n := k) (e := 0) (k := 16) (.inr (by omega)) (by omega) (by omega)
    simpa using this
  · exact (Offset.disjoint W (d := d) (n := k) (e := 512) (k := 1536) (.inl (by omega)) (by omega)
      (by omega)).sub_right hr
  · exact (dD.symm.sub_left (Lay.wSub (by omega))).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 112) (k := 16) (by omega) (by omega) (by omega)).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 216) (k := 8) (by omega) (by omega) (by omega)).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 240) (k := 32) (by omega) (by omega) (by omega)).sub_right hr

/-- A step that writes only in the work regions and keeps `r13`–`r15` and
`rsp`. -/
theorem SM.keep {s₀ : State} {Ctx W SP A D : Addr} {R al n : Nat} {J : Block} {tl : BitVec 64} {s s' : State}
    (S : SM s₀ Ctx W SP A D R al n J tl s) (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {rs : List Region} (f : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Wk W D n r)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SM s₀ Ctx W SP A D R al n J tl s' := by
  have kp : ∀ d, 16 ≤ d → d + 8 ≤ 512 → (d + 8 ≤ 112 ∨ 128 ≤ d) → (d + 8 ≤ 216 ∨ 224 ≤ d) →
      (d + 8 ≤ 240 ∨ 272 ≤ d) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ h₄ h₅ =>
    f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => wk_disj dD h₁ h₂ h₃ h₄ h₅ (hrs r hr)) (by decide)
  refine ⟨S.env.keep hg hrd hwr, by rw [kp 176 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r176,
    by rw [kp 184 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r184,
    by rw [kp 200 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r200,
    by rw [kp 208 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r208,
    by rw [kp 224 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r224,
    by rw [kp 232 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r232,
    by rw [kp 272 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r272,
    by rw [kp 280 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r280,
    by rw [kp 288 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r288,
    by rw [kp 296 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r296,
    ?_, S.saved.frame f fun r hr => wk_disj dD (by decide) (by decide) (by decide) (by decide) (by decide) (hrs r hr),
    S.frame.trans (f.sub fun r hr => ?_), hrd.trans S.rd, hwr.trans S.wr⟩
  · rw [blockAt_frame f fun r hr => wk_disj dD (by decide) (by decide) (by decide) (by decide) (by decide) (hrs r hr)]; exact S.j0
  · rcases hrs r hr with h | h | h | h | h | h
    · exact ⟨_, List.mem_cons_self .., fun x hx => Region.sub_prefix (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨⟨D, n⟩, by simp, h⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩

/-- A part of `W` that `j0` does not write. -/
theorem j0f_disj {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {d k : Nat} (h₁ : 112 ≤ d)
    (h₂ : d + k ≤ 216 ∨ 224 ≤ d) (h₃ : d + k ≤ 512) :
    ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have ww := L.ww
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint W (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  · exact (L.kw.sub_right (Lay.wSub (by omega))).symm

/-- The short path's start: `J₀` of the 12-byte nonce and the counts. -/
theorem shortStart_ok {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hnl : nl = 12) (hal : (s₀.gpr .r9).toNat = al)
    (hal5 : al < 512) (hn5 : n < 512) :
    WP isa (.block (Impl.AesGcm.X86_64.j012 ++ Impl.AesGcm.X86_64.Short.sizes)) s₁
      fun s => SM s₀ Ctx W SP A D (s₀.gpr .rsi).toNat al n
        (Spec.Gcm.j0 (Spec.Gcm.ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) (s₁.mem.readW (W + BitVec.ofNat 64 224) 64) s ∧ bytesAt s.mem A al = bytesAt s₀.mem A al ∧
        bytesAt s.mem D n = bytesAt s₀.mem D n := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W],
      (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s₀.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  subst hnl
  have hiv : bytesAt s₁.mem Np 12 = bytesAt s₀.mem Np 12 :=
    bytesAt_frame E.frame (dW _ _ C.nonce.w) (by decide)
  have j0in : J0In Ctx (W + BitVec.ofNat 64 16) W SP (Spec.Gcm.ctxH s₀.mem Ctx) Np 12 s₁ :=
    ⟨E.env, hH₁, by rw [E.r12, hNp], by rw [E.rbp, ← hnl', BitVec.ofNat_toNat, BitVec.setWidth_eq],
      C.nonce.of_eq E.rd E.wr⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.with_rdwr (j012_ok L j0in)) fun s₂ ⟨J, rd₂, wr₂⟩ => ?_
  rw [hiv] at J
  have kp : ∀ d, 112 ≤ d → (d + 8 ≤ 216 ∨ 224 ≤ d) → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ =>
    J.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (j0f_disj L h₁ h₂ h₃) (by decide)
  have hal₁ : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (sizes_ok s₂ J.env.r15 J.env.perm.w (by rw [kp 184 (by decide) (by decide) (by decide), hal₁])
    (by rw [kp 208 (by decide) (by decide) (by decide), E.len]) hal5 hn5)
    fun s₃ ⟨m272, m280, m288, m296, f₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  have kp₃ : ∀ d, 112 ≤ d → (d + 8 ≤ 216 ∨ 224 ≤ d) → d + 8 ≤ 272 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ => by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by omega)) (by have := L.ww; omega) (by have := L.ww; omega)) (by decide),
      kp d h₁ h₂ (by omega)]
  have f₃' : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₂.mem s₃.mem :=
    f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have f₂ : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₁.mem s₂.mem :=
    J.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩
  have f₁ : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s₁.mem :=
    E.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  refine ⟨⟨J.env.keep (fun r hr => ?_) rd₃ wr₃, by rw [kp₃ 176 (by decide) (by decide) (by decide)]; exact E.rounds.1,
    by rw [kp₃ 184 (by decide) (by decide) (by decide), hal₁],
    by rw [kp₃ 200 (by decide) (by decide) (by decide), E.dat],
    by rw [kp₃ 208 (by decide) (by decide) (by decide), E.len],
    by rw [kp₃ 224 (by decide) (by decide) (by decide)],
    by rw [kp₃ 232 (by decide) (by decide) (by decide), E.aad], m272, m280, m288, m296, ?_, ?_,
    f₁.trans (f₂.trans f₃'), by rw [rd₃, rd₂, E.rd], by rw [wr₃, wr₂, E.wr]⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide)
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by have := L.ww; omega) (by have := L.ww; omega)]
    exact J.j0
  · exact (E.saved.frame J.frame (saved_j0Frame L)).frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by have := L.ww; omega) (by have := L.ww; omega)

  · have hl := C.aad.lt
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.aad.w.sub_right (Lay.wSub (by decide))) (by omega),
      bytesAt_frame J.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact C.aad.st
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.stk.symm) (by omega),
      bytesAt_frame E.frame (dW _ _ C.aad.w) (by omega)]
  · have hl := C.data.ok.lt
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))) (by omega),
      bytesAt_frame J.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact C.data.ok.st
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.data.ok.stk.symm) (by omega),
      bytesAt_frame E.frame (dW _ _ C.dE) (by omega)]

end VG.Proof.AesGcm.X86_64.Short

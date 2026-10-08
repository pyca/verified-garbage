import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyPath
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SealCallee

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the call of `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_seal` on the text gathered in the output, with `dst`, `len` and
`tag` pushed for it (`sealCall_ok`): what it needs, from the layout of the
entry state `s` (`sealEntry`), and that what it leaves is what
`vg_aes_gcm_seal_gather` must (`Done`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat stackArg_entry)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.sealGatherPostG s s'

section
variable (s : State)

/-- What the call reads and writes. -/
abbrev sealRd (M : CtxMode) : List Region := [kR M s, nR s, aR s, ⟨SP s - BitVec.ofNat 64 24, 24⟩]
abbrev sealWr : List Region := [dR s, tgR s]

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- What the call of `vg_aes_gcm_seal` needs. -/
theorem sealPre_of {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 32) (hrd : u.rd = sealRd s M) (hwr : u.wr = sealWr s)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = Nn s)
    (h_cx : u.gpr .rcx = s.gpr .rcx) (h_8 : u.gpr .r8 = Ad s) (h_9 : u.gpr .r9 = AL s)
    (a0 : stackArg u 0 = Dst s) (a1 : stackArg u 1 = stackArg s 3) (a2 : stackArg u 2 = Tg s)
    (hok : M.ok u.mem (K s)) :
    (sealK M).pre u := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hargs : (Proof.AesGcm.args u 3) = ⟨SP s - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : below (SP s - BitVec.ofNat 64 32) 2624 = ⟨SP s - BitVec.ofNat 64 2656, 2624⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 24, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 32, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2656, 2624⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have hsp32 : (SP s - BitVec.ofNat 64 32).toNat = (SP s).toNat - 32 := toNat_sub_ofNat (by omega)
  have hsp24 : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have hsp2656 : (SP s - BitVec.ofNat 64 2656).toNat = (SP s).toNat - 2656 := toNat_sub_ofNat (by omega)
  have d₁ : (⟨SP s - BitVec.ofNat 64 32, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp32, hsp24]; omega) (by simp only [hsp24]; omega)
  have d₂ : (⟨SP s - BitVec.ofNat 64 2656, 2624⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2656, hsp24]; omega) (by simp only [hsp24]; omega)
  simp only [sealK, sealPreK, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0, a1,
    a2, hrsp, Proof.AesGcm.rounds, hstk]
  exact ⟨trivial, trivial, hp.k_d, hp.k_t, hp.n_d, hp.n_t, hp.a_d, hp.a_t, hp.d_t, hp.b_d.symm.sub_right tA,
    hp.b_t.symm.sub_right tA, hp.b_k.sub_left tR', hp.b_n.sub_left tR', hp.b_a.sub_left tR', hp.b_d.sub_left tR',
    hp.b_t.sub_left tR', d₁, hp.b_k.sub_left tS, hp.b_n.sub_left tS, hp.b_a.sub_left tS, hp.b_d.sub_left tS,
    hp.b_t.sub_left tS, d₂, hp.w_k, hp.w_n, hp.w_ad, hp.w_d, hp.w_t, by rw [hsp32]; omega, by rw [hsp32]; omega,
    hp.rounds, hok⟩

/-- The registers the call of `vg_aes_gcm_seal` is entered with. -/
structure SealRegs (s st : State) : Prop where
  rdi : st.gpr .rdi = K s
  rsi : st.gpr .rsi = s.gpr .rsi
  rdx : st.gpr .rdx = Nn s
  rcx : st.gpr .rcx = s.gpr .rcx
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s
  rax : st.gpr .rax = Tg s
  r10 : st.gpr .r10 = stackArg s 3
  r11 : st.gpr .r11 = Dst s

/-- What the call of `vg_aes_gcm_seal` needs, after the push. -/
theorem sealEntry {st : State} (h : SBase s st) (g : SealRegs s st) :
    (sealK M).pre ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) ∧
      Covers (sealRd s M ++ sealWr s) ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) ∧
      Covers (sealWr s) (pushed [.rax, .r10, .r11] st).wr ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 0 = Dst s ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 1 = stackArg s 3 ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 2 = Tg s := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  have hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r10, .r11] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r10, .r11][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (h.frame.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans
      (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have ea : ∀ j, j < 3 →
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) j =
        (pushed [.rax, .r10, .r11] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * j)) 64 :=
    fun j hj => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega)
  have a0 := ea 0 (by decide)
  have a1 := ea 1 (by decide)
  have a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have hok : M.ok ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_apart hp) hp.w_k hp.ok
  have hpre := sealPre_of hp hU rfl rfl (by rw [gU _ (by decide)]; exact g.rdi)
    (by rw [gU _ (by decide)]; exact g.rsi) (by rw [gU _ (by decide)]; exact g.rdx)
    (by rw [gU _ (by decide)]; exact g.rcx) (by rw [gU _ (by decide)]; exact g.r8)
    (by rw [gU _ (by decide)]; exact g.r9) (by rw [a0, g.r11]) (by rw [a1, g.r10]) (by rw [a2, g.rax]) hok
  have hPw : (pushed [.rax, .r10, .r11] st).wr = ⟨SP s - BitVec.ofNat 64 24, 24⟩ :: wR s := by
    rw [pushed_wr, hsp, h.wr, hp.wr]; rfl
  have hPr : (pushed [.rax, .r10, .r11] st).rd = [kR M s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] := by
    rw [pushed_rd, h.rd, hp.rd]
  have cw : Covers (sealWr s) (pushed [.rax, .r10, .r11] st).wr := by
    rw [hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')
  have cr : Covers (sealRd s M ++ sealWr s)
      ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
        (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')))))
  exact ⟨hpre, cr, cw, by rw [a0, g.r11], by rw [a1, g.r10], by rw [a2, g.rax]⟩

/-- The call of `vg_aes_gcm_seal` on the text gathered in the output, with
`dst`, `len` and `tag` pushed for it: what `vg_aes_gcm_seal_gather` must leave. -/
theorem sealCall_ok (S : SealFn M) {st : State} (h : SBase s st) (g : SealRegs s st) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call S.fn.name S.fn.code) (.pop .rax 3)) st (Done s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .r11] st).callEntry.mem := h.frame.trans fS
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain ⟨hpre, cr, cw, a0, a1, a2⟩ := sealEntry hp h g
  -- The text gathered, which the push and the return address leave as it was.
  have fS2 : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩, ⟨SP s - BitVec.ofNat 64 32, 8⟩] st.mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  have eD : bytesAt (pushed [.rax, .r10, .r11] st).callEntry.mem (Dst s) (L s) = pt s (Cnt s) := by
    rw [← h.out]
    refine bytesAt_frame fS2 (fun r hr => ?_) (Nat.le_of_lt hL)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.b_d.symm.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hp.b_d.symm.sub_right (stk_sub (s := s) (by decide) (by decide))
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := sealK M)
    S.ok S.sp (by have := S.xd; omega) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [sealK, Proof.AesGcm.sealX86_64, Proof.AesGcm.arg, a0, a1, a2, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    g.rdi, g.rsi, g.rdx, g.rcx, g.r8, g.r9, hm₂, ciph_eq hp fU, hk_eq hp fU, iv_eq hp fU, ad_eq hp fU, eD]
    at hpost
  have b4888 : Region.Sub (below ((pushed [.rax, .r10, .r11] st).gpr .rsp) (S.fn.code.x86_64Depth + 8)) (tR s) := by
    have h₁ := below_sub (sp := (pushed [.rax, .r10, .r11] st).gpr .rsp) (a := S.fn.code.x86_64Depth + 8)
      (b := 4864) (by have := S.xd; omega) (by decide)
    have e : below (SP s - BitVec.ofNat 64 24) 4864 = ⟨SP s - BitVec.ofNat 64 4888, 4864⟩ := by
      simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
    rw [hP] at h₁ ⊢
    rw [e] at h₁
    exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
  have fC : Frame (wR s ++ [tR s]) st.mem s'.mem := by
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨dR s, by simp, fun _ h => h⟩
      · exact ⟨tgR s, by simp, fun _ h => h⟩
      · exact ⟨tR s, by simp, b4888⟩
  refine ⟨r₃, hwr', ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP]
      show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr',
        h.saved r hr]
  · rw [popped_mem]
    exact (h.frame.trans fC).readW (Region.contains_self _ _) (ret_disj hp) (by decide)
  · show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) = _
    rw [popped_mem]
    exact hpost

end

/-- `SBase` through code that changes no memory, `rsp` or callee-saved register. -/
theorem SBase.regs {s st st' : State} (h : SBase s st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : SBase s st' :=
  ⟨⟨h.toBase.regs hm hcs hrd hwr, hm ▸ h.nonce, hm ▸ h.nonceLen⟩, hm ▸ h.out⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The path of a short text, after the test: the slices copied to the
output, and encrypted there by `vg_aes_gcm_seal`. -/
theorem copySeal_wp (S : SealFn M) (hL : L s < 2 ^ 63) {st : State} (h : Base s (AL s) 0 st)
    (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s) (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (Impl.AesGcm.X86_64.SealGather.copySeal S.fn) st (Done s) := by
  unfold Impl.AesGcm.X86_64.SealGather.copySeal
  refine WP.seq (WP.mono (copyEntry_ok hp h h11 hsi hdx) fun s₁ ⟨r9₁, rdi₁, r11₁, _, C₁⟩ => ?_)
  refine WP.seq (WP.mono (gatherCopy_wp s₁ (copyGatherPre hp hL C₁.toBase r9₁ rdi₁ r11₁)) fun s₂ ⟨m₂, k₂⟩ => ?_)
  have B₂ := gathered_after hp C₁ m₂ k₂
  refine WP.seq (WP.mono (sealArgs_ok hp B₂) fun s₃ ⟨di, si, dx, cx, r8, r9, ax, r10, r11, cs, m, rd, wr⟩ => ?_)
  exact sealCall_ok hp S (B₂.regs m cs rd wr) ⟨di, si, dx, cx, r8, r9, ax, r10, r11⟩

end

end VG.Proof.AesGcm.X86_64.Gather

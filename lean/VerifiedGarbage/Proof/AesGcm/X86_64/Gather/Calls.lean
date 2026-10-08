import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the calls without stack arguments

Untrusted: everything here is checked by Lean. A call, by its contract, of a
function that uses at most 4880 bytes of stack (`call0_ok`); and the calls
of `vg_aes_gcm_stream_init` (`initCall_ok`), `vg_aes_gcm_stream_aad`
(`aadCall_ok`) and `vg_aes_gcm_stream_finish` (`finCall_ok`): what each
needs, from the layout of the entry state `s`, and what it leaves.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block StreamRepr ctxCiph ctxH gctr inc32 j0 fullTag gathered)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_off covers_cons' covers_nil' streamRepr_frame)

theorem covers_left' {rd wr rs : List Region} (h : Covers rs rd) : Covers rs (rd ++ wr) :=
  fun a k hi => let ⟨r, hr, hc⟩ := h a k hi; ⟨r, List.mem_append_left _ hr, hc⟩

/-- A call by the contract `k` of a function using at most `d` bytes of
stack, from `rsp = SP`: what it changes is within its writable regions and
the stack. -/
theorem call0_ok {s : State} {k : Contract isa} {d : Nat} (F : CallFn k d) (hd : d + 8 ≤ 4888) {st : State}
    (hsp : st.gpr .rsp = SP s) {rd wr : List Region} (hpre : k.pre (st.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (st.rd ++ st.wr)) (hw : Covers wr st.wr) :
    WP isa (.call F.fn.name F.fn.code) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (wr ++ [tR s]) st.mem st'.mem ∧
      ∃ s₂ : State, s₂.mem = st'.mem ∧ k.post (st.callEntry.withRegions rd wr) s₂ :=
  WP.call_sp_mx F.ok F.sp (by have := F.xd; omega) hpre hc hw fun _ hrd hwr hcs hfr _ ⟨s₂, hm, _, hpost⟩ _ =>
    ⟨hcs, hrd, hwr, hfr.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨tR s, by simp, by rw [hsp]; exact below_sub (by have := F.xd; omega) (by decide)⟩,
      s₂, hm, hpost⟩

section
variable {s : State}

/-- The state a call enters, from `rsp = SP`. -/
theorem entry_gpr {st : State} (rd wr : List Region) {r : Reg} (hr : r ≠ .rsp) :
    (st.callEntry.withRegions rd wr).gpr r = st.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

theorem entry_rsp {st : State} (hsp : st.gpr .rsp = SP s) (rd wr : List Region) :
    (st.callEntry.withRegions rd wr).gpr .rsp = SP s - BitVec.ofNat 64 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hsp]; rfl

/-- The return address of a call from `rsp = SP`, on the stack the calls use. -/
theorem ret_sub : Region.Sub ⟨SP s - BitVec.ofNat 64 8, 8⟩ (tR s) := Offset.sub_below _ (by decide) (by decide)

/-- The stack of a callee using `n ≤ 4880` bytes of stack, called from `rsp = SP`. -/
theorem stk_sub' {n : Nat} (hn : n + 8 ≤ 4888) : Region.Sub (below (SP s - BitVec.ofNat 64 8) n) (tR s) :=
  fun a h => below_sub (sp := SP s) (by omega) (by decide) a (below_callee (SP s) n a h)

/-- The memory a call from `rsp = SP` enters with, from the entry's. -/
theorem entry_frame {st : State} (hsp : st.gpr .rsp = SP s) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (rd wr : List Region) : Frame (wR s ++ [tR s]) s.mem (st.callEntry.withRegions rd wr).mem := by
  refine hf.trans ((callEntry_frame st).sub fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨tR s, by simp, by rw [hsp]; exact below_sub (by decide) (by decide)⟩

/-- What the return address leaves as it was. -/
theorem entry_keep {st : State} (hsp : st.gpr .rsp = SP s) (rd wr : List Region) :
    Frame [tR s] st.mem (st.callEntry.withRegions rd wr).mem :=
  (callEntry_frame st).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨tR s, by simp, by rw [hsp]; exact below_sub (by decide) (by decide)⟩

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- `Base` after a call whose writable regions are within the regions written
and apart from the slots kept. -/
theorem Base.after {ap : BitVec 64} {i : Nat} {st st' : State} (h : Base s ap i st)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr)
    {wr : List Region} (hf : Frame (wr ++ [tR s]) st.mem st'.mem) (hsub : ∀ r ∈ wr, ∃ t ∈ wR s, r.Sub t)
    (hk : ∀ r ∈ wr, (kpR s).Disjoint r) : Base s ap i st' := by
  refine ⟨by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, h.kept.frame hf fun r hr => ?_, h.frame.trans (hf.sub fun r hr => ?_)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact hk r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_w.symm.sub_left kpR_sub
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨t, ht, hs⟩ := hsub r hr; exact ⟨t, List.mem_append_left _ ht, hs⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR s, by simp, fun _ h => h⟩

omit hp in
theorem ct_zero : ct s 0 = [] := List.eq_nil_of_length_eq_zero (by rw [length_ct, gl_zero])

omit hp in
theorem st_sub : ∀ r ∈ [stR s], ∃ t ∈ wR s, r.Sub t := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩

/-! ## `vg_aes_gcm_stream_init` -/

/-- What the call of `vg_aes_gcm_stream_init` needs. -/
theorem initEntry {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) (h_di : st.gpr .rdi = K s)
    (h_si : st.gpr .rsi = Nn s) (h_dx : st.gpr .rdx = s.gpr .rcx) (h_cx : st.gpr .rcx = St s) :
    initK.pre (st.callEntry.withRegions [⟨K s, 256⟩, nR s] [stR s]) ∧
      Covers ([⟨K s, 256⟩, nR s] ++ [stR s]) (st.rd ++ st.wr) ∧ Covers [stR s] st.wr := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hw := hp.w_w
  have kS : Region.Sub ⟨K s, 256⟩ (kR M s) := Region.sub_prefix M.ge
  have hst : (St s).toNat = (W s).toNat + 104 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 104) (by decide)]; omega
  have hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have hpre : initK.pre (st.callEntry.withRegions [⟨K s, 256⟩, nR s] [stR s]) := by
    simp only [initK, initPre, Proof.AesGcm.ret, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp), entry_rsp h.rsp, h_di, h_si, h_dx, h_cx, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, (hp.k_w.sub_left kS).sub_right stR_sub, hp.n_w.sub_right stR_sub,
      (hp.b_k.sub_left ret_sub).sub_right kS, hp.b_n.sub_left ret_sub, (hp.b_w.sub_left ret_sub).sub_right stR_sub,
      (hp.b_k.sub_left (stk_sub' (by decide))).sub_right kS, hp.b_n.sub_left (stk_sub' (by decide)),
      (hp.b_w.sub_left (stk_sub' (by decide))).sub_right stR_sub,
      by have := hp.w_k; have := M.ge; omega, hp.w_n, by rw [hst]; omega, by rw [hsp8]; omega, by rw [hsp8]; omega⟩
  have hc : Covers ([⟨K s, 256⟩, nR s] ++ [stR s]) (st.rd ++ st.wr) := by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact covers_cons' (StreamTo.covers_prefix (L := M.len) (by simp) M.ge) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide) (by decide)) covers_nil'))
  have hw' : Covers [stR s] st.wr := by
    rw [h.wr, hp.wr]
    exact covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide) (by decide)) covers_nil'
  exact ⟨hpre, hc, hw'⟩

/-- The call of `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state)` on the
state in `work`. -/
theorem initCall_ok (F : InitFn) {st : State} (h : Base s (AL s) 0 st) (h_di : st.gpr .rdi = K s)
    (h_si : st.gpr .rsi = Nn s) (h_dx : st.gpr .rdx = s.gpr .rcx) (h_cx : st.gpr .rcx = St s) :
    WP isa (.call F.fn.name F.fn.code) st (Mid s (AL s) 0 []) := by
  obtain ⟨hpre, hc, hw'⟩ := initEntry hp h h_di h_si h_dx h_cx
  refine WP.mono (call0_ok F (by decide) h.rsp hpre hc hw') fun st' ⟨hcs, hrd, hwr, hf, s₂, hm, hpost⟩ => ?_
  have fU := entry_frame h.rsp h.frame [⟨K s, 256⟩, nR s] [stR s]
  rw [State.withRegions_mem] at fU
  simp only [initK, Proof.AesGcm.streamInitX86_64, State.withRegions_mem,
    entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp), h_di, h_si, h_dx, h_cx,
    hk_eq hp fU, hm] at hpost
  rw [show (s.gpr .rcx).toNat = NL s from rfl, iv_eq hp fU] at hpost
  have hB := h.after hp hcs hrd hwr hf st_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  refine ⟨hB, Nat.zero_le _, ?_, ?_⟩
  · rw [ct_zero]; exact hpost _
  · rw [gl_zero, ct_zero]; rfl

/-! ## `vg_aes_gcm_stream_aad` -/

/-- What the call of `vg_aes_gcm_stream_aad` needs. -/
theorem aadEntry {ap : BitVec 64} {i : Nat} {D : Addr} {n : Nat} {st : State}
    (h : Base s ap i st) (hD : (stR s).Disjoint ⟨D, n⟩) (hDt : (tR s).Disjoint ⟨D, n⟩)
    (hDc : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : D.toNat + n ≤ 2 ^ 64) (hn64 : n < 2 ^ 64)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = St s) (h_cx : st.gpr .rcx = D)
    (h_8 : st.gpr .r8 = BitVec.ofNat 64 n) :
    aadK.pre (st.callEntry.withRegions [⟨K s, 256⟩, ⟨D, n⟩] [stR s]) ∧
      Covers ([⟨K s, 256⟩, ⟨D, n⟩] ++ [stR s]) (st.rd ++ st.wr) ∧ Covers [stR s] st.wr := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hw := hp.w_w
  have kS : Region.Sub ⟨K s, 256⟩ (kR M s) := Region.sub_prefix M.ge
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  have hst : (St s).toNat = (W s).toNat + 104 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 104) (by decide)]; omega
  have hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have hpre : aadK.pre (st.callEntry.withRegions [⟨K s, 256⟩, ⟨D, n⟩] [stR s]) := by
    simp only [aadK, aadPre, Proof.AesGcm.ret, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), entry_rsp h.rsp, h_di, h_si, h_cx, h_8, hn,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, (hp.k_w.sub_left kS).sub_right stR_sub, hD,
      (hp.b_k.sub_left ret_sub).sub_right kS, (hp.b_w.sub_left ret_sub).sub_right stR_sub, hDt.sub_left ret_sub,
      (hp.b_k.sub_left (stk_sub' (by decide))).sub_right kS, (hp.b_w.sub_left (stk_sub' (by decide))).sub_right stR_sub,
      hDt.sub_left (stk_sub' (by decide)),
      by have := hp.w_k; have := M.ge; omega, by rw [hst]; omega, hDw, by rw [hsp8]; omega, by rw [hsp8]; omega⟩
  have cSt : Covers [stR s] (s.rd ++ s.wr) := by
    rw [hp.wr]
    exact covers_left (covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide)
      (by decide)) covers_nil')
  have hc : Covers ([⟨K s, 256⟩, ⟨D, n⟩] ++ [stR s]) (st.rd ++ st.wr) := by
    rw [h.rd, h.wr]
    refine covers_cons' ?_ (covers_cons' hDc (covers_cons' cSt covers_nil'))
    rw [hp.rd]; exact covers_left' (StreamTo.covers_prefix (L := M.len) (by simp) M.ge)
  have hw' : Covers [stR s] st.wr := by
    rw [h.wr, hp.wr]
    exact covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide) (by decide))
      covers_nil'
  exact ⟨hpre, hc, hw'⟩

/-- The call of `vg_aes_gcm_stream_aad(ctx, state, aad_len, data, len)` on the
state in `work`, before any text, with `n` bytes of data at `D`, readable
and apart from the state and the stack. -/
theorem aadCall_ok (F : AadFn) {ap : BitVec 64} {A : List Byte} {D : Addr} {n : Nat} {st : State}
    (h : Mid s ap 0 A st) (hD : (stR s).Disjoint ⟨D, n⟩) (hDt : (tR s).Disjoint ⟨D, n⟩)
    (hDc : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : D.toNat + n ≤ 2 ^ 64) (hn64 : n < 2 ^ 64)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = St s) (h_dx : st.gpr .rdx = BitVec.ofNat 64 A.length)
    (h_cx : st.gpr .rcx = D) (h_8 : st.gpr .r8 = BitVec.ofNat 64 n) :
    WP isa (.call F.fn.name F.fn.code) st (Mid s ap 0 (A ++ bytesAt st.mem D n)) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  obtain ⟨hpre, hc, hw'⟩ := aadEntry hp h.toBase hD hDt hDc hDw hn64 h_di h_si h_cx h_8
  refine WP.mono (call0_ok F (by decide) h.rsp hpre hc hw') fun st' ⟨hcs, hrd, hwr, hf, s₂, hm, hpost⟩ => ?_
  have fU := entry_frame h.rsp h.frame [⟨K s, 256⟩, ⟨D, n⟩] [stR s]
  have fK := entry_keep h.rsp [⟨K s, 256⟩, ⟨D, n⟩] [stR s]
  rw [State.withRegions_mem] at fU fK
  simp only [aadK, Proof.AesGcm.streamAadX86_64, State.withRegions_mem,
    entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), h_di, h_si, h_dx, h_cx, h_8, hn, hk_eq hp fU, hm] at hpost
  have sr₀ : StreamRepr st.callEntry.mem (St s) (ciph s) (hk s) (iv s) A [] := by
    have := h.sr; rw [ct_zero] at this
    exact streamRepr_frame fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.b_w.symm.sub_left stR_sub) this
  have sr₁ := hpost (ciph s) (iv s) A sr₀ rfl
  rw [bytesAt_frame fK (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hDt.symm) (by omega)]
    at sr₁
  have hB := h.after hp hcs hrd hwr hf st_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  refine ⟨hB, Nat.zero_le _, by rw [ct_zero]; exact sr₁, by rw [gl_zero, ct_zero]; rfl⟩

/-! ## `vg_aes_gcm_stream_finish` -/

/-- What the call of `vg_aes_gcm_stream_finish` needs. -/
theorem finEntry {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_9 : st.gpr .r9 = Tg s) :
    finK.pre (st.callEntry.withRegions [⟨K s, 256⟩] [stR s, tgR s]) ∧
      Covers ([⟨K s, 256⟩] ++ [stR s, tgR s]) (st.rd ++ st.wr) ∧ Covers [stR s, tgR s] st.wr := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hw := hp.w_w
  have kS : Region.Sub ⟨K s, 256⟩ (kR M s) := Region.sub_prefix M.ge
  have hst : (St s).toNat = (W s).toNat + 104 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 104) (by decide)]; omega
  have hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have hpre : finK.pre (st.callEntry.withRegions [⟨K s, 256⟩] [stR s, tgR s]) := by
    simp only [finK, finPre, Proof.AesGcm.ret, Proof.AesGcm.rounds, entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp),
      entry_gpr _ _ (by decide : Reg.r9 ≠ .rsp), entry_rsp h.rsp, h_di, h_si, h_dx, h_9,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, (hp.k_w.sub_left kS).sub_right stR_sub, hp.k_t.sub_left kS,
      hp.t_w.symm.sub_left stR_sub,
      (hp.b_k.sub_left ret_sub).sub_right kS, (hp.b_w.sub_left ret_sub).sub_right stR_sub, hp.b_t.sub_left ret_sub,
      (hp.b_k.sub_left (stk_sub' (by decide))).sub_right kS, (hp.b_w.sub_left (stk_sub' (by decide))).sub_right stR_sub,
      hp.b_t.sub_left (stk_sub' (by decide)),
      by have := hp.w_k; have := M.ge; omega, by rw [hst]; omega, hp.w_t, by rw [hsp8]; omega, by rw [hsp8]; omega,
      hp.rounds⟩
  have cSt : Covers [stR s] (s.rd ++ s.wr) := by
    rw [hp.wr]
    exact covers_left (covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide)
      (by decide)) covers_nil')
  have hw' : Covers [stR s, tgR s] st.wr := by
    rw [h.wr, hp.wr]
    exact covers_cons' (StreamTo.covers_off (k := 184) (d := 104) (m := 80) (by simp) (by decide) (by decide))
      (covers_cons' (covers_of_mem (by simp)) covers_nil')
  have hc : Covers ([⟨K s, 256⟩] ++ [stR s, tgR s]) (st.rd ++ st.wr) := by
    refine covers_cons' ?_ (covers_left hw')
    rw [h.rd, h.wr, hp.rd]; exact covers_left' (StreamTo.covers_prefix (L := M.len) (by simp) M.ge)
  exact ⟨hpre, hc, hw'⟩

/-- The call of `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len,
text_len, tag)` on the state in `work`, representing the message with the
additional data and the ciphertext `C`. -/
theorem finCall_ok (F : FinFn) {ap : BitVec 64} {i : Nat} {C : List Byte} {st : State} (h : Base s ap i st)
    (hsr : StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) (ad s) C) (hC : C.length = L s)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_cx : st.gpr .rcx = AL s) (h_8 : st.gpr .r8 = stackArg s 3) (h_9 : st.gpr .r9 = Tg s) :
    WP isa (.call F.fn.name F.fn.code) st fun st' => Base s ap i st' ∧
      Frame [stR s, tgR s, tR s] st.mem st'.mem ∧
      bytesAt st'.mem (Tg s) 16 = fullTag (ciph s) (hk s) (iv s) (ad s) C := by
  obtain ⟨hpre, hc, hw'⟩ := finEntry hp h h_di h_si h_dx h_9
  refine WP.mono (call0_ok F (by decide) h.rsp hpre hc hw') fun st' ⟨hcs, hrd, hwr, hf, s₂, hm, hpost⟩ => ?_
  have fU := entry_frame h.rsp h.frame [⟨K s, 256⟩] [stR s, tgR s]
  have fK := entry_keep h.rsp [⟨K s, 256⟩] [stR s, tgR s]
  rw [State.withRegions_mem] at fU fK
  simp only [finK, Proof.AesGcm.streamFinishX86_64, State.withRegions_mem,
    entry_gpr _ _ (by decide : Reg.rdi ≠ .rsp), entry_gpr _ _ (by decide : Reg.rsi ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.rdx ≠ .rsp), entry_gpr _ _ (by decide : Reg.rcx ≠ .rsp),
    entry_gpr _ _ (by decide : Reg.r8 ≠ .rsp), entry_gpr _ _ (by decide : Reg.r9 ≠ .rsp), h_di, h_si, h_dx, h_cx,
    h_8, h_9, ciph_eq hp fU, hk_eq hp fU, hm] at hpost
  have sr₀ : StreamRepr st.callEntry.mem (St s) (ciph s) (hk s) (iv s) (ad s) C :=
    streamRepr_frame fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.b_w.symm.sub_left stR_sub) hsr
  have hB := h.after hp hcs hrd hwr hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wkR s, by simp, stR_sub⟩
      · exact ⟨tgR s, by simp, fun _ h => h⟩)
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kpR_stR
      · exact hp.t_w.symm.sub_left kpR_sub
  exact ⟨hB, hf, hpost (iv s) (ad s) C sr₀ (by rw [Cmac.bytesAt_length, ofNat_toNat]) (by rw [hC])⟩

end

end VG.Proof.AesGcm.X86_64.Gather

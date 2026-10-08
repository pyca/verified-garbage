import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the call of a slice

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_stream_encrypt_to` on slice `i`, to the output after the `gl i`
bytes of the slices before it, with its length, where it goes and its
length again pushed for it (`toCall_ok`): what it needs, from the layout of
the entry state `s` (`toEntry`), and what it leaves.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block StreamRepr ctxCiph ctxH gctr inc32 j0)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' streamRepr_frame sub_add_ofNat stackArg_entry)

section
variable (s : State)

/-- Where slice `i` goes in the output. -/
abbrev dqR (i : Nat) : Region := ⟨Dst s + BitVec.ofNat 64 (gl s i), sl s i⟩
/-- Slice `i`. -/
abbrev slR (i : Nat) : Region := ⟨sb s i, sl s i⟩

/-- What the call reads and writes. -/
abbrev toRd (M : CtxMode) (i : Nat) : List Region := [kR M s, slR s i, ⟨SP s - BitVec.ofNat 64 24, 24⟩]
abbrev toWr (i : Nat) : List Region := [stR s, dqR s i]

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

theorem dq_sub {i : Nat} (hi : i < Cnt s) : (dqR s i).Sub (dR s) := Offset.sub_base _ (gl_succ_le hp hi)

omit hp in
/-- A region of the stack below `SP - a`, in the stack the calls use. -/
theorem stk_sub {a n : Nat} (ha : a ≤ 4888) (hn : n ≤ a) :
    Region.Sub ⟨SP s - BitVec.ofNat 64 a, n⟩ (tR s) := Offset.sub_below _ (by omega) (by omega)

omit hp in
/-- A frame of a region of the stack below `SP - a` is one of the stack the
calls use. -/
theorem frame_stk {m m' : Mem} {a n : Nat} (ha : a ≤ 4888) (hn : n ≤ a)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 a, n⟩] m m') : Frame (wR s ++ [tR s]) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨tR s, by simp, stk_sub (s := s) ha hn⟩

/-- What the call of `vg_aes_gcm_stream_encrypt_to` needs. -/
theorem toPre_of {i : Nat} (hi : i < Cnt s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 32) (hrd : u.rd = toRd s M i) (hwr : u.wr = toWr s i)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s)
    (h_9 : u.gpr .r9 = sb s i) (a0 : stackArg u 0 = BitVec.ofNat 64 (sl s i))
    (a1 : stackArg u 1 = Dst s + BitVec.ofNat 64 (gl s i)) (a2 : stackArg u 2 = BitVec.ofNat 64 (sl s i))
    (hok : M.ok u.mem (K s)) :
    (toK M).pre u := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  have hsl : (BitVec.ofNat 64 (sl s i)).toNat = sl s i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hw := hp.w_w
  have ls := hp.ls _ (slice_mem s hi)
  have ds := dq_sub hp hi
  have hargs : (Proof.AesGcm.args u 3) = ⟨SP s - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : below (SP s - BitVec.ofNat 64 32) 4856 = ⟨SP s - BitVec.ofNat 64 4888, 4856⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 24, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 32, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 4888, 4856⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have hst : (St s).toNat = (W s).toNat + 104 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 104) (by decide)]; omega
  have hdq : (Dst s + BitVec.ofNat 64 (gl s i)).toNat + sl s i ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos (sl s i) with h0 | h0
    · rw [h0]; have := (Dst s + BitVec.ofNat 64 (gl s i)).isLt; omega
    · have := hp.w_d
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := gl s i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hsp32 : (SP s - BitVec.ofNat 64 32).toNat = (SP s).toNat - 32 := toNat_sub_ofNat (by omega)
  have hsp24 : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have hsp4888 : (SP s - BitVec.ofNat 64 4888).toNat = (SP s).toNat - 4888 := toNat_sub_ofNat (by omega)
  have d₁ : (⟨SP s - BitVec.ofNat 64 32, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp32, hsp24]; omega) (by simp only [hsp24]; omega)
  have d₂ : (⟨SP s - BitVec.ofNat 64 4888, 4856⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp4888, hsp24]; omega) (by simp only [hsp24]; omega)
  have wls := hp.w_ls _ (slice_mem s hi)
  simp only [toK, toPre, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_9, a0, a1, a2, hsl,
    hrsp, Proof.AesGcm.rounds, hstk]
  refine ⟨trivial, trivial, trivial, hp.k_w.sub_right stR_sub, hp.k_d.sub_right ds,
    ls.2.2.symm.sub_left stR_sub, (hp.d_w.symm.sub_left stR_sub).sub_right ds,
    (hp.b_w.symm.sub_left stR_sub).sub_right tA, ls.1.sub_right ds, (hp.b_d.symm.sub_left ds).sub_right tA,
    hp.b_k.sub_left tR', (hp.b_w.sub_left tR').sub_right stR_sub, (hp.b_ls _ (slice_mem s hi)).sub_left tR',
    (hp.b_d.sub_left tR').sub_right ds, d₁,
    hp.b_k.sub_left tS, (hp.b_w.sub_left tS).sub_right stR_sub, (hp.b_ls _ (slice_mem s hi)).sub_left tS,
    (hp.b_d.sub_left tS).sub_right ds, d₂,
    hp.w_k, by rw [hst]; omega, by simpa using wls, hdq,
    by rw [hsp32]; omega, by rw [hsp32]; omega, hp.rounds, hok⟩

/-- What the call of `vg_aes_gcm_stream_encrypt_to` needs, after the push. -/
theorem toEntry {ap : BitVec 64} {i : Nat} (hi : i < Cnt s) {st : State} (h : Base s ap i st)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_9 : st.gpr .r9 = sb s i) (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 (gl s i))
    (h_ax : st.gpr .rax = BitVec.ofNat 64 (sl s i)) :
    (toK M).pre ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)) ∧
      Covers (toRd s M i ++ toWr s i) ((pushed [.rax, .r10, .rax] st).rd ++ (pushed [.rax, .r10, .rax] st).wr) ∧
      Covers (toWr s i) (pushed [.rax, .r10, .rax] st).wr ∧
      stackArg ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)) 0 =
        BitVec.ofNat 64 (sl s i) ∧
      stackArg ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)) 1 =
        Dst s + BitVec.ofNat 64 (gl s i) ∧
      stackArg ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)) 2 =
        BitVec.ofNat 64 (sl s i) := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hn8 : 8 * [Reg.rax, .r10, .rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .rax] (by decide) hn8
  have hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r10, .rax] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r10, .rax][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r10, .rax] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .rax] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .rax] st).mem
      (pushed [.rax, .r10, .rax] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .rax] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .rax] st).callEntry.mem :=
    (h.frame.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans
      (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega)
  have ea : ∀ j, j < 3 → stackArg ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)) j =
      (pushed [.rax, .r10, .rax] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * j)) 64 :=
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
      ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have hok : M.ok ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_apart hp) hp.w_k hp.ok
  have hpre := toPre_of hp hi hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_9) (by rw [a0, h_ax])
    (by rw [a1, h_10]) (by rw [a2, h_ax]) hok
  have hPw : (pushed [.rax, .r10, .rax] st).wr = ⟨SP s - BitVec.ofNat 64 24, 24⟩ :: wR s := by
    rw [pushed_wr, hsp, h.wr, hp.wr]; rfl
  have hPr : (pushed [.rax, .r10, .rax] st).rd = [kR M s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] := by
    rw [pushed_rd, h.rd, hp.rd]
  have cSt : ∀ {ts : List Region}, wkR s ∈ ts → Covers [stR s] ts := fun h =>
    StreamTo.covers_off (k := 184) (d := 104) (m := 80) h (by decide) (by decide)
  have cDq : ∀ {ts : List Region}, dR s ∈ ts → Covers [dqR s i] ts := fun h =>
    StreamTo.covers_off (k := L s) (d := gl s i) (m := sl s i) h (gl_succ_le hp hi)
      (by have := gl_succ_le hp hi; omega)
  have cw : Covers (toWr s i) (pushed [.rax, .r10, .rax] st).wr := by
    rw [hPw]; exact covers_cons' (cSt (by simp)) (covers_cons' (cDq (by simp)) covers_nil')
  have cr : Covers (toRd s M i ++ toWr s i)
      ((pushed [.rax, .r10, .rax] st).rd ++ (pushed [.rax, .r10, .rax] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp [slice_mem s hi]))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cSt (by simp)) (covers_cons' (cDq (by simp))
        covers_nil'))))
  exact ⟨hpre, cr, cw, by rw [a0, h_ax], by rw [a1, h_10], by rw [a2, h_ax]⟩


/-- The call of `vg_aes_gcm_stream_encrypt_to` on slice `i`, to the output
after the `gl i` bytes of the slices before it, with the length of the
additional data so far `ap` and the slice's length, where it goes and its
length again pushed for it. -/
theorem toCall_ok (T : ToFn M) {ap : BitVec 64} {i : Nat} (hi : i < Cnt s) {st : State} (h : Base s ap i st)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_cx : st.gpr .rcx = ap) (h_8 : st.gpr .r8 = BitVec.ofNat 64 (gl s i)) (h_9 : st.gpr .r9 = sb s i)
    (h_10 : st.gpr .r10 = Dst s + BitVec.ofNat 64 (gl s i)) (h_ax : st.gpr .rax = BitVec.ofNat 64 (sl s i)) :
    WP isa (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (toWr s i ++ [tR s]) st.mem st'.mem ∧
      ∀ iv a p, StreamRepr st.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
        ap = BitVec.ofNat 64 a.length → gl s i = p.length →
        StreamRepr st'.mem (St s) (ciph s) (hk s) iv a
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (sb s i) (sl s i))) ∧
          bytesAt st'.mem (Dst s + BitVec.ofNat 64 (gl s i)) (sl s i) =
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (sb s i) (sl s i))).drop p.length := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .rax].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax, .r10, .rax] (by decide) hn8
  have hP : (pushed [.rax, .r10, .rax] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .rax] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .rax] st).mem
      (pushed [.rax, .r10, .rax] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .rax] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .rax] st).callEntry.mem :=
    (h.frame.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans
      (frame_stk (s := s) (by decide) (by decide) hE)
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .rax] st).callEntry.withRegions (toRd s M i) (toWr s i)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain ⟨hpre, cr, cw, a0, a1, -⟩ := toEntry hp hi h h_di h_si h_dx h_9 h_10 h_ax
  -- What the push and the return address leave as it was.
  have fS : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩, ⟨SP s - BitVec.ofNat 64 32, 8⟩] st.mem
      (pushed [.rax, .r10, .rax] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  have outT : ∀ {r : Region}, r.Disjoint (tR s) →
      ∀ r' ∈ [(⟨SP s - BitVec.ofNat 64 24, 24⟩ : Region), ⟨SP s - BitVec.ofNat 64 32, 8⟩], r.Disjoint r' := by
    intro r hd r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
  have hsl : (BitVec.ofNat 64 (sl s i)).toNat = sl s i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hgl : (BitVec.ofNat 64 (gl s i)).toNat = gl s i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have eS : bytesAt (pushed [.rax, .r10, .rax] st).callEntry.mem (sb s i) (sl s i) = bytesAt s.mem (sb s i) (sl s i) :=
    slice_eq hp fU hi
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := toK M)
    T.ok T.sp (by have := T.xd; omega) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [toK, Proof.AesGcm.streamToPost, Proof.AesGcm.arg, a0, a1, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    h_di, h_si, h_dx, h_cx, h_8, h_9, hm₂, ciph_eq hp fU, hk_eq hp fU, eS, hsl, hgl] at hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, fun iv a p hr hal hpl => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    have b4888 : Region.Sub (below ((pushed [.rax, .r10, .rax] st).gpr .rsp) (T.fn.code.x86_64Depth + 8)) (tR s) := by
      have h₁ := below_sub (sp := (pushed [.rax, .r10, .rax] st).gpr .rsp) (a := T.fn.code.x86_64Depth + 8)
        (b := 4864) (by have := T.xd; omega) (by decide)
      have e : below (SP s - BitVec.ofNat 64 24) 4864 = ⟨SP s - BitVec.ofNat 64 4888, 4864⟩ := by
        simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
      rw [hP] at h₁ ⊢
      rw [e] at h₁
      exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨tR s, by simp, b4888⟩
  · rw [popped_mem]
    exact hpost iv a p (streamRepr_frame fS (outT (hp.b_w.symm.sub_left stR_sub)) hr) hal hpl

end

end VG.Proof.AesGcm.X86_64.Gather

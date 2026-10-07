import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall

/-!
# AES-GCM streaming encryption out of place, x86-64: the call of the bytes left

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at `Dst + o`, with
their number pushed for it (`encCall_ok`): what it needs, from the layout of
`s` (`encPre`), and what it leaves.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

/-- The bytes left of the output, after `o` done. -/
abbrev dqR (o : Nat) : Region := ⟨Dst s + BitVec.ofNat 64 o, L s - o⟩

/-- What the call reads and writes. -/
abbrev encRd (M : CtxMode) : List Region := [kR M s, ⟨SP s - BitVec.ofNat 64 8, 8⟩]
abbrev encWr (o : Nat) : List Region := [stR s, dqR s o]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem dq_sub {o : Nat} (ho : o ≤ L s) : (dqR s o).Sub (dR s) := Offset.sub_base _ (by omega)

/-- What the call of `vg_aes_gcm_stream_encrypt` needs. -/
theorem encPre {o : Nat} (ho : o < L s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 16) (hrd : u.rd = encRd s M) (hwr : u.wr = encWr s o)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s)
    (h_9 : u.gpr .r9 = Dst s + BitVec.ofNat 64 o) (a0 : stackArg u 0 = BitVec.ofNat 64 (L s - o))
    (hok : M.ok u.mem (K s)) :
    (encK M).pre u := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hn : (BitVec.ofNat 64 (L s - o)).toNat = L s - o := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have wt := hp.w_t
  have wsp := hp.w_sp
  have ds := dq_sub (s := s) (Nat.le_of_lt ho)
  have hargs : (Proof.AesGcm.args u 1) = ⟨SP s - BitVec.ofNat 64 8, 8⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 16, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : below (SP s - BitVec.ofNat 64 16) 2608 = ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 8, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 16, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have ho' : o < 2 ^ 64 := by omega
  have hdq : (Dst s + BitVec.ofNat 64 o).toNat = (Dst s).toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) ho']
    have := hp.w_d; omega
  have hsp16 : (SP s - BitVec.ofNat 64 16).toNat = (SP s).toNat - 16 := toNat_sub_ofNat (by omega)
  have hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have hsp2624 : (SP s - BitVec.ofNat 64 2624).toNat = (SP s).toNat - 2624 := toNat_sub_ofNat (by omega)
  have d₁ : (⟨SP s - BitVec.ofNat 64 16, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp16, hsp8]; omega) (by simp only [hsp8]; omega)
  have d₂ : (⟨SP s - BitVec.ofNat 64 2624, 2608⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2624, hsp8]; omega) (by simp only [hsp8]; omega)
  simp only [encK, encCallPre, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_9, a0, hn,
    hrsp, Proof.AesGcm.rounds, hstk]
  refine ⟨trivial, trivial, hp.k_st, hp.k_d.sub_right ds, hp.st_d.sub_right ds, hp.b_st.symm.sub_right tA,
    hp.b_d.symm.sub_left ds |>.sub_right tA,
    hp.b_k.sub_left tR', hp.b_st.sub_left tR', (hp.b_d.sub_left tR').sub_right ds,
    d₁,
    hp.b_k.sub_left tS, hp.b_st.sub_left tS, (hp.b_d.sub_left tS).sub_right ds,
    d₂,
    hp.w_k, hp.w_st, by rw [hdq]; have := hp.w_d; omega, by rw [hsp16]; omega, by rw [hsp16]; omega, hp.rounds,
    hok⟩

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the call of `vg_aes_gcm_stream_encrypt` needs, after the push. -/
theorem encEntry {o : Nat} (ho : o < L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (L s - o)) :
    (encK M).pre ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)) ∧
      Covers (encRd s M ++ encWr s o) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) ∧
      Covers (encWr s o) (pushed [.r10] st).wr ∧
      stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)) 0 = BitVec.ofNat 64 (L s - o) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  have hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  have hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)) 0 = BitVec.ofNat 64 (L s - o) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  have gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have hok : M.ok ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)).mem (K s) := by
    rw [State.withRegions_mem]; exact M.frame fU (k_disj hp) hp.w_k hp.ok
  have hpre := encPre hp ho hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_9) a0 hok
  have hPw : (pushed [.r10] st).wr = ⟨SP s - BitVec.ofNat 64 8, 8⟩ :: wR s := by
    rw [pushed_wr, hsp, hwr, hp.wr]; rfl
  have hPr : (pushed [.r10] st).rd = [kR M s, srcR s, aR s] := by rw [pushed_rd, hrd, hp.rd]
  have cDq : ∀ {ts : List Region}, dR s ∈ ts → Covers [dqR s o] ts := fun h =>
    covers_off (k := L s) (d := o) (m := L s - o) h (by omega) (by omega)
  have cw : Covers (encWr s o) (pushed [.r10] st).wr := by
    rw [hPw]; exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')
  have cr : Covers (encRd s M ++ encWr s o) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')))
  exact ⟨hpre, cr, cw, a0⟩

/-- The call of `vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at
`Dst + o`, with their number pushed for it. -/
theorem encCall_ok (E : EncFn M) {o : Nat} (ho : o < L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_cx : st.gpr .rcx = AL s) (h_8 : st.gpr .r8 = TL s + BitVec.ofNat 64 o)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (L s - o)) :
    WP isa (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (encWr s o ++ [tR s]) st.mem st'.mem ∧
      ∀ iv a p, StreamRepr st.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
        AL s = BitVec.ofNat 64 a.length → (TL s + BitVec.ofNat 64 o).toNat = p.length →
        StreamRepr st'.mem (St s) (ciph s) (hk s) iv a
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (L s - o))) ∧
          bytesAt st'.mem (Dst s + BitVec.ofNat 64 o) (L s - o) =
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (L s - o))).drop
              p.length := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  have hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  have hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega)
  have a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)) 0 = BitVec.ofNat 64 (L s - o) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  have gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain ⟨hpre, cr, cw, -⟩ := encEntry hp ho hsp hrd hwr hf h_di h_si h_dx h_9 h_10
  -- What the push and the return address leave as it was.
  have fS : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩, ⟨SP s - BitVec.ofNat 64 16, 8⟩] st.mem
      (pushed [.r10] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  have outT : ∀ {r : Region}, r.Disjoint (tR s) →
      ∀ r' ∈ [(⟨SP s - BitVec.ofNat 64 8, 8⟩ : Region), ⟨SP s - BitVec.ofNat 64 16, 8⟩], r.Disjoint r' := by
    intro r hd r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
  have dsq := dq_sub (s := s) (Nat.le_of_lt ho)
  have eD : bytesAt (pushed [.r10] st).callEntry.mem (Dst s + BitVec.ofNat 64 o) (L s - o) =
      bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    bytesAt_frame fS (outT (hp.b_d.symm.sub_left dsq)) (by omega)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := encK M)
    E.ok E.sp (by have := E.xd; omega) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [encK, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.arg, a0, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    h_di, h_si, h_dx, h_cx, h_8, h_9, hm₂, ciph_eq hp fU, hk_eq hp fU, eD] at hpost
  have hn : (BitVec.ofNat 64 (L s - o)).toNat = L s - o := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hn] at hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, fun iv a p hr hal hpl => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    have b2616 : Region.Sub (below ((pushed [.r10] st).gpr .rsp) (E.fn.code.x86_64Depth + 8)) (tR s) := by
      have h₁ := below_sub (sp := (pushed [.r10] st).gpr .rsp) (a := E.fn.code.x86_64Depth + 8) (b := 2616)
        (by have := E.xd; omega) (by decide)
      have e : below (SP s - BitVec.ofNat 64 8) 2616 = ⟨SP s - BitVec.ofNat 64 2624, 2616⟩ := by
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
        exact ⟨tR s, by simp, b2616⟩
  · rw [popped_mem]
    have := hpost iv a p (streamRepr_frame fS (outT hp.b_st.symm) hr) hal hpl
    rwa [eD] at this

end

end VG.Proof.AesGcm.X86_64.StreamTo

module

public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Mid
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `AesGcm.X86_64.StreamTo.EncCall`, which only this module used -/

section

/-!
# AES-GCM streaming encryption out of place, x86-64: the call of the bytes left

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at `Dst + o`, with
their number pushed for it (`encCall_ok`): what it needs, from the layout of
`s` (`encPre`), and what it leaves.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

/-- `n` bytes of the output, after `o` done. -/
abbrev dqR (o n : Nat) : Region := ⟨Dst s + BitVec.ofNat 64 o, n⟩

/-- What the call reads and writes. -/
abbrev encRd (M : CtxMode) : List Region := [kR M s, ⟨SP s - BitVec.ofNat 64 8, 8⟩]
abbrev encWr (o n : Nat) : List Region := [stR s, dqR s o n]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem dq_sub {o n : Nat} (hn : o + n ≤ L s) : (dqR s o n).Sub (dR s) := Offset.sub_base _ hn

/-- What the call of `vg_aes_gcm_stream_encrypt` needs. -/
theorem encPre {o n : Nat} (hn : o + n ≤ L s) {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 16) (hrd : u.rd = encRd s M) (hwr : u.wr = encWr s o n)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = St s)
    (h_9 : u.gpr .r9 = Dst s + BitVec.ofNat 64 o) (a0 : stackArg u 0 = BitVec.ofNat 64 (n))
    (hok : M.ok u.mem (K s)) :
    (encK M).pre u := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain hnn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain ds := dq_sub (s := s) hn
  obtain hargs : (Proof.AesGcm.args u 1) = ⟨SP s - BitVec.ofNat 64 8, 8⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  obtain hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 16, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  obtain hstk : below (SP s - BitVec.ofNat 64 16) 2608 = ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  obtain tA : Region.Sub ⟨SP s - BitVec.ofNat 64 8, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 16, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2624, 2608⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  obtain hsp16 : (SP s - BitVec.ofNat 64 16).toNat = (SP s).toNat - 16 := toNat_sub_ofNat (by omega_arith)
  obtain hsp8 : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain hsp2624 : (SP s - BitVec.ofNat 64 2624).toNat = (SP s).toNat - 2624 := toNat_sub_ofNat (by omega_arith)
  obtain d₁ : (⟨SP s - BitVec.ofNat 64 16, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp16, hsp8]; omega_arith) (by simp only [hsp8]; omega_arith)
  obtain d₂ : (⟨SP s - BitVec.ofNat 64 2624, 2608⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 8, 8⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2624, hsp8]; omega_arith) (by simp only [hsp8]; omega_arith)
  simp only [encK, encCallPre, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_9, a0, hnn,
    hrsp, Proof.AesGcm.rounds, hstk]
  refine ⟨trivial, trivial, hp.k_st, hp.k_d.sub_right ds, hp.st_d.sub_right ds, hp.b_st.symm.sub_right tA,
    hp.b_d.symm.sub_left ds |>.sub_right tA,
    hp.b_k.sub_left tR', hp.b_st.sub_left tR', (hp.b_d.sub_left tR').sub_right ds,
    d₁,
    hp.b_k.sub_left tS, hp.b_st.sub_left tS, (hp.b_d.sub_left tS).sub_right ds,
    d₂,
    hp.w_k, hp.w_st, off_bound hp.w_d hn, by rw [hsp16]; omega_arith, by rw [hsp16]; omega_arith, hp.rounds,
    hok⟩

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the call of `vg_aes_gcm_stream_encrypt` needs, after the push. -/
theorem encEntry {o n : Nat} (hn : o + n ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (n)) :
    (encK M).pre ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) ∧
      Covers (encRd s M ++ encWr s o n) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) ∧
      Covers (encWr s o n) (pushed [.r10] st).wr ∧
      stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  obtain hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  obtain gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain hok : M.ok ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).mem (K s) := by
    rw [State.withRegions_mem]; exact M.frame fU (k_disj hp) hp.w_k hp.ok
  obtain hpre := encPre hp hn hU rfl rfl (by rw [gU _ (by decide)]; exact h_di) (by rw [gU _ (by decide)]; exact h_si)
    (by rw [gU _ (by decide)]; exact h_dx) (by rw [gU _ (by decide)]; exact h_9) a0 hok
  obtain hPw : (pushed [.r10] st).wr = ⟨SP s - BitVec.ofNat 64 8, 8⟩ :: wR s := by
    rw [pushed_wr, hsp, hwr, hp.wr]; rfl
  obtain hPr : (pushed [.r10] st).rd = [kR M s, srcR s, aR s] := by rw [pushed_rd, hrd, hp.rd]
  obtain cDq : ∀ {ts : List Region}, dR s ∈ ts → Covers [dqR s o n] ts := fun h =>
    covers_off (k := L s) (d := o) (m := n) h (by omega_arith) (by omega_arith)
  obtain cw : Covers (encWr s o n) (pushed [.r10] st).wr := by
    rw [hPw]; exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')
  obtain cr : Covers (encRd s M ++ encWr s o n) ((pushed [.r10] st).rd ++ (pushed [.r10] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (cDq (by simp)) covers_nil')))
  exact ⟨hpre, cr, cw, a0⟩

/-- The call of `vg_aes_gcm_stream_encrypt` on the `L - o` bytes left at
`Dst + o`, with their number pushed for it. -/
theorem encCall_ok (E : EncFn M) {o n : Nat} (hn : o + n ≤ L s) {st : State}
    (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) (hf : Frame (wR s ++ [tR s]) s.mem st.mem)
    (h_di : st.gpr .rdi = K s) (h_si : st.gpr .rsi = s.gpr .rsi) (h_dx : st.gpr .rdx = St s)
    (h_cx : st.gpr .rcx = AL s) (h_8 : st.gpr .r8 = TL s + BitVec.ofNat 64 o)
    (h_9 : st.gpr .r9 = Dst s + BitVec.ofNat 64 o) (h_10 : st.gpr .r10 = BitVec.ofNat 64 (n)) :
    WP isa (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      Frame (encWr s o n ++ [tR s]) st.mem st'.mem ∧
      ∀ iv a p, StreamRepr st.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) p) →
        AL s = BitVec.ofNat 64 a.length → (TL s + BitVec.ofNat 64 o).toNat = p.length →
        StreamRepr st'.mem (St s) (ciph s) (hk s) iv a
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n))) ∧
          bytesAt st'.mem (Dst s + BitVec.ofNat 64 o) (n) =
            (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n))).drop
              p.length := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have wt := hp.w_t
  have wsp := hp.w_sp
  obtain hn8 : 8 * [Reg.r10].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.r10] (by decide) hn8
  obtain hP : (pushed [.r10] st).gpr .rsp = SP s - BitVec.ofNat 64 8 := by rw [pushed_rsp, hsp]; rfl
  obtain hpf' : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩] st.mem (pushed [.r10] st).mem := by
    rw [hsp] at hpf; exact hpf
  obtain hE : Frame [⟨SP s - BitVec.ofNat 64 16, 8⟩] (pushed [.r10] st).mem (pushed [.r10] st).callEntry.mem := by
    have := callEntry_frame (pushed [.r10] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  obtain fU : Frame (wR s ++ [tR s]) s.mem (pushed [.r10] st).callEntry.mem :=
    (hf.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans (frame_stk (s := s) (by decide) (by decide) hE)
  obtain hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  obtain hPt : (SP s - BitVec.ofNat 64 8).toNat = (SP s).toNat - 8 := toNat_sub_ofNat (by omega_arith)
  obtain a0 : stackArg ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)) 0 = BitVec.ofNat 64 (n) := by
    rw [stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith), show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * 0) =
      SP s - BitVec.ofNat 64 (8 * (0 + 1)) by simp, ← hsp]
    exact (hpj 0 (by decide)).trans h_10
  obtain gU : ∀ r, r ≠ .rsp → ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain hU : ((pushed [.r10] st).callEntry.withRegions (encRd s M) (encWr s o n)).gpr .rsp = SP s - BitVec.ofNat 64 16 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  obtain ⟨hpre, cr, cw, -⟩ := encEntry hp hn hsp hrd hwr hf h_di h_si h_dx h_9 h_10
  -- What the push and the return address leave as it was.
  obtain fS : Frame [⟨SP s - BitVec.ofNat 64 8, 8⟩, ⟨SP s - BitVec.ofNat 64 16, 8⟩] st.mem
      (pushed [.r10] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  obtain outT : ∀ {r : Region}, r.Disjoint (tR s) →
      ∀ r' ∈ [(⟨SP s - BitVec.ofNat 64 8, 8⟩ : Region), ⟨SP s - BitVec.ofNat 64 16, 8⟩], r.Disjoint r' := by
    intro r hd r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hd.sub_right (stk_sub (s := s) (by decide) (by decide))
  obtain dsq := dq_sub (s := s) hn
  obtain eD : bytesAt (pushed [.r10] st).callEntry.mem (Dst s + BitVec.ofNat 64 o) (n) =
      bytesAt st.mem (Dst s + BitVec.ofNat 64 o) (n) :=
    bytesAt_frame fS (outT (hp.b_d.symm.sub_left dsq)) (by omega_arith)
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := encK M)
    E.ok E.sp (by have := E.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  obtain r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [encK, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.arg, a0, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    h_di, h_si, h_dx, h_cx, h_8, h_9, hm₂, ciph_eq hp fU, hk_eq hp fU, eD] at hpost
  obtain hnn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [hnn] at hpost
  refine ⟨r₃, hwr', fun r hr => ?_, by rw [popped_rd, hrd', pushed_rd], by rw [popped_wr, hwr', pushed_wr]; rfl,
    ?_, fun iv a p hr hal hpl => ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP, hsp]
      show SP s - BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr']
  · rw [popped_mem]
    obtain b2616 : Region.Sub (below ((pushed [.r10] st).gpr .rsp) (E.fn.code.x86_64Depth + 8)) (tR s) := by
      obtain h₁ := below_sub (sp := (pushed [.r10] st).gpr .rsp) (a := E.fn.code.x86_64Depth + 8) (b := 2616)
        (by have := E.xd; omega_arith) (by decide)
      obtain e : below (SP s - BitVec.ofNat 64 8) 2616 = ⟨SP s - BitVec.ofNat 64 2624, 2616⟩ := by
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

end

end


/-!
# AES-GCM streaming encryption out of place, x86-64: the bytes left

Untrusted: everything here is checked by Lean. `rest` from `Mid s o`: the
`L - o` bytes left, if any, copied from the plaintext to the output and
encrypted there by `vg_aes_gcm_stream_encrypt` as the continuation of the
text so far and the first `o` bytes, make the whole encryption (`rest_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.streamToPost s s'

/-- The encryption of a text in two pieces, past the first `k ≤ |x|` bytes. -/
theorem gctr_drop (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb : Spec.Gcm.Block) {x y : List Byte} {k : Nat}
    (hk : k ≤ x.length) :
    (gctr ciph icb (x ++ y)).drop k = (gctr ciph icb x).drop k ++ (gctr ciph icb (x ++ y)).drop x.length := by
  rw [Proof.Gcm.gctr_append, List.drop_append_of_le_length (by rw [Proof.Gcm.length_gctr]; exact hk),
    List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `work` from the stack, and the bytes left, `L - o`. -/
theorem restHead_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧ st'.gpr .rax = BitVec.ofNat 64 o ∧
      st'.zf = some (decide (L s - o = 0)) ∧
      (∀ r, r ≠ .r11 → r ≠ .rcx → r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  obtain a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  obtain hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  obtain r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain hsub := ofNat_sub ho hL
  obtain hz := and_self_beq (show L s - o < 2 ^ 64 by omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wLen, wDone]; xrun [a₃, hW, r₆, r₈, hlen, h.kept.done, hsub], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, hsub]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hsub, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The pointers of the copy: past the `o` bytes done. -/
theorem restPtrs_ok {o : Nat} {st : State} (h : Mid s o st) (h11 : st.gpr .r11 = W s)
    (hax : st.gpr .rax = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) st fun st' =>
      st'.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st'.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain r₅ := slot_in hp h.rd h.wr (d := 40) (by decide)
  obtain r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wSrc, wDst]; xrun [h11, hax, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The arguments of `vg_aes_gcm_stream_encrypt` on the bytes left. -/
theorem restArgs_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block restArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st'.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
      st'.gpr .r10 = BitVec.ofNat 64 (L s - o) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  obtain a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  obtain hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  obtain r₀ := slot_in hp h.rd h.wr (d := 0) (by decide)
  obtain r₁ := slot_in hp h.rd h.wr (d := 8) (by decide)
  obtain r₂ := slot_in hp h.rd h.wr (d := 16) (by decide)
  obtain r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  obtain r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  obtain r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  obtain r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  obtain r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  obtain k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  obtain hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  obtain hsub := ofNat_sub ho hL
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [restArgs, wCtx, wRounds, wState, wAad, wTlen, wLen, wDst, wDone]
    xrun [a₃, hW, r₀, r₁, r₂, r₃, r₄, r₆, r₇, r₈, k0, h.kept.rounds, h.kept.st, h.kept.aad, h.kept.tl, hlen,
      h.kept.dst, h.kept.done, hsub],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags, hsub]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The return address is apart from what the code writes. -/
theorem ret_disj : ∀ r ∈ wR s ++ [tR s], (⟨SP s, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.t_st, hp.t_d, hp.t_w, Offset.base_disjoint_below _ (by have := hp.w_sp; omega_arith)]

/-- With every byte done, `Mid` is the end. -/
theorem done_of {st : State} (h : Mid s (L s) st) : Done s st :=
  ⟨⟨h.saved, h.frame.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩,
    fun iv a p hr hal hpl => h.sem iv a p hr hal hpl⟩

/-- `Mid` through the copy, which writes only `n` bytes of the output past
the `o` bytes done. -/
theorem Mid.copy {o n : Nat} {st st' : State} (h : Mid s o st) (hn : o + n ≤ L s)
    (hf : Frame [dqR s o n] st.mem st'.mem) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r)
    (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) (hmx : st'.mxcsr = st.mxcsr) : Mid s o st' := by
  obtain ds := dq_sub (s := s) hn
  obtain one : ∀ {r : Region}, r.Disjoint (dqR s o n) → ∀ r' ∈ [dqR s o n], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf (one ((hp.d_w.symm.sub_left kR'_sub).sub_right ds)),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩),
    fun iv a p hr hal hpl => ?_, hmx.trans h.mx⟩
  obtain ⟨sr, dd⟩ := h.sem iv a p hr hal hpl
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨streamRepr_frame hf (one (hp.st_d.sub_right ds)) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (one (Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_arith))) (by omega_arith)

/-- `rest`, from `Mid s o`: the end. -/
theorem rest_ok (E : EncFn M) {o : Nat} {st : State} (h : Mid s o st) : WP isa (rest E.fn) st (Done s) := by
  obtain hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  unfold rest
  refine WP.seq (WP.mono_mx (by decide) (restHead_ok hp h) fun s₁ ⟨r11₁, cx₁, ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ mx_s₁ => ?_)
  obtain M₁ : Mid s o s₁ := h.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁ mx_s₁
  refine WP.ite (decide (L s - o = 0)) (by simp only [eval, z₁]) (fun e => ?_) (fun e => ?_)
  · have hoL : o = L s := by simp at e; omega_arith
    exact WP.block_nil (done_of hp (hoL ▸ M₁))
  obtain hlt : o < L s := by simp at e; omega_arith
  refine WP.seq (WP.mono_mx (by decide) (restPtrs_ok hp M₁ r11₁ ax₁) fun s₂ ⟨si₂, di₂, g₂, m₂, rd₂, wr₂⟩ mx_s₂ => ?_)
  obtain M₂ : Mid s o s₂ := M₁.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂ mx_s₂
  obtain ds := dq_sub (s := s) (o := o) (n := L s - o) (by omega_arith)
  obtain ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega_arith)
  obtain cp : CopyPre s₂ (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si₂, di₂, by rw [g₂ _ (by decide) (by decide), cx₁], by omega_arith, by omega_arith,
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega_arith) (by omega_arith),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega_arith) (by omega_arith),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.seq (WP.mono_mx (by decide) (copyLoopL_ok s₂ cp) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ mx_s₃ => ?_)
  obtain f₃ : Frame [dqR s o (L s - o)] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain M₃ : Mid s o s₃ := M₂.copy hp (by omega_arith) f₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃ mx_s₃
  obtain hX₃ : bytesAt s₃.mem (Dst s + BitVec.ofNat 64 o) (L s - o) = bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    obtain e := bytesAt_writeBytes_self s₂.mem (Dst s + BitVec.ofNat 64 o)
      (bytesAt s₂.mem (Src s + BitVec.ofNat 64 o) (L s - o)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at e
    rw [m₃, e]
    exact bytesAt_frame M₂.frame (fun r hr => (r_disj hp r hr).sub_left ss) (by omega_arith)
  refine WP.seq (WP.mono_mx (by decide) (restArgs_ok hp M₃) fun s₄ ⟨di, si, dx, cx, r8, r9, r10, cs₄, m₄, rd₄, wr₄⟩ mx_s₄ => ?_)
  obtain M₄ : Mid s o s₄ := M₃.regs m₄ cs₄ rd₄ wr₄ mx_s₄
  refine WP.mono (encCall_ok hp E (n := L s - o) (by omega_arith) M₄.rsp M₄.rd M₄.wr M₄.frame di si dx cx r8 r9 r10)
    fun s₅ ⟨cs₅, rd₅, wr₅, f₅, post⟩ => ?_
  obtain f₅' : Frame (wR s ++ [tR s]) s.mem s₅.mem := M₄.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨stR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, ds⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩)
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr],
    f₅'.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩, fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr₄, dd₄⟩ := M₄.sem iv a p hr hal hpl
  obtain hpl' : (TL s + BitVec.ofNat 64 o).toNat = (p ++ pt s o).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt M₄.tl,
      List.length_append, length_bytesAt]
    show (TL s).toNat + o = p.length + o
    rw [hpl]
  obtain ⟨sr₅, dd₅⟩ := post iv a (p ++ pt s o) sr₄ hal hpl'
  rw [m₄, hX₃] at sr₅ dd₅
  obtain hP : p ++ bytesAt s.mem (Src s) (L s) = p ++ pt s o ++ bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' ho]
  show StreamRepr s₅.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))) ∧
    bytesAt s₅.mem (Dst s) (L s) = (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))).drop p.length
  rw [hP]
  refine ⟨sr₅, ?_⟩
  obtain hD : bytesAt s₅.mem (Dst s) o = bytesAt s₄.mem (Dst s) o := by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact (hp.st_d.symm.sub_left (Region.sub_prefix ho))
    · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_arith)
    · exact hp.b_d.symm.sub_left (Region.sub_prefix ho)
  rw [← Nat.add_sub_cancel' ho, bytesAt_add, Nat.add_sub_cancel' ho, hD, dd₄, dd₅,
    gctr_drop (x := p ++ pt s o) (k := p.length) _ _ (by rw [List.length_append]; omega_arith)]

end

end VG.Proof.AesGcm.X86_64.StreamTo

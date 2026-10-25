module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitPath
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCallee
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the call of `vg_aes_gcm_seal_split`

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_seal_split` on the first slice where it is and the slices after
it gathered in the output after it, with `src`, `src_len`, `dst`, `len` and
`tag` pushed for it and `ctx` and `rounds` loaded from `work` above them
(`splitCall_ok`): what it needs, from the layout of the entry state `s`
(`splitPre_of`), and that what it leaves is what `vg_aes_gcm_seal_gather`
must (`Done`); and the whole path of such a text (`copySplit_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat stackArg_entry)

section
variable (s : State)

/-- The first slice (empty, at the descriptors, if there is none). -/
abbrev fR : Region := ⟨fb s, fl s⟩

/-- What the call reads. -/
abbrev splitRd (M : CtxMode) : List Region := [kR M s, nR s, aR s, fR s, ⟨SP s - BitVec.ofNat 64 40, 40⟩]

end

/-- A region of the caller's is one of those with one more pushed. -/
theorem in_cons {rd wr : List Region} {x : Region} {a : Addr} {n : Nat} (h : InRegions (rd ++ wr) a n) :
    InRegions (rd ++ x :: wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, ?_, hc⟩
  simp only [List.mem_append, List.mem_cons] at hr ⊢
  rcases hr with hr | hr
  exacts [Or.inl hr, Or.inr (Or.inr hr)]

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

omit hp in
/-- What is disjoint from every slice is disjoint from the first. -/
theorem fR_disj {r : Region} (h : ∀ q ∈ lsR s, q.Disjoint r) : (fR s).Disjoint r := by
  by_cases hc : Cnt s = 0
  · have e : (fR s).len = 0 := by show fl s = 0; simp only [fl_eq, hc, ↓reduceIte]
    intro a ha _
    unfold Region.Contains at ha
    omega_arith
  · have e : fR s = ⟨sb s 0, sl s 0⟩ := by
      show (⟨fb s, fl s⟩ : Region) = _
      simp only [fl_eq, fb, hc, ↓reduceIte]
    rw [e]; exact h _ (slice_mem s (by omega_arith))

theorem fR_apart : Apart (fR s) s :=
  apart_of (fR_disj fun q hq => (hp.ls q hq).1) (fR_disj fun q hq => (hp.ls q hq).2.1)
    (fR_disj fun q hq => (hp.ls q hq).2.2) (fR_disj fun q hq => (hp.b_ls q hq).symm).symm

theorem fR_wrap : (fb s).toNat + fl s ≤ 2 ^ 64 := by
  by_cases hc : Cnt s = 0
  · have e : fl s = 0 := by simp only [fl_eq, hc, ↓reduceIte]
    rw [e]; exact Nat.le_of_lt (fb s).isLt
  · have e₁ : fl s = sl s 0 := by simp only [fl_eq, hc, ↓reduceIte]
    have e₂ : fb s = sb s 0 := by simp only [fb, hc, ↓reduceIte]
    have := hp.w_ls _ (slice_mem s (i := 0) (by omega_arith))
    rw [e₁, e₂]; exact this

/-- The caller may read the first slice. -/
theorem fR_covers : Covers [fR s] s.rd := by
  by_cases hc : Cnt s = 0
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have e : fl s = 0 := by simp only [fl_eq, hc, ↓reduceIte]
    refine ⟨dsR s, by rw [hp.rd]; simp, 0, ?_, by simp only [e]; omega_arith⟩
    show fb s = Src s + BitVec.ofNat 64 0
    simp only [fb, hc, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · have e : fR s = ⟨sb s 0, sl s 0⟩ := by
      show (⟨fb s, fl s⟩ : Region) = _
      simp only [fl_eq, fb, hc, ↓reduceIte]
    rw [e, hp.rd]
    exact covers_of_mem (by simp [slice_mem s (i := 0) (by omega_arith)])

/-- What the call of `vg_aes_gcm_seal_split` needs. -/
theorem splitPre_of {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 48) (hrd : u.rd = splitRd s M) (hwr : u.wr = sealWr s)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = Nn s)
    (h_cx : u.gpr .rcx = s.gpr .rcx) (h_8 : u.gpr .r8 = Ad s) (h_9 : u.gpr .r9 = AL s)
    (a0 : stackArg u 0 = fb s) (a1 : stackArg u 1 = BitVec.ofNat 64 (fl s)) (a2 : stackArg u 2 = Dst s)
    (a3 : stackArg u 3 = stackArg s 3) (a4 : stackArg u 4 = Tg s) (hok : M.ok u.mem (K s)) :
    (splitK M).pre u := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hfl := fl_le hp
  have hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  have hargs : (Proof.AesGcm.args u 5) = ⟨SP s - BitVec.ofNat 64 40, 40⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 48, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : below (SP s - BitVec.ofNat 64 48) 2672 = ⟨SP s - BitVec.ofNat 64 2720, 2672⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 40, 40⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 48, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2720, 2672⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have hsp48 : (SP s - BitVec.ofNat 64 48).toNat = (SP s).toNat - 48 := toNat_sub_ofNat (by omega_arith)
  have hsp40 : (SP s - BitVec.ofNat 64 40).toNat = (SP s).toNat - 40 := toNat_sub_ofNat (by omega_arith)
  have hsp2720 : (SP s - BitVec.ofNat 64 2720).toNat = (SP s).toNat - 2720 := toNat_sub_ofNat (by omega_arith)
  have d₁ : (⟨SP s - BitVec.ofNat 64 48, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 40, 40⟩ :=
    Offset.disjoint_of_le (by simp only [hsp48, hsp40]; omega_arith) (by simp only [hsp40]; omega_arith)
  have d₂ : (⟨SP s - BitVec.ofNat 64 2720, 2672⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 40, 40⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2720, hsp40]; omega_arith) (by simp only [hsp40]; omega_arith)
  have bF : (tR s).Disjoint (fR s) := (fR_disj fun q hq => (hp.b_ls q hq).symm).symm
  simp only [splitK, splitPreK, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0,
    a1, a2, a3, a4, hflN, hrsp, Proof.AesGcm.rounds, hstk]
  exact ⟨trivial, trivial, hp.k_d, hp.k_t, hp.n_d, hp.n_t, hp.a_d, hp.a_t,
    fR_disj fun q hq => (hp.ls q hq).1, fR_disj fun q hq => (hp.ls q hq).2.1, hp.d_t,
    hp.b_d.symm.sub_right tA, hp.b_t.symm.sub_right tA, hp.b_k.sub_left tR', hp.b_n.sub_left tR',
    hp.b_a.sub_left tR', bF.sub_left tR', hp.b_d.sub_left tR', hp.b_t.sub_left tR', d₁, hp.b_k.sub_left tS,
    hp.b_n.sub_left tS, hp.b_a.sub_left tS, bF.sub_left tS, hp.b_d.sub_left tS, hp.b_t.sub_left tS, d₂, hp.w_k,
    hp.w_n, hp.w_ad, fR_wrap hp, hp.w_d, hp.w_t, by rw [hsp48]; omega_arith, by rw [hsp48]; omega_arith, hp.rounds, hfl,
    hok⟩

/-- What the call of `vg_aes_gcm_seal_split` needs of the state it is made
from: the stack, the callee-saved registers and the regions as on entry, the
memory as on entry but where the code writes, `ctx` and `rounds` in `work`
(for `splitCtx`), and the slices after the first in the output after it. -/
structure SCBase (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctx : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s
  rounds : st.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  out : bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)

omit hp in
theorem SPBase.toSC {st : State} (h : SPBase s st) : SCBase s st :=
  ⟨h.rsp, h.saved, h.rd, h.wr, h.frame, h.kept.ctx, h.kept.rounds, h.out⟩

/-- `work`, above the five arguments pushed. -/
theorem pushedW {st : State} (h : SCBase s st) {p : State}
    (hP : p.gpr .rsp = SP s - BitVec.ofNat 64 40) (hrd : p.rd = st.rd)
    (hwr : p.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem p.mem) :
    InRegions (p.rd ++ p.wr) (p.gpr .rsp + BitVec.ofNat 64 88) 8 ∧
      p.mem.readW (p.gpr .rsp + BitVec.ofNat 64 88) 64 = W s := by
  have e88 : p.gpr .rsp + BitVec.ofNat 64 88 = SP s + BitVec.ofNat 64 48 := by
    rw [hP, show (BitVec.ofNat 64 88 : Addr) = BitVec.ofNat 64 40 + BitVec.ofNat 64 48 from rfl,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have fP : Frame (wR s ++ [tR s]) s.mem p.mem := h.frame.trans (frame_stk (s := s) (by decide) (by decide) hf)
  refine ⟨?_, by rw [e88]; exact keep_w hp fP⟩
  rw [e88, hrd, hwr, h.rd, h.wr]; exact in_cons (a_in hp (i := 5) (by decide))

/-- `ctx` and `rounds`, from `work` above the five arguments pushed. -/
theorem splitCtx_ok {st : State} (h : SCBase s st) {p : State}
    (hP : p.gpr .rsp = SP s - BitVec.ofNat 64 40) (hrd : p.rd = st.rd)
    (hwr : p.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr)
    (hf : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem p.mem) :
    WP isa (.block splitCtx) p fun q => q.gpr .rdi = K s ∧ q.gpr .rsi = s.gpr .rsi ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r11 → q.gpr r = p.gpr r) ∧ q.mem = p.mem ∧ q.rd = p.rd ∧
      q.wr = p.wr := by
  obtain ⟨a₈, e₈⟩ := pushedW hp h hP hrd hwr hf
  have hd : ∀ r ∈ [(⟨SP s - BitVec.ofNat 64 40, 40⟩ : Region)], (kpR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.b_w.symm.sub_left kpR_sub).sub_right (stk_sub (s := s) (by decide) (by decide))
  have k : ∀ d, d + 8 ≤ 104 → p.mem.readW (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => hf.readW (Offset.contains_base _ hd' (by omega_arith)) hd (by decide)
  have kc : p.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by rw [k 0 (by decide)]; exact h.ctx
  have kr : p.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi := by rw [k 8 (by decide)]; exact h.rounds
  have r₀ : InRegions (p.rd ++ p.wr) (W s + BitVec.ofNat 64 0) 8 := by
    rw [hrd, hwr, h.rd, h.wr]; exact in_cons (w_in' hp (by decide))
  have r₁ : InRegions (p.rd ++ p.wr) (W s + BitVec.ofNat 64 8) 8 := by
    rw [hrd, hwr, h.rd, h.wr]; exact in_cons (w_in' hp (by decide))
  apply WP.of_runBlock
  refine ⟨_, by simp only [splitCtx, gCtx, gRounds]; xrun [a₈, e₈, r₀, r₁, kc, kr], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ h₃ => by simp [gpr_setReg, h₁, h₂, h₃], ?_, ?_, ?_⟩
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The registers the call of `vg_aes_gcm_seal_split` is entered with. -/
structure SplitRegs (s st : State) : Prop where
  rdx : st.gpr .rdx = Nn s
  rcx : st.gpr .rcx = s.gpr .rcx
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s
  rax : st.gpr .rax = Tg s
  r10 : st.gpr .r10 = stackArg s 3
  rdi : st.gpr .rdi = BitVec.ofNat 64 (fl s)
  rsi : st.gpr .rsi = fb s
  r11 : st.gpr .r11 = Dst s

/-- The state the call of `vg_aes_gcm_seal_split` is made from, after the
push and `splitCtx`. -/
structure SplitQ (s st q : State) : Prop where
  di : q.gpr .rdi = K s
  si : q.gpr .rsi = s.gpr .rsi
  g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r11 → q.gpr r = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr r
  m : q.mem = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
  rd : q.rd = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).rd
  wr : q.wr = (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr

/-- What the call of `vg_aes_gcm_seal_split` needs, after the push and
`splitCtx`, and its stack arguments. -/
theorem splitCallEntry {st : State} (h : SCBase s st) (g : SplitRegs s st) {q : State} (Q : SplitQ s st q) :
    (splitK M).pre (q.callEntry.withRegions (splitRd s M) (sealWr s)) ∧
      Covers (splitRd s M ++ sealWr s) (q.rd ++ q.wr) ∧ Covers (sealWr s) q.wr ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 0 = fb s ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 1 = BitVec.ofNat 64 (fl s) ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 2 = Dst s ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 3 = stackArg s 3 ∧
      stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) 4 = Tg s := by
  obtain ⟨q_di, q_si, q_g, q_m, q_rd, q_wr⟩ := Q
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hfl := fl_le hp
  have hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn8
  have hpj' : ∀ j (hj : j < 5), (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW
      (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 = st.gpr ([Reg.rax, .r10, .r11, .rdi, .rsi][j]'hj) :=
    fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hPw : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr := by
    rw [pushed_wr, hsp]; rfl
  have qsp : q.gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [q_g _ (by decide) (by decide) (by decide), hP]
  have hE : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] q.mem q.callEntry.mem := by
    have := callEntry_frame q
    rw [qsp] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have hE' : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
      q.callEntry.mem := by rw [← q_m]; exact hE
  have fS : Frame (wR s ++ [tR s]) st.mem q.callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE')
  have fU : Frame (wR s ++ [tR s]) s.mem q.callEntry.mem := h.frame.trans fS
  have gU : ∀ r, r ≠ .rsp → (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = q.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have gS : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r h₀ h₁ h₂ h₃ => by rw [gU r h₀, q_g r h₁ h₂ h₃, pushed_gpr _ _ h₀]
  have hU : (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr .rsp = SP s - BitVec.ofNat 64 48 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, qsp, ← Offset.sub_add_eq]; rfl
  have hQsp8 : 8 ≤ (SP s - BitVec.ofNat 64 40).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  have hQt : (SP s - BitVec.ofNat 64 40).toNat = (SP s).toNat - 40 := toNat_sub_ofNat (by omega_arith)
  have ea : ∀ j, j < 5 → stackArg (q.callEntry.withRegions (splitRd s M) (sealWr s)) j =
      (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW (SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * j)) 64 :=
    fun j hj => by rw [← q_m]; exact stackArg_entry qsp hQsp8 _ _ (by rw [hQt]; omega_arith)
  have a0 := ea 0 (by decide)
  have a1 := ea 1 (by decide)
  have a2 := ea 2 (by decide)
  have a3 := ea 3 (by decide)
  have a4 := ea 4 (by decide)
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (4 + 1)) from
    by simp, hpj' 4 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (3 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 3 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 2 (by decide)] at a2
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 3) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a3
  rw [show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * 4) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a4
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2 a3 a4
  rw [g.rsi] at a0
  rw [g.rdi] at a1
  rw [g.r11] at a2
  rw [g.r10] at a3
  rw [g.rax] at a4
  have hok : M.ok (q.callEntry.withRegions (splitRd s M) (sealWr s)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_apart hp) hp.w_k hp.ok
  have hpre := splitPre_of hp hU rfl rfl (by rw [gU _ (by decide), q_di]) (by rw [gU _ (by decide), q_si])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.rdx])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.rcx])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.r8])
    (by rw [gS _ (by decide) (by decide) (by decide) (by decide), g.r9]) a0 a1 a2 a3 a4 hok
  have hR : q.rd = s.rd := by rw [q_rd, pushed_rd, h.rd]
  have hW : q.wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: wR s := by rw [q_wr, hPw, h.wr, hp.wr]
  have cF : Covers [fR s] (q.rd ++ q.wr) := by rw [hR]; exact Covers.left (fR_covers hp)
  have cw : Covers (sealWr s) q.wr := by
    rw [hW]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')
  have cr : Covers (splitRd s M ++ sealWr s) (q.rd ++ q.wr) := by
    rw [hR, hW] at cF ⊢
    rw [hp.rd] at cF ⊢
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' cF (covers_cons' (covers_of_mem (by simp))
        (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil'))))))
  exact ⟨hpre, cr, cw, a0, a1, a2, a3, a4⟩

/-- The call of `vg_aes_gcm_seal_split` on the first slice where it is and
those after it gathered in the output after it, with `src`, `src_len`,
`dst`, `len` and `tag` pushed for it: what `vg_aes_gcm_seal_gather` must
leave. -/
theorem splitCall_ok (S : SplitFn M) {st : State} (h : SCBase s st) (g : SplitRegs s st) :
    WP isa (.frame (.push [.rax, .r10, .r11, .rdi, .rsi]) (.seq (.block splitCtx) (.call S.fn.name S.fn.code))
      (.pop .rax 5)) st (Done s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hfl := fl_le hp
  have hflN : (BitVec.ofNat 64 (fl s)).toNat = fl s := toNat_ofNat_of_lt (by omega_arith)
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn8
  have hpj' : ∀ j (hj : j < 5), (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem.readW
      (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 = st.gpr ([Reg.rax, .r10, .r11, .rdi, .rsi][j]'hj) :=
    fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩] st.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hPw : (pushed [.rax, .r10, .r11, .rdi, .rsi] st).wr = ⟨SP s - BitVec.ofNat 64 40, 40⟩ :: st.wr := by
    rw [pushed_wr, hsp]; rfl
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.seq (WP.mono
    (splitCtx_ok hp h hP (pushed_rd _ _) hPw hpf') fun q ⟨q_di, q_si, q_g, q_m, q_rd, q_wr⟩ => ?_))
  obtain ⟨hpre, cr, cw, a0, a1, a2, a3, a4⟩ := splitCallEntry hp h g ⟨q_di, q_si, q_g, q_m, q_rd, q_wr⟩
  have qsp : q.gpr .rsp = SP s - BitVec.ofNat 64 40 := by
    rw [q_g _ (by decide) (by decide) (by decide), hP]
  have hE : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] q.mem q.callEntry.mem := by
    have := callEntry_frame q
    rw [qsp] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have hE' : Frame [⟨SP s - BitVec.ofNat 64 48, 8⟩] (pushed [.rax, .r10, .r11, .rdi, .rsi] st).mem
      q.callEntry.mem := by rw [← q_m]; exact hE
  have fS : Frame (wR s ++ [tR s]) st.mem q.callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE')
  have fU : Frame (wR s ++ [tR s]) s.mem q.callEntry.mem := h.frame.trans fS
  have gU : ∀ r, r ≠ .rsp → (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = q.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have gS : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q.callEntry.withRegions (splitRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r h₀ h₁ h₂ h₃ => by rw [gU r h₀, q_g r h₁ h₂ h₃, pushed_gpr _ _ h₀]
  refine WP.call_sp_mx (k := splitK M) S.ok S.sp (by have := S.xd; omega_arith) hpre cr cw
    fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  -- The first slice, and those after it in the output, which the push and the
  -- return address leave as they were.
  have eF : bytesAt q.callEntry.mem (fb s) (fl s) = pt s (k0 s) := by
    rw [pt_k0]; exact bytesAt_frame fU (fR_apart hp) (by have := fR_wrap hp; omega_arith)
  have fS2 : Frame [⟨SP s - BitVec.ofNat 64 40, 40⟩, ⟨SP s - BitVec.ofNat 64 48, 8⟩] st.mem q.callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  have eD : (bytesAt q.callEntry.mem (Dst s) (L s)).drop (fl s) =
      gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) := by
    rw [show L s = fl s + (L s - fl s) by omega_arith, Proof.Cmac.Stream.bytesAt_append,
      List.drop_left' (length_bytesAt _ _ _), ← h.out]
    refine bytesAt_frame fS2 (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.b_d.symm.sub_left (dK_sub hp)).sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact (hp.b_d.symm.sub_left (dK_sub hp)).sub_right (stk_sub (s := s) (by decide) (by decide))
  simp only [splitK, Proof.AesGcm.sealSplitX86_64M, Proof.AesGcm.arg, a0, a1, a2, a3, a4, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), q_di, q_si,
    gS _ (by decide : Reg.rdx ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.rcx ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.r8 ≠ .rsp) (by decide) (by decide) (by decide),
    gS _ (by decide : Reg.r9 ≠ .rsp) (by decide) (by decide) (by decide),
    g.rdx, g.rcx, g.r8, g.r9, hm₂, hflN, ciph_eq hp fU, hk_eq hp fU, iv_eq hp fU, ad_eq hp fU, eF, eD,
    ← (pt_split s).1] at hpost
  have hpost := hpost hfl
  have b4888 : Region.Sub (below (q.gpr .rsp) (S.fn.code.x86_64Depth + 8)) (tR s) := by
    have h₁ := below_sub (sp := q.gpr .rsp) (a := S.fn.code.x86_64Depth + 8) (b := 4848)
      (by have := S.xd; omega_arith) (by decide)
    have e : below (SP s - BitVec.ofNat 64 40) 4848 = ⟨SP s - BitVec.ofNat 64 4888, 4848⟩ := by
      simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
    rw [qsp] at h₁ ⊢
    rw [e] at h₁
    exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
  rw [q_m] at hfr
  have fC : Frame (wR s ++ [tR s]) st.mem s'.mem := by
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨dR s, by simp, fun _ h => h⟩
      · exact ⟨tgR s, by simp, fun _ h => h⟩
      · exact ⟨tR s, by simp, b4888⟩
  refine ⟨by rw [r₃, qsp, hP], by rw [hwr', q_wr], ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, qsp]
      show SP s - BitVec.ofNat 64 40 + BitVec.ofNat 64 40 = SP s
      exact BitVec.sub_add_cancel _ _
    · have n₁ : r ≠ .rdi := fun e => by subst e; simp [calleeSaved] at hr
      have n₂ : r ≠ .rsi := fun e => by subst e; simp [calleeSaved] at hr
      have n₃ : r ≠ .r11 := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, q_g r n₁ n₂ n₃,
        pushed_gpr _ _ hr', h.saved r hr]
  · rw [popped_mem]
    exact (h.frame.trans fC).readW (Region.contains_self _ _) (ret_disj hp) (by decide)
  · show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) = _
    rw [popped_mem]
    exact hpost

end

/-- `SPBase` through code that changes no memory, `rsp` or callee-saved register. -/
theorem SPBase.regs {s st st' : State} (h : SPBase s st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : SPBase s st' :=
  ⟨⟨⟨h.toBase.regs hm hcs hrd hwr, hm ▸ h.nonce, hm ▸ h.nonceLen⟩, hm ▸ h.first, hm ▸ h.firstLen⟩, hm ▸ h.out⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The path of a text whose slices after the first are short, after the
test: those slices copied to the output after the first's length, and the
text encrypted by `vg_aes_gcm_seal_split` from the first slice where it is
and the rest at the output. -/
theorem copySplit_wp (S : SplitFn M) (hL : L s - fl s < 2 ^ 63) {st : State} (h : Base s (AL s) 0 st)
    (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s) (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (copySplit S.fn) st (Done s) := by
  unfold copySplit
  refine WP.seq (WP.mono (splitHead_wp hp h h11 hsi hdx) fun s₁ ⟨F₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (splitKeep_ok hp F₁ C₁) fun s₂ ⟨P₂, r9₂, rdi₂, r11₂, _⟩ => ?_)
  refine WP.seq (WP.mono (gatherCopy_wp s₂ (splitGatherPre hp hL P₂.toBase r9₂ rdi₂ r11₂)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have B₃ := split_after hp P₂ m₃ k₃
  refine WP.seq (WP.mono (splitArgs_ok hp B₃) fun s₄ ⟨dx, cx, r8, r9, ax, r10, di, si, r11, cs, m, rd, wr⟩ => ?_)
  exact splitCall_ok hp S (B₃.regs m cs rd wr).toSC ⟨dx, cx, r8, r9, ax, r10, di, si, r11⟩

end

end VG.Proof.AesGcm.X86_64.Gather

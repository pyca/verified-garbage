import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
import VerifiedGarbage.Proof.Rsa.X86_64.KeyEntry
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract

/-!
# `vg_rsa_check_key` on x86-64: correctness

`code`, from a state its contract allows, returns `checkKey` of its inputs
as 1 or 0 (`keyCode_correct`), against `keyContract`, which states the
shared contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit)

/-! ## The contract on the registers and the stack -/

/-- The key's checks, from the arguments. -/
def keyOf (s : State) : Bool :=
  Spec.Rsa.checkKey (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)

/-- `vg_rsa_check_key(n = rdi, n_len = rsi, e = rdx, e_len = rcx, d = r8,
d_len = r9, p = [rsp + 8], p_len = [rsp + 16], q = [rsp + 24],
q_len = [rsp + 32], dp = [rsp + 40], dp_len = [rsp + 48], dq = [rsp + 56],
dq_len = [rsp + 64], qinv = [rsp + 72], qinv_len = [rsp + 80],
scratch = [rsp + 88], scratch_len = [rsp + 96])`. -/
def keyContract : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let d : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 96⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint d ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rsi).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rsi).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 11).toNat
  post s s' := (s'.gpr .rax).setWidth 32 = if keyOf s then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧ stackArg s₁ 8 = stackArg s₂ 8 ∧
      stackArg s₁ 9 = stackArg s₂ 9 ∧ stackArg s₁ 10 = stackArg s₂ 10 ∧ stackArg s₁ 11 = stackArg s₂ 11 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

/-! ## The precondition, as the code uses it -/

theorem stackArgAddr_add' (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stackArgAddr_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What `code` uses of its contract's precondition, for the working space
`B` (stack argument 10) of `Z` bytes. -/
structure KeyArgs (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 1024
  el1 : 1 ≤ (s.gpr .rcx).toNat
  el2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  dl1 : 1 ≤ (s.gpr .r9).toNat
  dl2 : (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat
  pl1 : 1 ≤ (stackArg s 1).toNat
  pl2 : (stackArg s 1).toNat < (s.gpr .rsi).toNat
  ql1 : 1 ≤ (stackArg s 3).toNat
  ql2 : (stackArg s 3).toNat < (s.gpr .rsi).toNat
  hZ : 128 * (s.gpr .rsi).toNat ≤ (stackArg s 11).toNat * 8
  hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8)
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', Outside (stackArg s 10) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  nb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rdi)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  eb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  db : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  qb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 2)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
  dpb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 4)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
  dqb : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 6)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
  qib : Src s (stackArg s 10) ((stackArg s 11).toNat * 8) (stackArg s 8)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
  hret : ∀ b < 8, (stackArg s 11).toNat * 8 ≤ ofs (stackArg s 10) (s.gpr .rsp + BitVec.ofNat 64 b)

theorem keyArgs_of {s : State} (h : keyContract.pre s) : KeyArgs s := by
  simp only [keyContract] at h
  obtain ⟨hsp, hrd, hwr, dns, des, dds, dps, dqs, ddps, ddqs, dqis, dsa,
    dRn, dRe, dRd, dRp, dRq, dRdp, dRdq, dRqi, dRs, dRa, wN, wE, wD, wP, wQ, wDp, wDq, wQi, wS, hk,
    hel1, hel2, hdl1, hdl2, hpl1, hpl2, hql1, hql2, hdpl, hqil, hdql, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hel1, hel2, hdl1, hdl2, hpl1, hpl2, hql1, hql2, by omega, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega) (by omega))
      rw [← stackArgAddr_add' s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega) (by rw [← hqil]; exact dqis),
    fun b hb => out_scr dRs (contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega))⟩

/-! ## The exits -/

/-- `fail`: 0, and the saved registers restored. -/
theorem failK_ok {t : State} {B : Addr} {Z : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = B) (hZ : 8 * 32 ≤ Z) :
    WP isa (.block fail) t fun t' => t'.gpr .rax = BitVec.ofNat 64 (false).toNat ∧
      (∀ i < 6, t'.gpr (saved.getD i .rax) = word t.mem B (8 * i)) ∧ t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold fail
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t' =>
      t'.gpr .rax = BitVec.ofNat 64 (false).toNat ∧ t'.gpr .rbx = word t.mem B (8 * 0) ∧
      t'.gpr .rbp = word t.mem B (8 * 1) ∧ t'.gpr .r12 = word t.mem B (8 * 2) ∧
      t'.gpr .r13 = word t.mem B (8 * 3) ∧ t'.gpr .r14 = word t.mem B (8 * 4) ∧
      t'.gpr .r15 = word t.mem B (8 * 5) ∧ t'.mem = t.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide)]) rfl)
    fun t' ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k⟩ => ⟨hax, ?_, hm, k.mono (by decide)⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- What `code` leaves, from the result `cb` and the saved registers. -/
theorem keyFin {s t₁ t : State} (c : KeyArgs s) (h₁ : EntryPost s (stackArg s 10) t₁) {cb : Bool}
    (hax : t.gpr .rax = BitVec.ofNat 64 cb.toNat)
    (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = word t₁.mem (stackArg s 10) (8 * i))
    (hsp : t.gpr .rsp = s.gpr .rsp) (hin : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem)
    (hcb : cb = keyOf s) : gprPreserved s t ∧ keyContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsv 0 (by decide)).trans (h₁.saved 0 (by decide))
    · exact (hsv 1 (by decide)).trans (h₁.saved 1 (by decide))
    · exact hsp
    · exact (hsv 2 (by decide)).trans (h₁.saved 2 (by decide))
    · exact (hsv 3 (by decide)).trans (h₁.saved 3 (by decide))
    · exact (hsv 4 (by decide)).trans (h₁.saved 4 (by decide))
    · exact (hsv 5 (by decide)).trans (h₁.saved 5 (by decide))
  · rw [hin _ (c.hret b hb)]
  · show (t.gpr .rax).setWidth 32 = if keyOf s then 1 else 0
    rw [hax, setWidth_flag, hcb]

/-! ## Correctness -/

theorem bytesAt_of_src {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) :
    Spec.Rsa.bytesAt s.mem p bs.length = bs :=
  List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h₁ h₂ => by
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]; exact h.val i h₂

theorem sat_of_valid {x : Nat} (h : Spec.Rsa.exponentValid x = true) : sat x = x := by
  simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  unfold sat; simp only [h.2, ↓reduceIte]

/-- `vg_rsa_check_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem keyCode_correct (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (h : keyContract.pre s) : ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  have c := keyArgs_of h
  clear h
  suffices hwp : WP isa code s fun s' => gprPreserved s s' ∧ keyContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  have hk1 := c.k1
  have hk2 := c.k2
  have hZ := c.hZ
  have := c.el2
  have hn := c.hs.nowrap
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 10) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  unfold code
  refine WP.seq (WP.mono (keyEntry_ok rfl hw c.ha c.hsep) fun t₁ h₁ => ?_)
  have hs₁ := c.hs.congr h₁.keep.2.2
  have in₁ : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t₁.mem :=
    InScr.of_outside h₁.out (by omega)
  have eb₁ := c.eb.congrK in₁ h₁.keep
  refine WP.seq (WP.mono (expCheckR_ok (s := t₁) (eb := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    h₁.r8 (by rw [h₁.r9, ofNat_toNat64]) c.el1 (by omega)
    (fun i hi => eb₁.rd i (by rw [bytesAt_length]; exact hi))
    (by have := bytesAt_of_src eb₁; rw [bytesAt_length] at this; exact this.symm))
    fun t₂ ⟨hz₂, hm₂, h11₂, k₂⟩ => ?_)
  have k12 := h₁.keep.trans k₂
  have hdi₂ : t₂.gpr .rdi = stackArg s 10 := (k₂.gpr (by decide)).trans h₁.rdi
  have hs₂ := hs₁.congr k₂.2.2
  have hsv₂ : ∀ i < 6, word t₂.mem (stackArg s 10) (8 * i) = word t₁.mem (stackArg s 10) (8 * i) := by
    intro i _; rw [hm₂]
  refine WP.ite (!Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)))
    (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) =
        false := by simpa using hb
    refine WP.mono (failK_ok hs₂ hdi₂ (by omega)) fun t ⟨hax, hsv, hm, k⟩ =>
      keyFin c h₁ hax (fun i hi => (hsv i hi).trans (hsv₂ i hi)) ((k.gpr (by decide)).trans (k12.gpr (by decide)))
        (by rw [hm, hm₂]; exact in₁) ?_
    simp only [keyOf, Spec.Rsa.checkKey, Spec.Rsa.keyValid, hv, Bool.and_false, Bool.false_and]
  · have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) =
        true := by simpa using hb
    have hlt : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) < 2 ^ 33 := by
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv; exact hv.2
    have hEv := hs₂.st (d := 8 * sEv) (by unfold sEv sFn; omega)
    have hwE : ∀ i < 32, i ≠ sEv → ∀ v, word (t₂.mem.writeW (off (stackArg s 10) (8 * sEv)) v) (stackArg s 10)
        (8 * i) = word t₁.mem (stackArg s 10) (8 * i) := fun i hi hne v => by
      rw [hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hne), hm₂]
    have hN₃ := hwE sN (by decide) (by decide) (t₂.gpr .r11)
    have hK₃ := hwE sK (by decide) (by decide) (t₂.gpr .r11)
    rw [h₁.hN] at hN₃
    rw [h₁.hK] at hK₃
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧
        t.mem = t₂.mem.writeW (off (stackArg s 10) (8 * sEv)) (t₂.gpr .r11)) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hEv, hs₂.ld (d := 8 * sN) (by unfold sN sFn; omega),
        hs₂.ld (d := 8 * sK) (by unfold sK sFn; omega), hN₃, hK₃]) rfl)
      fun t₃ ⟨⟨hdx₃, hcx₃, hm₃⟩, k₃⟩ => ?_
    have in₃ : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t₃.mem := by
      rw [hm₃, hm₂]; exact in₁.trans (InScr.of_outside (writeW_outside (d := 8 * sEv) _ _ _ (by unfold sEv sFn; omega))
        (by unfold sEv sFn; omega))
    have k13 := k12.trans k₃
    have nb₃ := c.nb.congrK in₃ k13
    refine WP.mono (invalid_ok (s := t₃) (nb := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) hdx₃
      (by rw [hcx₃, ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
      (fun i hi => nb₃.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => nb₃.val i _))
      fun t₄ ⟨hz₄, hm₄, k₄⟩ => ?_
    have k14 := k13.trans k₄
    have hs₄ := (hs₂.congr k₃.2.2).congr k₄.2.2
    have hdi₄ : t₄.gpr .rdi = stackArg s 10 := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
    have in₄ : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t₄.mem := by rw [hm₄]; exact in₃
    have hw₄ : ∀ i < 32, i ≠ sEv → word t₄.mem (stackArg s 10) (8 * i) = word t₁.mem (stackArg s 10) (8 * i) :=
      fun i hi hne => by rw [hm₄, hm₃]; exact hwE i hi hne _
    have hsv₄ : ∀ i < 6, word t₄.mem (stackArg s 10) (8 * i) = word t₁.mem (stackArg s 10) (8 * i) :=
      fun i hi => hw₄ i (by omega) (by unfold sEv sFn; omega)
    refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
      (s.gpr .rsi).toNat) (by simp [eval, hz₄]) (fun hb => ?_) (fun hb => ?_)
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
          (s.gpr .rsi).toNat = false := by simpa using hb
      refine WP.mono (failK_ok hs₄ hdi₄ (by omega)) fun t ⟨hax, hsv, hmt, k⟩ =>
        keyFin c h₁ hax (fun i hi => (hsv i hi).trans (hsv₄ i hi)) ((k.gpr (by decide)).trans (k14.gpr (by decide)))
          (by rw [hmt]; exact in₄) ?_
      simp only [keyOf, Spec.Rsa.checkKey, Spec.Rsa.keyValid, bytesAt_length, hm, Bool.false_and]
    · have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
          (s.gpr .rsi).toNat = true := by simpa using hb
      have src : ∀ {p : Addr} {bs : List Byte}, Src s (stackArg s 10) ((stackArg s 11).toNat * 8) p bs →
          Src t₄ (stackArg s 10) ((stackArg s 11).toNat * 8) p bs := fun h => h.congrK in₄ k14
      have := c.dl1
      have := c.dl2
      have := c.pl1
      have := c.pl2
      have := c.ql1
      have := c.ql2
      have hp : MainPre t₄ (stackArg s 10) ((stackArg s 11).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) (s.gpr .r8)
          (stackArg s 0) (stackArg s 2) (stackArg s 4) (stackArg s 6) (stackArg s 8)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) :=
        { scr := hs₄, rdi := hdi₄, zk := hZ, k1 := hk1, k2 := hk2, nl := bytesAt_length _ _ _,
          dl1 := by rw [bytesAt_length]; omega, dl2 := by rw [bytesAt_length]; omega,
          pl1 := by rw [bytesAt_length]; omega, pl2 := by rw [bytesAt_length]; omega,
          ql1 := by rw [bytesAt_length]; omega, ql2 := by rw [bytesAt_length]; omega,
          dpl := by rw [bytesAt_length, bytesAt_length], qil := by rw [bytesAt_length, bytesAt_length],
          dql := by rw [bytesAt_length, bytesAt_length],
          hK := by rw [hw₄ sK (by decide) (by decide), h₁.hK, ofNat_toNat64],
          hN := by rw [hw₄ sN (by decide) (by decide), h₁.hN],
          hD := by rw [hw₄ sD (by decide) (by decide), h₁.hD],
          hDl := by rw [hw₄ sDlen (by decide) (by decide), h₁.hDl, bytesAt_length, ofNat_toNat64],
          hP := by rw [hw₄ sP (by decide) (by decide), h₁.hP],
          hPl := by rw [hw₄ sPlen (by decide) (by decide), h₁.hPl, bytesAt_length, ofNat_toNat64],
          hQ := by rw [hw₄ sQ (by decide) (by decide), h₁.hQ],
          hQl := by rw [hw₄ sQlen (by decide) (by decide), h₁.hQl, bytesAt_length, ofNat_toNat64],
          hDP := by rw [hw₄ sDP (by decide) (by decide), h₁.hDP],
          hDQ := by rw [hw₄ sDQ (by decide) (by decide), h₁.hDQ],
          hQI := by rw [hw₄ sQI (by decide) (by decide), h₁.hQI],
          hEv := by
            rw [hm₄, hm₃, word_writeW_self, h11₂, sat_of_valid hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
          srN := src c.nb, srD := src c.db, srP := src c.pb, srQ := src c.qb, srDP := src c.dpb,
          srDQ := src c.dqb, srQI := src c.qib, mv := hm }
      refine WP.mono (main_ok hp hv) fun t ⟨hax, hsv, hin, _, _, kk⟩ =>
        keyFin c h₁ hax (fun i hi => (hsv i hi).trans (hsv₄ i hi)) ((kk.gpr (by decide)).trans (k14.gpr (by decide)))
          (in₄.trans hin) ?_
      simp only [keyOf, Spec.Rsa.checkKey, bytesAt_length]

end VG.Proof.Rsa.X86_64

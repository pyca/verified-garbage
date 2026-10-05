import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain

/-!
# `vg_rsa_crt_values` on x86-64: constant time but for `n`

`entry` and the modulus' check leak the same in runs that agree on the
public data (the pointers, the lengths and `n`), and so do `fail` and
`main` (`cvMain_ct`): `cvCode_ct`, and the contract's `ConstantTime`
(`cvCode_constantTime`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- A state the contract allows, with the public data `p`. -/
def CVRel (p : CvP) (s : State) : Prop := cvContract.pre s ∧ (cvIn s).pub = p

theorem cvEntry_split : entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 72 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

/-- After `entry`'s first instruction. -/
def CV1 (p : CvP) (t : State) : Prop :=
  ∃ s, CVRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))])) t (CvHeadPost s)

/-- After `entry` and the reloads. -/
def CV2 (p : CvP) (t : State) : Prop := ∃ s, CVRel p s ∧ CvHeadPost s t

/-- After the modulus' check. -/
def CV3 (p : CvP) (t : State) : Prop :=
  ∃ s t₁, CVRel p s ∧ CvHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- Between the zeros of `fail`. -/
def GF (p : CvP) (s : State) : Prop :=
  ∃ I : CvIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv ∧ s.wr = I.W ∧ CvLens I ∧
    CvOuts I

theorem pins_GF : Pins GF [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg CvP.B e₁).trans (congrArg CvP.B e₂).symm

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .rsi => ptr
  | .rcx => BitVec.ofNat 64 len
  | _ => 0

theorem zeroOut_ct {sPtr sLen : Nat} (hP : sPtr < 32) (hL : sLen < 32) (ptr : CvP → Addr) (len : CvP → Nat)
    (hA : ∀ p s, GF p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∀ i < len p, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < len p, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)) ∧ 1 ≤ len p ∧ len p < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
      .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two GF) (zeroOut sPtr sLen) (Two GF) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p => zoVal (ptr p) (len p)) pins_GF ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, -, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 (len I.pub)) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl' sPtr hP, hl' sLen hL]
        exact ⟨hp, hl⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, hwr, hsep, hl1, hl2⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [CvIn.pub] at hp hl hwr hsep hl1 hl2 ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      refine WP.mono (zeroOut_ok hs hdi h256 hP hL hp hl hl1 hl2 ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩)
        fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, Bignum.X86_64.word t.mem I.B (8 * i) = Bignum.X86_64.word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold argSlot at hi; omega), k.2.2.trans hW, L, O⟩

theorem failExit_ct : RelCT isa (Two GF) (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ Impl.Bignum.X86_64.Public.exit))
    fun _ _ => True :=
  two_taint [.rdi] pins_GF (by taint_decide)

/-- `fail` leaks the same in two runs with the same public data. -/
theorem fail_ct : RelCT isa (Two GF) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pDp CvP.pl (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pDq CvP.ql (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOut_ct (by decide) (by decide) CvP.pQi CvP.pl (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : CvP) (_ : State) => True)
      (failExit_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [CvIn.pub]
    have := L.k2
  · exact ⟨ha.dp, ha.pl, O.dp, O.sdp, L.pl1, by have := L.pl2; omega⟩
  · exact ⟨ha.dq, ha.ql, O.dq, O.sdq, L.ql1, by have := L.ql2; omega⟩
  · exact ⟨ha.qi, ha.pl, O.qi, O.sqi, L.pl1, by have := L.pl2; omega⟩

/-- `vg_rsa_crt_values` leaks the same in runs that agree on the public
data. -/
theorem cvCode_ct : RelCT isa (Two CVRel) CrtValues.code fun _ _ => True := by
  unfold CrtValues.code
  refine RelCT.seq (R := Two CV3) (RelCT.block_append (RelCT.seq (R := Two CV2) ?_ ?_)) ?_
  · rw [cvEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CV1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg CvP.sp h₁.2).trans (congrArg CvP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := cvCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 72 })] : List Instr) ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (CvHeadPost s) := by
      rw [← cvEntry_split]; exact cvHead_ok' c
    have e8 : s.gpr .rsp + BitVec.ofInt 64 72 = stackArgAddr s 8 := rfl
    have hB' : s.mem.readW (stackArgAddr s 8) 64 = stackArg s 8 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 8)
      (by xrun [State.ea, e8, c.ha 8 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg CvP.B hs.2), (k.gpr (by decide)).trans (congrArg CvP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg CvP.pN c₁.2).trans (congrArg CvP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg CvP.k c₁.2).trans (congrArg CvP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := cvCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (cvIn s).nb.length = (stackArg s 1).toNat := bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · exact fail_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := cvPre_of (cvCtx_of hs.1) h hm k
      exact ⟨cvIn s, hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact cvMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
      ⟨cvIn s, hs.2, cvPre_of (cvCtx_of hs.1) h hm k⟩) h) fun _ _ h => h

/-- `vg_rsa_crt_values` is constant time but for `n`. -/
theorem cvCode_constantTime : ConstantTime isa cvContract.pre cvContract.pub CrtValues.code := by
  refine RelCT.constantTime (cvCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(cvIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CvIn.pub, cvIn, CvP.mk.injEq]
  refine ⟨a8.symm, by rw [a9], by rw [a1], by rw [a3], by rw [a5], by rw [a7], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, hn.symm, ?_, r .rsp (by decide)⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), r .r8 (by decide),
    r .r9 (by decide), a8, a9]

end VG.Proof.Rsa.X86_64

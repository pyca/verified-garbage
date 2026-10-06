import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
import VerifiedGarbage.Proof.Rsa.X86_64.RpCode

/-!
# `vg_rsa_recover_primes` on x86-64: constant time but for `n`, `e` and the tries

`rest` (`rest_ct`), `fail` (`failR_ct`) and `main` (`rpMain_ct`): `main`'s
branch on `d e` is the public number of tries being 0. Then the entry and
the modulus' check (`rpCode_ct`), and the contract's `ConstantTime`
(`rpCode_constantTime`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Spec.Rsa (recoverPrimes)

namespace Rp

/-- After the halvings, Montgomery form, the candidates and the factors. -/
theorem rest_ct (M : Mont) : RelCT isa (Two GR0) (rest M.mm) fun _ _ => True := by
  rw [show rest M.mm = seqs ([halving] ++ (mont M.mm ++ ([candLoop M.mm] ++ fin M.mm))) by
    simp only [rest, List.append_assoc]]
  exact (ct_app (Ξ := fun (_ : RpP) (_ : State) => True) (by simp) (by simp [mont]) halving_ct (ct_app (by simp [mont]) (by simp [fin]) (mont_ct M)
    (ct_app (by simp) (by simp [fin]) (ct_one (candLoop_ct M)) ((fin_ct M).mono (fun _ _ h => h)
      fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ RpLens I ∧ RpOuts I

theorem pins_GFr : Pins GFr [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GFr p s → word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Impl.Bignum.X86_64.Public.sK) (Two GFr) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p => zoVal (ptr p) p.k) pins_GFr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 I.k) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl' sPtr hP, hl' Impl.Bignum.X86_64.Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs hdi h256 hP (by decide) hp ha.k (by omega) (by omega)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega), k.2.2.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : RpP) (_ : State) => True)
      ((two_taint [.rdi] pins_GFr (by taint_decide)).mono (fun _ _ h => h)
        fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [RpIn.pub]
  · exact ⟨ha.p, O.p, O.sp⟩
  · exact ⟨ha.q, O.q, O.sq⟩

/-! ## `main` -/

/-- The public number of tries is 0 iff `d e` fails step 1. -/
theorem cnt_zero {I : RpIn} (hv : Spec.Rsa.modulusValid I.N I.k = true) (L : RpLens I) :
    I.pub.cnt = 0 ↔ ¬(I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E) := by
  have e : I.pub.cnt = (recoverPrimes I.N I.E I.D).2 := by
    show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = _
    simp only [Spec.Rsa.primesKey, L.nbl, hv, ite_true]
    split <;> simp_all
  rw [e]
  by_cases h : I.D * I.E < 2 ∨ (I.D * I.E - 1) % 2 = 1
  · rw [VG.Proof.Rsa.recoverPrimes_none h]; omega
  · rw [VG.Proof.Rsa.recoverPrimes_go h]
    have := VG.Proof.Rsa.go_pos I.N (Spec.Rsa.splitTwos (I.D * I.E - 1)).1
      (Spec.Rsa.splitTwos (I.D * I.E - 1)).2 _ (Nat.le_refl _)
    omega

/-- After `main`'s prefix. -/
def GMP (p : RpP) (s : State) : Prop :=
  ∃ (σ : State) (I : RpIn), I.pub = p ∧ RpPre I σ ∧ Spec.Rsa.modulusValid I.N I.k = true ∧ RpS I σ.mem s ∧
    s.zf = some (decide (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)) ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E - I.D * I.E % 2 ∧
    wv s.mem I.B (slot (wk I.k) Impl.Bignum.X86_64.Public.aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) Impl.Bignum.X86_64.Public.aN)).toNat *
      (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    I.D * I.E < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem gmp_eval {p : RpP} {s : State} (h : GMP p s) : isa.eval .ne s = some (decide (p.cnt = 0)) := by
  obtain ⟨σ, I, rfl, hp, hv, -, hz, -⟩ := h
  simp only [eval, hz, Option.map_some]
  congr 1
  have := cnt_zero hv hp.L
  by_cases hc : (I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E)
  · simp_all
  · simp_all; omega

/-- `main` leaks the same in runs that agree on the public data. -/
theorem rpMain_ct (M : Mont) : RelCT isa (Two GM) (main M.mm) fun _ _ => True := by
  rw [rpMain_eq']
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two GMP) (two_post (prefix_ct.mono (fun _ _ h => h) fun _ _ _ => trivial)
    fun p s ⟨I, e, h, hv⟩ => WP.mono (rpPrefix_ok h hv) fun t ⟨S, hz, vM, vN, hi, hDE⟩ =>
      ⟨s, I, e, h, hv, S, hz, vM, vN, hi, hDE⟩) ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [gmp_eval h₁, gmp_eval h₂]) ?_ ?_
  · refine failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨σ, I, e, hp, hv, S, _⟩, _⟩ =>
      ⟨I, e, S.ws.scr, S.ws.rdi, S.args, S.wr, hp.L, hp.outs⟩) h) fun _ _ h => h
  · refine (rest_ct M).mono (fun _ _ h => two_mono (fun p t ⟨h, hf⟩ => ?_) h) fun _ _ h => h
    have hev := gmp_eval h
    obtain ⟨σ, I, rfl, hp, hv, S, hz, vM, vN, hi, hDE⟩ := h
    rw [hev] at hf
    have hb : I.D * I.E % 2 = 1 ∧ 2 ≤ I.D * I.E := by
      have := cnt_zero hv hp.L; simp only [Option.some.injEq, decide_eq_false_iff_not] at hf
      by_contra hn; exact hf (this.mpr hn)
    have L := hp.L
    have k1 := L.k1
    have k2 := L.k2
    obtain ⟨hNo, hlo⟩ := valid_lo hv
    have hlo' : 2 ^ (64 * (wk I.k - 1)) ≤ I.N := by
      refine Nat.le_trans ?_ hlo
      rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by unfold wk; omega)
    exact ⟨I, σ.mem, rfl, ⟨S, L, hNo, hlo', vN, hi, by rw [vM]; omega, by omega, by omega, by omega,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oP.wr i hi, hp.oP.sep⟩,
      ⟨fun i hi => by rw [S.wr, ← hp.wr]; exact hp.oQ.wr i hi, hp.oQ.sep⟩, hp.a⟩, hp.outs, hv⟩

end Rp

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def RPRel (p : RpP) (s : State) : Prop := rpContract.pre s ∧ (rpIn s).pub = p

theorem rpEntry_split : entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

/-- After `entry`'s first instruction. -/
def RP1 (p : RpP) (t : State) : Prop :=
  ∃ s, RPRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))])) t (RpHeadPost s)

/-- After `entry` and the reloads. -/
def RP2 (p : RpP) (t : State) : Prop := ∃ s, RPRel p s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RP3 (p : RpP) (t : State) : Prop :=
  ∃ s t₁, RPRel p s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- `vg_rsa_recover_primes` leaks the same in runs that agree on the public
data. -/
theorem rpCode_ct (M : Mont) : RelCT isa (Two RPRel) (code M.mm) fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two RP3) (RelCT.block_append (RelCT.seq (R := Two RP2) ?_ ?_)) ?_
  · rw [rpEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RP1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg RpP.sp h₁.2).trans (congrArg RpP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := rpCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
        ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (RpHeadPost s) := by
      rw [← rpEntry_split]; exact rpHead_ok' c
    have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
    have hB' : s.mem.readW (stackArgAddr s 4) 64 = stackArg s 4 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 4)
      (by xrun [State.ea, e4, c.ha 4 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg RpP.B hs.2), (k.gpr (by decide)).trans (congrArg RpP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg RpP.pN c₁.2).trans (congrArg RpP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg RpP.k c₁.2).trans (congrArg RpP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of hs.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := rpPre_of (rpCtx_of hs.1) h hm k
      exact ⟨rpIn s, hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr, hpre.L, hpre.outs⟩) h) fun _ _ h => h
  · exact (Rp.rpMain_ct M).mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => by
      refine ⟨rpIn s, hs.2, rpPre_of (rpCtx_of hs.1) h hm k, ?_⟩
      have hz : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k = true := by
        simp only [eval, z, Option.map_some, Option.some.injEq] at hf; simpa using hf
      have e : (rpIn s).pub = p := hs.2
      subst e
      exact hz) h) fun _ _ h => h

/-- `vg_rsa_recover_primes` is constant time but for `n`, `e` and the number
of tries. -/
theorem rpCode_constantTime (M : Mont) : ConstantTime isa rpContract.pre rpContract.pub (code M.mm) := by
  refine RelCT.constantTime ((rpCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(rpIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, hn, he, hc⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [RpIn.pub, rpIn, RpP.mk.injEq]
  refine ⟨a4.symm, by rw [a5], by rw [r .r9 (by decide)], by rw [a1], by rw [a3], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, hn.symm, he.symm, ?_, r .rsp (by decide), hc.symm⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), a4, a5]

end VG.Proof.Rsa.X86_64

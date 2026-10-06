import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Code

/-!
# A candidate on x86-64: constant time

`code` leaks the same in runs that agree on the arguments, `e` and
`candidateLeak` (`code_constantTime`): the entry, the zeros to `out` and the
length check depend on the arguments alone, and `kMain` on the schedule the
leak fixes (`schedOf_eq`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (Sched schedOf shapeOf)

/-- The public data of `vg_rsa_keygen_candidate`: the stages' and the stack
pointer. -/
structure CPub where
  f : FPub
  rsp : Addr

/-- A state the contract allows, with the public data `p`. -/
structure CRel (p : CPub) (s : State) : Prop where
  pre : candPre s
  rsp : s.gpr .rsp = p.rsp
  B : arg s 3 = p.f.B
  Z : (arg s 4).toNat * 8 = p.f.Z
  w : (s.gpr .rsi).toNat = 8 * p.f.w
  op : s.gpr .rdi = p.f.op
  up : s.gpr .rdx = p.f.up
  eP : s.gpr .rcx = p.f.eP
  eB : Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat = p.f.eB
  pP : s.gpr .r9 = p.f.pP
  pl : (arg s 0).toNat = p.f.pl
  rP : arg s 1 = p.f.rP
  rl : (arg s 2).toNat = p.f.rl
  wr : s.wr = p.f.wr
  sch : 8 * p.f.w ≤ p.f.rl → schedOf (8 * p.f.w) (Spec.Rsa.os2ip p.f.eB)
    (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
    (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) = p.f.sch

theorem candPre_wr {s : State} (h : candPre s) :
    s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨arg s 3, (arg s 4).toNat * 8⟩] := h.2.2.1

/-- The writable regions the precondition gives. -/
theorem kw_of {s : State} (h : candPre s) : KW (arg s 3) s.wr := by
  have c := kctx_of h
  have hZ := c.hZ
  have hk1 := c.k1
  simp only [candPre] at h
  obtain ⟨-, -, hwr, dOu, -, -, -, dOs, -, -, -, -, dUs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, wS, -⟩ := h
  refine ⟨_, _, _, hwr, Nat.le_refl _, by omega, ?_, ?_⟩
  · rw [hwr]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl); exacts [dOu, dOs]
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ rfl; exact dUs
  · rw [hwr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact Nat.le_of_lt (s.gpr .rsi).isLt
    · dsimp only; decide
    · dsimp only; omega

/-- After `kEntry`'s first instruction. -/
def C1 (p : CPub) (t : State) : Prop :=
  ∃ s, CRel p s ∧ t.gpr .r11 = p.f.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block (kEntry.drop 1)) t (EntryPost s · (arg s 3))

/-- After `kEntry`. -/
def C2 (p : CPub) (t : State) : Prop := ∃ s, CRel p s ∧ EntryPost s t (arg s 3)

/-- After the zeros to `out` and the length check. -/
def C3 (p : CPub) (t : State) : Prop := ∃ s t₁, CRel p s ∧ EntryPost s t₁ (arg s 3) ∧ Front s t₁ t

theorem C3.cf {p : CPub} {t : State} (h : C3 p t) : t.cf = some (decide (p.f.rl < 8 * p.f.w)) := by
  obtain ⟨s, t₁, hs, -, hf⟩ := h
  rw [hf.cf, hs.rl, hs.w]

theorem WP.and' {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

theorem kEntry_split : kEntry = ([.mov .r11 (.mem { base := .rsp, disp := 32 })] : List Instr) ++ kEntry.drop 1 := rfl

/-- What `kMain` needs, from a state past the length check with enough
octets. -/
theorem C3.k0 {p : CPub} {t : State} (h : C3 p t) (hlt : ¬ p.f.rl < 8 * p.f.w) : K0 p.f t := by
  obtain ⟨s, t₁, hs, he, hf⟩ := h
  have c := kctx_of hs.pre
  have hk1 := c.k1
  have hk2 := c.k2
  have hle : (s.gpr .rsi).toNat ≤ (arg s 2).toNat := by rw [hs.w, hs.rl]; omega
  have hm := mainCtx_of c he hf hs.w hle
  have hw := hs.w
  have hsch := hs.sch (by omega)
  rw [hs.eB, hs.B, hs.Z, hs.op, hs.up, hs.eP, hs.pP, hs.rP] at hm
  rw [hs.pP, hs.rP] at hsch
  refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, (hf.keep.2.2.trans he.keep.2.2).trans hs.wr,
    ⟨by have := hm.z; rwa [show 8 * p.f.w / 8 = p.f.w by omega] at this, by omega, by omega,
      by rw [← hs.rl]; exact (arg s 2).isLt, by omega, ?_, ?_, ?_⟩, _, _, hm, by rw [bytesAt_length, hs.pl],
    by rw [bytesAt_length, hs.rl], hsch⟩
  · rw [← hs.eB, bytesAt_length]; exact c.el1
  · rw [← hs.eB, bytesAt_length]; exact c.el8
  · rw [← hs.pl, ← hs.w]; exact c.pl

/-- `vg_rsa_keygen_candidate` leaks the same in runs that agree on the public
data. -/
theorem code_ct (M : Mont) : RelCT isa (Two CRel) (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.X86_64.Candidate.code
  simp only [seqs]
  refine RelCT.seq (R := Two C2) ?_ (RelCT.assoc (RelCT.seq (R := Two C3) ?_ ?_))
  · -- The entry: the scratch space's base from the stack, then the header.
    rw [kEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := kctx_of hs.pre
    have hn := c.hs.nowrap
    have hZ := c.hZ
    have hk1 := c.k1
    have hhw : ∀ i < 32, InRegions s.wr (off (arg s 3) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 32 })] ++ kEntry.drop 1)) s
        (EntryPost s · (arg s 3)) := by
      rw [← kEntry_split]; exact kEntry_ok rfl hhw c.ha c.hsep
    have e3 : s.gpr .rsp + BitVec.ofInt 64 32 = stackArgAddr s 3 := rfl
    have hB' : s.mem.readW (stackArgAddr s 3) 64 = stackArg s 3 := rfl
    refine WP.mono (WP.and' (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 3)
      (by xrun [State.ea, e3, c.ha 3 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.B, (k.gpr (by decide)).trans hs.rsp, hw⟩
  · -- The zeros to `out` and the length check.
    refine kt_piece (fun p : CPub => p.f.B) (fun p => p.f.wr) [kOut, kLen, kRandLen]
      (fun p => [(kOut, p.f.op), (kLen, BitVec.ofNat 64 (8 * p.f.w)), (kRandLen, BitVec.ofNat 64 p.f.rl)]) []
      (by decide) (fun _ => rfl) ?_ (pins_nil _) (by taint_decide) ?_
    · rintro p t ⟨s, hs, he⟩
      refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [he.rdi, hs.B], by rw [he.keep.2.2, hs.wr],
        fun e he' => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl | rfl
      · rw [← hs.B, he.out, hs.op]
      · rw [← hs.B, he.len, ← hs.w, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [← hs.B, he.rlen, ← hs.rl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rintro p t ⟨s, hs, he⟩
      exact WP.mono (front_ok (kctx_of hs.pre) he) fun t' hf => ⟨s, t, hs, he, hf⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.cf, h₂.cf]) ?_ ?_
  · -- Too few octets.
    refine kt_ct (fun p : CPub => p.f.B) (fun p => p.f.wr) [kUsedP] (fun p => [(kUsedP, p.f.up)]) [] (by decide)
      (fun _ => rfl) ?_ (pins_nil _) (by taint_decide)
    rintro p t ⟨⟨s, t₁, hs, he, hf⟩, -⟩
    have c := kctx_of hs.pre
    refine ⟨by rw [← hs.B, ← hs.wr]; exact kw_of hs.pre, by rw [hf.keep.gpr (by decide), he.rdi, hs.B],
      by rw [hf.keep.2.2, he.keep.2.2, hs.wr], fun e he' => ?_⟩
    simp only [List.mem_singleton] at he'
    subst he'
    show word t.mem p.f.B (8 * kUsedP) = p.f.up
    rw [← hs.B, hf.word c (i := kUsedP) (by decide), he.usedP, hs.up]
  · exact (kMain_ct M).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.f, h₁.1.k0 (by have := h₁.2; simpa [eval, h₁.1.cf] using this),
        h₂.1.k0 (by have := h₂.2; simpa [eval, h₂.1.cf] using this)⟩) h) fun _ _ h => h

/-- The public data of a state. -/
def cpubOf (s : State) : CPub :=
  ⟨⟨arg s 3, (arg s 4).toNat * 8, (s.gpr .rsi).toNat / 8, s.wr, s.gpr .rdi, s.gpr .rdx, s.gpr .rcx,
    Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat, s.gpr .r9, (arg s 0).toNat, arg s 1, (arg s 2).toNat,
    schedOf (8 * ((s.gpr .rsi).toNat / 8)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
      (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat)⟩, s.gpr .rsp⟩

theorem crel_self {s : State} (h : candPre s) : CRel (cpubOf s) s := by
  have := (kctx_of h).k8
  exact ⟨h, rfl, rfl, rfl, by dsimp only [cpubOf]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Runs that agree on the arguments and the leak agree on the public data. -/
theorem crel_of {s₁ s₂ : State} (h₁ : candPre s₁) (h₂ : candPre s₂) (hp : candPub s₁ s₂) : CRel (cpubOf s₁) s₂ := by
  obtain ⟨hdi, hsi, hdx, hcx, hr8, hr9, hsp, ha, hl⟩ := hp
  have c := kctx_of h₁
  have hk8 := c.k8
  have hk1 := c.k1
  unfold candLeak at hl
  obtain ⟨he, hl'⟩ := List.append_inj hl (by simp only [List.length_map, bytesAt_length, hr8])
  have heB := VG.Proof.RsaKeyGen.map_toNat_inj he
  refine ⟨h₂, hsp.symm, (ha 3 (by decide)).symm, by rw [← ha 4 (by decide)]; rfl, by dsimp only [cpubOf]; rw [← hsi]; omega,
    hdi.symm, hdx.symm, hcx.symm, heB.symm, hr9.symm, by rw [← ha 0 (by decide)]; rfl, (ha 1 (by decide)).symm,
    by rw [← ha 2 (by decide)]; rfl, ?_, fun hk => ?_⟩
  · rw [candPre_wr h₂, ← hdi, ← hsi, ← hdx, ← ha 3 (by decide), ← ha 4 (by decide), ← candPre_wr h₁]; rfl
  · dsimp only [cpubOf] at hk ⊢
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl'
    unfold Spec.RsaKeyGen.candidateOp at hl'
    rw [← heB, ← hsi] at hl'
    rw [show 8 * ((s₁.gpr .rsi).toNat / 8) = (s₁.gpr .rsi).toNat by omega] at hk ⊢
    refine (VG.Proof.RsaKeyGen.schedOf_eq (by omega) (by rw [bytesAt_length, bytesAt_length, ha 2 (by decide)])
      (by rw [bytesAt_length]; omega) hl').symm

/-- `vg_rsa_keygen_candidate` is constant time but for the arguments, `e` and
`candidateLeak`. -/
theorem code_constantTime (M : Mont) :
    ConstantTime isa candPre candPub (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm) :=
  RelCT.constantTime ((code_ct M).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ => ⟨cpubOf s₁, crel_self h₁, crel_of h₁ h₂ hp⟩)
    fun _ _ h => h)

end VG.Proof.RsaKeyGen.X86_64

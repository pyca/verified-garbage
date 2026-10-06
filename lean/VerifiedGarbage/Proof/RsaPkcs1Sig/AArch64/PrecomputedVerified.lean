import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyVerified
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_verify_precomputed` on AArch64: `Verified`

Correctness (`code_ok`), constant time (`code_ct`: as `vg_rsa_pkcs1_verify`'s,
with the precomputed operation's call, and the padding check and the mask
checked by the taint analysis at once, since no branch reads the status)
and a state meeting the precondition.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Pc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Precomputed VG.Proof.RsaPkcs1Sig.AArch64.Ver
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 restore lenCheck ret0)
open VG.Impl.RsaPkcs1Sig.AArch64 (encode)
open VG.Proof.MlKem.AArch64 (Only wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_ite two_alloc)

/-! ## Correctness -/

/-- The result, if `pre` holds the modulus' values, and the calling
convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧
    (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) =
        some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat) →
      (s'.gpr .x0).setWidth 32 = if verOut s then 1 else 0)

theorem code_ok (c : PdChecked) {s : State} (hp : PreP c.stack s) :
    WP isa (code c.name c.code) s (Post s) := by
  have hv := hp.v
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hv) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .x1
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; have := hv.sp1; unfold stk at this; omega) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_okP hp (by simp [allocated, o₁.sp]) (by simp [allocated, o₁.rd])
      (by simp [allocated, o₁.sp, o₁.wr]) (by simp [allocated, o₁.mem]) (fun r hr => by
        simp only [allocated]; exact o₁.gpr r (by simpa using hr)) (fun r hr => o₁.vcs r hr))
      fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (callP_ok c hp h₂ hsig) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (afterPubP_ok hp hsig h₃) fun t₄ ⟨m₄, r₄⟩ => ?_)
    exact WP.mono (restore_ok m₄) fun w ⟨habi, hx0⟩ => ⟨habi, fun hc => by rw [hx0]; exact r₄ hc⟩
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (ret0_ok t₁) fun w ⟨o, e⟩ =>
      ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, fun _ => ?_⟩) (by simp)
    · have h8 : r ∉ [Reg.x8] ++ [Reg.x0] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      exact (o₁.trans o).gpr r h8
    · rw [o.sp, o₁.sp]
    · rw [o.vcs r hr, o₁.vcs r hr]
    · rw [e, verOut_len hsig]; rfl

theorem code_correct (c : PdChecked) (s : State)
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk c.stack)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c (preP_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  exact hr

/-! ## Constant time -/

theorem pubArgs_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem afterPub_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.x19, .x20, .x21, .x22]) :
    RelCT isa (Two Φ) afterPub fun _ _ => True :=
  two_taint [.x19, .x20, .x21, .x22] h (by taint_decide)

/-- The public data: `vg_rsa_pkcs1_verify`'s, and the precomputed values. -/
structure PubP (a s : State) : Prop where
  v : PubV a s
  a3 : stackArg s 3 = stackArg a 3
  a4 : stackArg s 4 = stackArg a 4
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem PubP.refl (s : State) : PubP s s := ⟨PubV.refl s, rfl, rfl, rfl⟩

theorem leak_eqW {a b c d a' b' c' d' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length) (hc : c.length = c'.length) (hd : d.length = d'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) ++ w.map (·.toNat) =
      (a' ++ b' ++ c' ++ d').map (·.toNat) ++ w'.map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb, hc, hd])
  obtain ⟨e₁, e₂, e₃, e₄⟩ := leak_eq4 ha hb hc h₁
  exact ⟨e₁, e₂, e₃, e₄, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubP_of {S : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi S).pub s₁ s₂) : PubP s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨hn, he, hd, hg, hw⟩ := leak_eqW (by simp [bytesAt_length, h1]) (by simp [bytesAt_length, h3])
    (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, a0]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, h4.symm, fun i hi => ?_, hn.symm, he.symm, hd.symm, hg.symm⟩,
    a3.symm, a4.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm]

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PreP K s ∧ PubP a s

theorem call_ct (c : PdChecked) :
    RelCT isa (Two fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧ AtCallP s t)
      (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pdOk_of c h₁.1 c₁ g₁,
    pdOk_of c h₂.1 c₂ g₂, ?_⟩
  obtain ⟨⟨u₁, b₁, o₁⟩, x2₁, x3₁⟩ := c₁
  obtain ⟨⟨u₂, b₂, o₂⟩, x2₂, x3₂⟩ := c₂
  have e := fun r hr => (h₁.2.v.g r hr).trans (h₂.2.v.g r hr).symm
  have g : ∀ {t u : State}, Only [.x2, .x3] u t → ∀ r ∈ [Reg.x0, .x1, .x4, .x5, .x6, .x7],
      t.gpr r = u.gpr r := fun o r hr =>
    o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have sa : ∀ {t u : State} {s : State}, Only [.x2, .x3] u t → AtCall s u → ∀ i < 2,
      stackArg t i = stackArg s (i + 1) := fun o b i hi => by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [← b.a0]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
    · rw [← b.a1]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  refine ⟨⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [o₁.sp, o₂.sp, b₁.sp, b₂.sp]; simp only [fb, h₁.2.v.sp, h₂.2.v.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g o₁ .x0 (by simp), g o₂ .x0 (by simp), b₁.x0, b₂.x0]; simp only [fb, h₁.2.v.sp, h₂.2.v.sp]
    · rw [g o₁ .x1 (by simp), g o₂ .x1 (by simp), b₁.x1, b₂.x1, e .x1 (by decide)]
    · rw [x2₁, x2₂, h₁.2.a3, h₂.2.a3]
    · rw [x3₁, x3₂, h₁.2.a4, h₂.2.a4]
    · rw [g o₁ .x4 (by simp), g o₂ .x4 (by simp), b₁.x4, b₂.x4, e .x2 (by decide)]
    · rw [g o₁ .x5 (by simp), g o₂ .x5 (by simp), b₁.x5, b₂.x5, e .x3 (by decide)]
    · rw [g o₁ .x6 (by simp), g o₂ .x6 (by simp), b₁.x6, b₂.x6, e .x7 (by decide)]
    · rw [g o₁ .x7 (by simp), g o₂ .x7 (by simp), b₁.x7, b₂.x7, e .x1 (by decide)]
  · rw [sa o₁ b₁ i hi, sa o₂ b₂ i hi, h₁.2.v.args (i + 1) (by omega), h₂.2.v.args (i + 1) (by omega)]
  · have fr : ∀ {s t u : State}, PreP c.stack s → AtCall s u → Only [.x2, .x3] u t →
        Frame [kR c.stack s, sR s] s.mem t.mem := fun hp b o => by
      rw [o.mem]
      exact b.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩
    rw [x2₁, x2₂, x3₁, x3₂, words_of_frame (fr h₁.1 b₁ o₁) h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame (fr h₂.1 b₂ o₂) h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · have b : ∀ {s t u : State}, PreP c.stack s → AtCall s u → Only [.x2, .x3] u t →
        Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat := fun hp b o => by
      rw [g o .x4 (by simp), g o .x5 (by simp), b.x4, b.x5, o.mem]
      exact bytes_of_frame (b.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩) hp.v.ke
        hp.v.es.symm (by have := hp.v.we; omega)
    rw [b h₁.1 b₁ o₁, b h₂.1 b₂ o₂, h₁.2.v.be, h₂.2.v.be]

theorem code_ct (c : PdChecked) :
    RelCT isa (Two (E c.stack)) (code c.name c.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Only [.x8] s t ∧
      t.gpr .x8 = stackArg s 0 - s.gpr .x1)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.v.sp, h₂.2.v.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1.v) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, h₁.2.v.args 0 (by decide), h₂.2.v.args 0 (by decide),
        h₁.2.v.g .x1 (by decide), h₂.2.v.g .x1 (by decide)])
    (ret0_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.v.sp, h₂.2.v.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧ AtCallP s t)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; simp only [allocated, o₁.sp, o₂.sp, h₁.2.v.sp, h₂.2.v.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .x1 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_okP h.1 (by simp [allocated, o.sp]) (by simp [allocated, o.rd])
      (by simp [allocated, o.sp, o.wr]) (by simp [allocated, o.mem])
      (fun r hr => by simp only [allocated]; exact o.gpr r (by simpa using hr)) (fun r hr => o.vcs r hr))
      fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧
      AfterCallP c.stack s t) (call_ct c) fun a t ⟨s, h, g, ht⟩ =>
    WP.mono (callP_ok c h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Mid c.stack s t)
    (afterPub_taint fun _ _ _ ⟨s₁, h₁, _, a₁⟩ ⟨s₂, h₂, _, a₂⟩ => ⟨?_, fun r hr => ?_⟩)
    fun a t ⟨s, h, g, ht⟩ => WP.mono (afterPubP_ok h.1 g ht) fun w hw => ⟨s, h, hw.1⟩) ?_
  · rw [a₁.sp, a₂.sp]; simp only [fb, h₁.2.v.sp, h₂.2.v.sp]
  · have e := fun r hr => (h₁.2.v.g r hr).trans (h₂.2.v.g r hr).symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.x19, a₂.x19, e .x1 (by decide)]
    · rw [a₁.x20, a₂.x20, h₁.2.v.h4, h₂.2.v.h4]
    · rw [a₁.x21, a₂.x21, e .x5 (by decide)]
    · rw [a₁.x22, a₂.x22, e .x6 (by decide)]
  exact restore_taint fun _ _ _ ⟨s₁, h₁, m₁⟩ ⟨s₂, h₂, m₂⟩ =>
    ⟨by rw [m₁.sp, m₂.sp]; simp only [fb, h₁.2.v.sp, h₂.2.v.sp], fun _ h => absurd h List.not_mem_nil⟩

theorem code_constantTime (c : PdChecked) :
    ConstantTime isa (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk c.stack)).pre
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk c.stack)).pub (code c.name c.code) :=
  RelCT.constantTime ((code_ct c).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preP_of h₁, PubP.refl s₁⟩, preP_of h₂, pubP_of hp⟩) fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- `vg_rsa_pkcs1_verify`'s (`Ver.satState`), with 16 precomputed words. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 1 | .x5 => 0x3000 | .x6 => 1 | .x7 => 0x4000
    | _ => 0
  sp := 0x10000000000
  mem a := if a = 0x10000000000 then 1 else if a = 0x1000000000A then 1
    else if a = 0x10000000011 then 4 else if a = 0x10000000019 then 0x50
    else if a = 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x10000, 8192⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 1024 ∧
    stackArg satState 3 = 0x5000 ∧ stackArg satState 4 = 16 := by
  decide

theorem sat (K : Nat) (hK : K ≤ 2 ^ 20) :
    ∃ s, (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk K)).pre s := by
  refine ⟨satState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4⟩ := sat_args
  have hS : frameBytes + K - 1 + 1 = 2128 + K := by unfold frameBytes; omega
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (2128 + K)).toNat = 2 ^ 40 - (2128 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (2128 + K), 2128 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; omega)
  refine ⟨by rw [hsp]; omega, by decide, by decide, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), kd _ _ (by decide),
    kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide),
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; rw [hsp]; omega),
    by decide, by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide,
    by decide, by decide, by decide⟩

theorem code_verified (c : PdChecked) :
    Verified AArch64.target (code c.name c.code) (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi (stk c.stack)) :=
  ⟨code_correct c, code_constantTime c, sat c.stack c.le⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Pc

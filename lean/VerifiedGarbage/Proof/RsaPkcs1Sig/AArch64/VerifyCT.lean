import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two

/-!
# `vg_rsa_pkcs1_verify` on AArch64: constant time
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.MlKem.AArch64 (Only)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ret0_taint (h : Pins Φ []) : RelCT isa (Two Φ) ret0 fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem pubArgs_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encTail_taint (h : Pins Φ [.x19, .x20, .x21, .x22]) :
    RelCT isa (Two Φ) (.seq (.block encArgs) (.seq encode tail)) fun _ _ => True :=
  two_taint [.x19, .x20, .x21, .x22] h (by taint_decide)

end

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, `hash`, and the bytes of `n`, `e`, the hash value and
the signature. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x5, .x6, .x7], s.gpr r = a.gpr r
  h4 : (s.gpr .x4).setWidth 32 = (a.gpr .x4).setWidth 32
  args : ∀ i < 3, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x0) (a.gpr .x1).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  bd : Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x5) (a.gpr .x6).toNat
  bg : Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .x7) (stackArg a 0).toNat

theorem PubV.refl (s : State) : PubV s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem leak_eq4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) = (a' ++ b' ++ c' ++ d').map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₂, rfl⟩ := List.append_inj h₁ (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₂ ha
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pubV_of {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.verifyContract abi S).pub s₁ s₂) :
    PubV s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, stackArgs_three,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2⟩ := h
  obtain ⟨hn, he, hd, hg⟩ := leak_eq4 (by simp [bytesAt_length, h1]) (by simp [bytesAt_length, h3])
    (by simp [bytesAt_length, h6]) hl
  refine ⟨hsp.symm, fun r hr => ?_, h4.symm, fun i hi => ?_, hn.symm, he.symm, hd.symm, hg.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm]

/-! ## The points of the code -/

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PreV K s ∧ PubV a s

theorem pubOut_eq {K : Nat} {a s : State} (h : E K a s) (hsig : stackArg s 0 = s.gpr .x1) :
    pubOut s = pubOut a := by
  have g0 := h.2.g .x0 (by decide); have g1 := h.2.g .x1 (by decide)
  have g2 := h.2.g .x2 (by decide); have g3 := h.2.g .x3 (by decide); have g7 := h.2.g .x7 (by decide)
  have hsa : stackArg a 0 = a.gpr .x1 := by rw [← h.2.args 0 (by decide), hsig, g1]
  have hg := h.2.bg
  rw [hsig, hsa] at hg
  unfold pubOut
  rw [h.2.bn, h.2.be, hg]

/-- Two calls of `vg_rsa_public_checked` from `AtCall` agree on what the
callee may leak. -/
theorem call_ct (c : PubChecked) :
    RelCT isa (Two fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧ AtCall s t)
      (.call c.name c.code) fun _ _ => True := by
  refine pubCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pubOk_of c h₁.1 c₁ g₁,
    pubOk_of c h₂.1 c₂ g₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp]; simp only [fb, h₁.2.sp, h₂.2.sp]
  · have e := fun r hr => (h₁.2.g r hr).trans (h₂.2.g r hr).symm
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0]; simp only [fb, h₁.2.sp, h₂.2.sp]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x0 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x1 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x2 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x3 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x7 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x1 (by decide)]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.2.args 1 (by decide), h₂.2.args 1 (by decide)]
    · rw [c₁.a1, c₂.a1, h₁.2.args 2 (by decide), h₂.2.args 2 (by decide)]
  · have b : ∀ {s t : State}, PreV c.stack s → AtCall s t →
        Spec.Rsa.bytesAt t.mem (t.gpr .x2) (t.gpr .x3).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := fun hp ht => by
      rw [ht.x2, ht.x3]
      exact bytes_of_frame (ht.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩) hp.kn
        hp.ns.symm (by have := hp.wn; omega)
    rw [b h₁.1 c₁, b h₂.1 c₂, h₁.2.bn, h₂.2.bn]
  · have b : ∀ {s t : State}, PreV c.stack s → AtCall s t →
        Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat := fun hp ht => by
      rw [ht.x4, ht.x5]
      exact bytes_of_frame (ht.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩) hp.ke
        hp.es.symm (by have := hp.we; omega)
    rw [b h₁.1 c₁, b h₂.1 c₂, h₁.2.be, h₂.2.be]

/-- After the call: the condition of its result's branch and the registers
the padding check reads are the anchor's. -/
theorem afterPub_ct {K : Nat} :
    RelCT isa (Two fun a t => ∃ s, E K a s ∧ stackArg s 0 = s.gpr .x1 ∧ AfterCall K s t) afterPub
      fun _ _ => True := by
  unfold afterPub
  have res : ∀ {a s t}, E K a s → stackArg s 0 = s.gpr .x1 → AfterCall K s t →
      isa.eval (.zero .w .x0) t = some (pubOut a).isNone := fun {a s t} h g ht => by
    have hr := ht.res
    rw [pubOut_eq h g] at hr
    simp only [eval, State.read]
    cases hpo : pubOut a with
    | none => rw [hpo] at hr; rw [hr.1]; rfl
    | some y => rw [hpo] at hr; rw [hr.1]; rfl
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, g₁, a₁⟩ ⟨s₂, h₂, g₂, a₂⟩ => by rw [res h₁ g₁ a₁, res h₂ g₂ a₂])
    (ret0_taint fun _ _ _ ⟨⟨s₁, h₁, _, a₁⟩, _⟩ ⟨⟨s₂, h₂, _, a₂⟩, _⟩ => ⟨?_, fun _ h => absurd h List.not_mem_nil⟩)
    (encTail_taint fun _ _ _ ⟨⟨s₁, h₁, _, a₁⟩, _⟩ ⟨⟨s₂, h₂, _, a₂⟩, _⟩ => ⟨?_, fun r hr => ?_⟩)
  · rw [a₁.sp, a₂.sp]; simp only [fb, h₁.2.sp, h₂.2.sp]
  · rw [a₁.sp, a₂.sp]; simp only [fb, h₁.2.sp, h₂.2.sp]
  · have e := fun r hr => (h₁.2.g r hr).trans (h₂.2.g r hr).symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a₁.x19, a₂.x19, e .x1 (by decide)]
    · rw [a₁.x20, a₂.x20, h₁.2.h4, h₂.2.h4]
    · rw [a₁.x21, a₂.x21, e .x5 (by decide)]
    · rw [a₁.x22, a₂.x22, e .x6 (by decide)]

theorem code_ct (c : PubChecked) :
    RelCT isa (Two (E c.stack)) (code c.name c.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Only [.x8] s t ∧
      t.gpr .x8 = stackArg s 0 - s.gpr .x1)
    (lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (lenCheck_ok h.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [eval_len e₁, eval_len e₂, h₁.2.args 0 (by decide), h₂.2.args 0 (by decide),
        h₁.2.g .x1 (by decide), h₂.2.g .x1 (by decide)])
    (ret0_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧ AtCall s t)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; simp only [allocated, o₁.sp, o₂.sp, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .x1 := by
      rw [eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_ok h.1 (by simp [allocated, o.sp]) (by simp [allocated, o.rd])
      (by simp [allocated, o.sp, o.wr]) (by simp [allocated, o.mem])
      (fun r hr => by simp only [allocated]; exact o.gpr r (by simpa using hr)) (fun r hr => o.vcs r hr))
      fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ stackArg s 0 = s.gpr .x1 ∧
      AfterCall c.stack s t) (call_ct c) fun a t ⟨s, h, g, ht⟩ =>
    WP.mono (call_ok c h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Mid c.stack s t) afterPub_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (afterPub_ok h.1 g ht) fun w hw => ⟨s, h, hw.1⟩) ?_
  exact restore_taint fun _ _ _ ⟨s₁, h₁, m₁⟩ ⟨s₂, h₂, m₂⟩ =>
    ⟨by rw [m₁.sp, m₂.sp]; simp only [fb, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Ver

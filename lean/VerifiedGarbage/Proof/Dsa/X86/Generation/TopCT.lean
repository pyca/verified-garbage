module

import VerifiedGarbage.Proof.Dsa.X86.Generation.FinishCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Entry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base

/-! # Parameter generation's trace depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86.Compact (entered savedRegisters)

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (fun x => x.toNat) = l₂.map (fun x => x.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem pub_env {s₁ s₂ : State} (h : genContract.pub s₁ s₂) :
    callEnv s₁ = callEnv s₂ ∧ s₁.gpr .esp = s₂.gpr .esp := by
  sig_pub [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at h
  obtain ⟨esp, sy, leak, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  rw [a3, a4, a7] at leak
  obtain ⟨lw, lb⟩ := List.append_inj leak (by simp [Spec.Rsa.wordsAt])
  have eW := map_toNat_inj64 lw
  change [s₁.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0) 64,
      s₁.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + 8) 64, _, _] =
    [s₂.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0) 64,
      s₂.mem.readW (BitVec.setWidth 64 (arg s₂ 7) + 8) 64, _, _] at eW
  simp only [List.cons.injEq] at eW
  obtain ⟨w0, w1, -, -, -⟩ := eW
  have e0 : BitVec.setWidth 64 (arg s₂ 7) + BitVec.ofNat 64 0 = BitVec.setWidth 64 (arg s₂ 7) := by simp
  rw [e0] at w0
  refine ⟨?_, esp⟩
  simp only [callEnv, pLenOf, a0, a2, a3, a4, a5, a6, a7, esp, sy, w0, w1, map_toNat_inj lb]

/-- At the entry: the frame of saved registers pushed, from a state the
contract holds in. -/
def TIn (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ t = entered s

/-- After the entry. -/
def TEnt (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ EPost s t

theorem entry_ct : RelCT isa (Both TIn) (.block entry) fun _ _ => True := by
  rw [show entry = [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 5))] ++ entry.tail from rfl]
  refine RelCT.block_append (RelCT.seq (both_post (Ψ := fun E t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h r hr => ?_) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) (both_agree [.esp, .edi] (fun E => baseVal E) (fun _ _ h => h) (tcheck _ _ (by decide +kernel))))
  · obtain ⟨s, rfl, F, rfl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (entered_inv F).esp
  · obtain ⟨s, rfl, F, rfl⟩ := h
    have I₀ := entered_inv F
    refine wp_ldm (B := (callEnv s).sp) I₀.esp (by rw [addrArg]; exact argAccess F I₀ (by decide))
      fun t₀ u₀ => WP.block_nil fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [u₀.other _ (by decide)]; exact I₀.esp
    · rw [u₀.gpr, addrArg, argValue F I₀ (by decide)]
      exact (narrow _).symm

/-- After the pointer to `state`. -/
def TPtr (E : Env) (t : State) : Prop := ∃ s t₀, callEnv s = E ∧ CallFacts s ∧ EPost s t₀ ∧ DPtr s t₀ t

/-- After `state`'s reads, then the comparison of its width with `c`. -/
def TCmp (c : Nat) (E : Env) (t : State) : Prop :=
  ∃ s, callEnv s = E ∧ CallFacts s ∧ SIn E t ∧ t.gpr .eax = BitVec.ofNat 32 E.pLen ∧
    isa.eval .e t = some (decide (E.pLen = c))

theorem TCmp.pins {c : Nat} {E : Env} {t : State} (h : TCmp c E t) : ∀ r ∈ [Reg.esp], t.gpr r = baseVal E r := by
  obtain ⟨s, rfl, F, ⟨B, _⟩, _⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact B.sp

/-- One geometry, chosen by `state[1]`. -/
theorem run_ct {g : Geo} (G : GeoOk g) {c : Nat} {Φ : Env → State → Prop} (hd : ∀ E t, Φ E t → TCmp c E t)
    (hpl : ∀ E t, Φ E t → E.pLen = g.pLen) : RelCT isa (Both Φ) g.generate fun _ _ => True := by
  refine both_exists fun E => relct_of_fact (P := E.Valid ∧ E.pLen = g.pLen ∧ E.qLen = g.qLen)
    (fun s t h => ?_) fun ⟨v, hp, hq⟩ =>
      (generate_ct G v hp hq).mono (fun s t h => ⟨(), by obtain ⟨_, _, _, I, _⟩ := hd _ _ h.1; exact I,
        by obtain ⟨_, _, _, I, _⟩ := hd _ _ h.2; exact I⟩) fun _ _ h => h
  have hp := hpl _ _ h.1
  obtain ⟨s', rfl, F, _⟩ := hd _ _ h.1
  refine ⟨F.valid, hp, ?_⟩
  have := G.lengths
  change pLenOf s' = _ at hp
  change (if pLenOf s' = 128 then 20 else 32) = _
  split <;> omega

theorem dispatch_ct {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) :
    RelCT isa (Both TEnt) (dispatch g1 g2 g3) fun _ _ => True := by
  unfold dispatch
  simp only [seqs]
  refine RelCT.seq (both_post (Ψ := TPtr)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h r hr => ?_) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨s, rfl, F, P⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact P.inv.esp
  · obtain ⟨s, rfl, F, P⟩ := h
    exact WP.mono (dPtr_ok F P) fun t₁ D => ⟨s, t, rfl, F, P, D⟩
  refine RelCT.seq (both_post (Ψ := TCmp 128)
    (both_agree [.esp, .edi, .ebx] (fun E => ptrPins E E.stP) (fun E t h r hr => ?_)
      (tcheck _ _ (by decide +kernel))) fun E t h => ?_) ?_
  · obtain ⟨s, t₀, rfl, F, P, D⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [D.esp]; exact P.inv.esp
    · rw [D.edi]; exact P.base.edi
    · rw [D.ebx]; exact (narrow _).symm
  · obtain ⟨s, t₀, rfl, F, P, D⟩ := h
    exact WP.mono (dRead_ok F P D) fun t₅ R => ⟨s, rfl, F, ⟨R.base, R.left, R.cur, R.status⟩, R.eax, R.zf⟩
  refine both_ite (fun E => decide (E.pLen = 128)) (fun E t h => by obtain ⟨_, _, _, _, _, z⟩ := h; exact z)
    (run_ct G1 (fun _ _ h => h.1) fun E t h => by rw [h1]; exact of_decide_eq_true h.2) ?_
  refine RelCT.seq (both_post (Ψ := fun E t => TCmp 256 E t ∧ decide (E.pLen = 128) = false)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h => h.1.pins) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨⟨s, rfl, F, I, ax, _⟩, n⟩ := h
    have p32 : pLenOf s < 2 ^ 32 := by rcases F.pLens with h | h | h <;> rw [h] <;> decide
    refine wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ⟨⟨s, rfl, F, ⟨I.1.regs f₃.mem (by rw [f₃.gpr]) (by rw [f₃.gpr])
      f₃.rd f₃.wr f₃.syms, by rw [f₃.mem]; exact I.2.1, by rw [f₃.mem]; exact I.2.2.1, by rw [f₃.mem]; exact I.2.2.2⟩,
      by rw [f₃.gpr, ax], ?_⟩, n⟩
    show t₃.zf = _
    rw [z₃, ax]
    exact congrArg some (sub_beq (b := 256) p32 (by decide))
  refine both_ite (fun E => decide (E.pLen = 256))
    (fun E t h => by obtain ⟨⟨_, _, _, _, _, z⟩, _⟩ := h; exact z)
    (run_ct G2 (fun _ _ h => h.1.1) fun E t h => by rw [h2]; exact of_decide_eq_true h.2)
    (run_ct G3 (fun _ _ h => h.1.1) fun E t h => ?_)
  obtain ⟨⟨⟨s, rfl, F, _⟩, n128⟩, n256⟩ := h
  have a := of_decide_eq_false n128
  have b := of_decide_eq_false n256
  rw [h3]
  change ¬ pLenOf s = 128 at a
  change ¬ pLenOf s = 256 at b
  change pLenOf s = 384
  rcases F.pLens with c | c | c <;> omega

/-- Two runs from inputs the contract makes public leak the same. -/
theorem constantTime {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) :
    ConstantTime isa genContract.pre genContract.pub (code g1 g2 g3) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold code
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => (pub_env h.2.2).2) ?_
  refine RelCT.seq (R := VG.X86.Taint.Agree (τr [.esp])) ?_ (tcheck [.esp] _ (by decide +kernel))
  have body := RelCT.seq (both_post (Ψ := TEnt) entry_ct
    fun E t ⟨s, hE, F, ht⟩ => ht ▸ WP.mono (entry_ok F) fun u P => ⟨s, hE, F, P⟩) (dispatch_ct G1 G2 G3 h1 h2 h3)
  refine ((body.mono (fun a b ⟨s₁, s₂, ⟨p₁, p₂, pb⟩, ha, hb⟩ => ⟨callEnv s₁, ⟨s₁, rfl, call_facts p₁, ha⟩,
      ⟨s₂, (pub_env pb).1.symm, call_facts p₂, hb⟩⟩) fun _ _ h => h).wpDep
    (F := fun (σ u : State) => u.gpr .esp = σ.gpr .esp) fun a b h => ?_).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, H, e₁, e₂⟩ => agree_regs fun r hr => ?_
  · obtain ⟨s₁, s₂, ⟨p₁, p₂, _⟩, rfl, rfl⟩ := h
    exact ⟨WP.mono (body_ok G1 G2 G3 h1 h2 h3 (call_facts p₁)) fun t ⟨_, _, K⟩ => K.1 .esp (by decide),
      WP.mono (body_ok G1 G2 G3 h1 h2 h3 (call_facts p₂)) fun t ⟨_, _, K⟩ => K.1 .esp (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨s₁, s₂, ⟨_, _, pb⟩, rfl, rfl⟩ := H
    rw [e₁, e₂, pushed_esp, pushed_esp, (pub_env pb).2]

end VG.Proof.Dsa.X86.Generation

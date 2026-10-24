module

import VerifiedGarbage.Proof.Dsa.X86.Generation.FinishCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Entry
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
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

theorem pub_env {s₁ s₂ : State} (h : genContract.pub s₁ s₂) :
    callEnv s₁ = callEnv s₂ ∧ s₁.gpr .esp = s₂.gpr .esp := by
  sig_pub [genContract, Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at h
  obtain ⟨esp, sy, leak, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  rw [a4, a5, a6, a7, a8, a9] at leak
  have len : ∀ m p n, (List.map (fun x : Byte => x.toNat) (Spec.Rsa.bytesAt m p n)).length = n := by
    simp [Spec.Rsa.bytesAt]
  obtain ⟨l12, l3⟩ := List.append_inj leak (by simp only [List.length_append, len])
  obtain ⟨l1, l2⟩ := List.append_inj l12 (by simp only [len])
  refine ⟨?_, esp⟩
  simp only [callEnv, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, esp, sy, map_toNat_inj l1, map_toNat_inj l2,
    map_toNat_inj l3]

/-- At the entry: the frame of saved registers pushed, from a state the
contract holds in. -/
def TIn (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ t = entered s

/-- After the entry. -/
def TEnt (E : Env) (t : State) : Prop := ∃ s, callEnv s = E ∧ CallFacts s ∧ EPost s t

theorem entry_ct : RelCT isa (Both TIn) (.block entry) fun _ _ => True := by
  rw [show entry = [.mov .edi (.mem (VG.Impl.Mont.X86.Compact.arg 10))] ++ entry.tail from rfl]
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

/-- After `p_len`'s comparison with `c`. -/
def TCmp (c : Nat) (E : Env) (t : State) : Prop :=
  ∃ s t₀, callEnv s = E ∧ CallFacts s ∧ EPost s t₀ ∧ t.mem = t₀.mem ∧ t.gpr .edi = t₀.gpr .edi ∧
    t.gpr .esp = t₀.gpr .esp ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr ∧ t.syms = t₀.syms ∧ t.gpr .eax = arg s 2 ∧
    isa.eval .e t = some (decide (E.pLen = c))

theorem TCmp.sIn {c : Nat} {E : Env} {t : State} (h : TCmp c E t) : SIn E t := by
  obtain ⟨s, t₀, rfl, F, P, m, e, p, r, w, y, _⟩ := h
  exact ⟨P.base.regs m e p r w y, by rw [m]; exact P.seed, by rw [m]; exact P.left, by rw [m]; exact P.status,
    by rw [m]; exact P.used⟩

theorem TCmp.pins {c : Nat} {E : Env} {t : State} (h : TCmp c E t) : ∀ r ∈ [Reg.esp], t.gpr r = baseVal E r := by
  obtain ⟨s, t₀, rfl, F, P, m, e, p, r, w, y, _⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [p]; exact P.inv.esp

theorem zf_cmp {x : BitVec 32} {c : BitVec 32} : decide (x = c) = decide (x.toNat = c.toNat) :=
  decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩

/-- One geometry, chosen by `p_len`. -/
theorem run_ct {g : Geo} (G : GeoOk g) {c : Nat} {Φ : Env → State → Prop} (hd : ∀ E t, Φ E t → TCmp c E t)
    (hpl : ∀ E t, Φ E t → E.pLen = g.pLen) : RelCT isa (Both Φ) g.generate fun _ _ => True := by
  refine both_exists fun E => relct_of_fact (P := E.Valid ∧ E.pLen = g.pLen ∧ E.qLen = g.qLen)
    (fun s t h => ?_) fun ⟨v, hp, hq⟩ =>
      (generate_ct G v hp hq).mono (fun s t h => ⟨(), (hd _ _ h.1).sIn, (hd _ _ h.2).sIn⟩) fun _ _ h => h
  have hp := hpl _ _ h.1
  obtain ⟨s', t₀, rfl, F, _⟩ := hd _ _ h.1
  refine ⟨F.valid, hp, ?_⟩
  have lengths := F.lengths
  have := G.lengths
  change (arg s' 2).toNat = _ at hp
  change (arg s' 3).toNat = _
  rcases lengths with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> rcases this with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;> omega

theorem dispatch_ct {g1 g2 g3 : Geo} (G1 : GeoOk g1) (G2 : GeoOk g2) (G3 : GeoOk g3) (h1 : g1.pLen = 128)
    (h2 : g2.pLen = 256) (h3 : g3.pLen = 384) :
    RelCT isa (Both TEnt) (dispatch g1 g2 g3) fun _ _ => True := by
  unfold dispatch
  refine RelCT.seq (both_post (Ψ := TCmp 128)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h r hr => ?_) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨s, rfl, F, P⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact P.inv.esp
  · obtain ⟨s, rfl, F, P⟩ := h
    refine wp_ldm (B := (callEnv s).sp) P.inv.esp (by rw [addrArg]; exact argAccess F P.inv (by decide))
      fun t₁ u₁ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ?_
    have eax₁ : t₁.gpr .eax = arg s 2 := by rw [u₁.gpr, addrArg, argValue F P.inv (by decide)]
    refine ⟨s, t, rfl, F, P, by rw [f₂.mem, u₁.mem], by rw [f₂.gpr, u₁.other _ (by decide)],
      by rw [f₂.gpr, u₁.other _ (by decide)], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.syms, u₁.syms],
      by rw [f₂.gpr, eax₁], ?_⟩
    show t₂.zf = _
    rw [z₂, eax₁, sub_beq_zero, zf_cmp]
    rfl
  refine both_ite (fun E => decide (E.pLen = 128)) (fun E t h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, z⟩ := h; exact z)
    (run_ct G1 (fun _ _ h => h.1) fun E t h => by rw [h1]; exact of_decide_eq_true h.2) ?_
  refine RelCT.seq (both_post (Ψ := fun E t => TCmp 256 E t ∧ decide (E.pLen = 128) = false)
    (both_agree [.esp] (fun E => baseVal E) (fun E t h => h.1.pins) (tcheck _ _ (by decide +kernel)))
    fun E t h => ?_) ?_
  · obtain ⟨⟨s, t₀, rfl, F, P, m, e, p, r, w, y, ax, _⟩, n⟩ := h
    refine wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ⟨⟨s, t₀, rfl, F, P, by rw [f₃.mem, m], by rw [f₃.gpr, e],
      by rw [f₃.gpr, p], by rw [f₃.rd, r], by rw [f₃.wr, w], by rw [f₃.syms, y], by rw [f₃.gpr, ax], ?_⟩, n⟩
    show t₃.zf = _
    rw [z₃, ax, sub_beq_zero, zf_cmp]
    rfl
  refine both_ite (fun E => decide (E.pLen = 256))
    (fun E t h => by obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, z⟩, _⟩ := h; exact z)
    (run_ct G2 (fun _ _ h => h.1.1) fun E t h => by rw [h2]; exact of_decide_eq_true h.2)
    (run_ct G3 (fun _ _ h => h.1.1) fun E t h => ?_)
  obtain ⟨⟨⟨s, t₀, rfl, F, _⟩, n128⟩, n256⟩ := h
  have lengths := F.lengths
  have a := of_decide_eq_false n128
  have b := of_decide_eq_false n256
  rw [h3]
  change ¬ (arg s 2).toNat = 128 at a
  change ¬ (arg s 2).toNat = 256 at b
  change (arg s 2).toNat = 384
  rcases lengths with ⟨c, _⟩ | ⟨c, _⟩ | ⟨c, _⟩ <;> omega

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

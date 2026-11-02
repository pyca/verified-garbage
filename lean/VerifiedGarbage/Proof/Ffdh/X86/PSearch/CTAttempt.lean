module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CTExits
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Classify
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CTExits
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Classify
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-! # Two runs of an attempt (x86)

Two runs with the same public descriptor and loop point pass
`vg_ffdh_parameter_candidate_sieved` the same arguments and the same public
data (`callee_pub`), so their attempts leak the same (`attempt_ct`); after
it, `classify` branches on the candidate's status, a function of the public
tape (`classify_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)

/-- Two entry states with the same public descriptor have the same arguments. -/
theorem args_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) {i : Nat} (hi : i < 10) : arg o₁ i = arg o₂ i := by
  have ofn : ∀ {x y : BitVec 32}, x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg PPub.op e
  · exact ofn (congrArg PPub.len e)
  · exact congrArg PPub.up e
  · exact ofn (congrArg PPub.bits e)
  · exact ofn (congrArg PPub.gen e)
  · exact congrArg PPub.rp e
  · exact ofn (congrArg PPub.randLen e)
  · exact congrArg PPub.B e
  · exact ofn (congrArg PPub.slen e)
  · exact congrArg PPub.S e

theorem callArg_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) (used j : Nat) :
    callArg o₁ used j = callArg o₂ used j := by
  unfold callArg
  simp only [args_eq e (i := 0) (by omega), args_eq e (i := 1) (by omega), args_eq e (i := 3) (by omega),
    args_eq e (i := 4) (by omega), args_eq e (i := 5) (by omega), args_eq e (i := 6) (by omega),
    args_eq e (i := 7) (by omega), args_eq e (i := 8) (by omega), args_eq e (i := 9) (by omega)]

theorem callee_pub {o₁ o₂ t₁ t₂ : State} {ds₁ ds₂ : List Nat} {f₁ f₂ : Nat → BitVec 32} {used : Nat}
    (e : ofState o₁ = ofState o₂) (h₁ : Fr o₁ ds₁ f₁ t₁) (h₂ : Fr o₂ ds₂ f₂ t₂)
    (hu : used < (arg o₁ 6).toNat) (a₁ : ArgsAt o₁ used 9 t₁.mem) (a₂ : ArgsAt o₂ used 9 t₂.mem)
    (rd wr : List Region) :
    Cand.contract.pub (t₁.callEntry.withRegions rd wr) (t₂.callEntry.withRegions rd wr) := by
  have A₁ := h₁.abi
  have A₂ := h₂.abi
  have hu₂ : used < (arg o₂ 6).toNat := by rw [← args_eq e (i := 6) (by omega)]; exact hu
  have sp : o₁.gpr .esp = o₂.gpr .esp := congrArg PPub.sp e
  sig_pub [Cand.contract, Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  have c₁ := fun j (hj : j < 9) => ce_arg A₁ h₁.esp a₁ rd wr hj
  have c₂ := fun j (hj : j < 9) => ce_arg A₂ h₂.esp a₂ rd wr hj
  simp only [c₁ 0 (by decide), c₁ 1 (by decide), c₁ 2 (by decide), c₁ 3 (by decide), c₁ 4 (by decide),
    c₁ 5 (by decide), c₁ 6 (by decide), c₁ 7 (by decide), c₁ 8 (by decide),
    c₂ 0 (by decide), c₂ 1 (by decide), c₂ 2 (by decide), c₂ 3 (by decide), c₂ 4 (by decide),
    c₂ 5 (by decide), c₂ 6 (by decide), c₂ 7 (by decide), c₂ 8 (by decide)]
  have ca := callArg_eq e used
  refine ⟨by rw [h₁.esp, h₂.esp, sp], by rw [h₁.syms, h₂.syms]; exact congrArg PPub.T e, ?_, ca 0, ca 1, ca 2,
    ca 3, ca 4, ca 5, ca 6, ca 7, ca 8⟩
  have l₁ : (BitVec.ofNat 32 ((arg o₁ 6).toNat - used)).toNat = (arg o₁ 6).toNat - used := by
    have := (arg o₁ 6).isLt; rw [BitVec.toNat_ofNat]; omega
  have l₂ : (BitVec.ofNat 32 ((arg o₂ 6).toNat - used)).toNat = (arg o₂ 6).toNat - used := by
    have := (arg o₂ 6).isLt; rw [BitVec.toNat_ofNat]; omega
  simp only [callArg, Nat.reduceEqDiff, ↓reduceIte, l₁, l₂]
  rw [ret_eq A₁ h₁.esp, ret_eq A₂ h₂.esp, entry_bytes h₁ hu, entry_bytes h₂ hu₂, e]

/-- Relating two runs for each public datum. -/
theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

/-- In the attempt's frame. -/
def FrAt (q : Lp) (f : State) : Prop := ∃ s, LiveAt q s ∧ q.2.1 < q.1.randLen ∧ f = allocFrame argsBytes s

/-- With the arguments in the frame. -/
def CallAt (q : Lp) (t : State) : Prop :=
  ∃ o, ofState o = q.1 ∧ Fr o liveDs (liveF q.1 (o.gpr .esi) q.2.1 q.2.2) t ∧ ArgsAt o q.2.1 9 t.mem ∧
    q.2.1 < q.1.randLen

theorem frAt_pins : Pins FrAt [.esi, .esp] := by
  intro k f₁ f₂ ⟨s₁, ⟨o₁, L₁⟩, _, e₁⟩ ⟨s₂, ⟨o₂, L₂⟩, _, e₂⟩ r hr
  subst e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), L₁.esi, L₂.esi]
  · rw [allocFrame_esp, allocFrame_esp, L₁.esp, L₂.esp]

/-- What the callee reads and writes, from the public descriptor. -/
abbrev callRdK (p : PPub) (used : Nat) : List Region :=
  [⟨(p.rp + BitVec.ofNat 32 used).setWidth 64, p.randLen - used⟩,
    ⟨p.T.setWidth 64, 8192⟩]
abbrev callWrK (p : PPub) : List Region :=
  [⟨p.op.setWidth 64, p.len⟩, ⟨(p.S + BitVec.ofNat 32 candOff).setWidth 64, 8⟩, ⟨p.B.setWidth 64, p.slen * 8⟩,
    ⟨p.sp.setWidth 64 - 212#64 + BitVec.ofNat 64 176, 36⟩]

theorem call_ct (q : Lp) :
    RelCT isa (fun t₁ t₂ => CallAt q t₁ ∧ CallAt q t₂)
      (.call "vg_ffdh_parameter_candidate_sieved" Impl.Ffdh.X86.Candidate.code) fun _ _ => True := by
  refine RelCT.call Cand.verified.1 Cand.verified.2.1 (callRdK q.1 q.2.1) (callWrK q.1)
    fun t₁ t₂ ⟨⟨o₁, e₁, F₁, a₁, hu₁⟩, ⟨o₂, e₂, F₂, a₂, hu₂⟩⟩ => ?_
  obtain ⟨p, used, n⟩ := q
  dsimp only at e₁ e₂ F₁ F₂ a₁ a₂ hu₁ hu₂ ⊢
  subst e₁
  have r₁ : callRdK (ofState o₁) used = callRd o₁ used := by rw [callRd, tableRs_eq]; rfl
  have w₁ : callWrK (ofState o₁) = callWr o₁ := rfl
  have r₂ : callRdK (ofState o₂) used = callRd o₂ used := by rw [callRd, tableRs_eq]; rfl
  have w₂ : callWrK (ofState o₂) = callWr o₂ := rfl
  have c₁ := call_covers (t := t₁) F₁.abi hu₁ F₁.rd F₁.wr
  have hu₂' : used < (arg o₂ 6).toNat := by have := hu₂; rw [← e₂] at this; exact this
  have c₂ := call_covers (t := t₂) F₂.abi hu₂' F₂.rd F₂.wr
  have eqR : callRd o₂ used = callRd o₁ used := by rw [← r₁, ← r₂, e₂]
  have eqW : callWr o₂ = callWr o₁ := by rw [← w₁, ← w₂, e₂]
  rw [r₁, w₁]
  rw [eqR, eqW] at c₂
  refine ⟨call_pre F₁.abi hu₁ F₁.esp a₁ F₁.syms F₁.frame, ?_, callee_pub e₂.symm F₁ F₂ hu₁ a₁ a₂ _ _,
    c₁.1, c₁.2, c₂.1, c₂.2, ?_⟩
  · rw [← eqR, ← eqW]
    exact call_pre F₂.abi hu₂' F₂.esp a₂ F₂.syms F₂.frame
  · rw [F₁.esp, F₂.esp, show o₁.gpr .esp = o₂.gpr .esp from (congrArg PPub.sp e₂).symm]

theorem attempt_ct : RelCT isa (Two fun (q : Lp) s => LiveAt q s ∧ q.2.1 < q.1.randLen) attempt fun _ _ => True := by
  unfold attempt
  refine RelCT.frameAlloc ((RelCT.seq (two_piece (Ψ := CallAt) [.esi, .esp] frAt_pins (by taint_decide)
    fun q f ⟨s, ⟨o, L⟩, hu, e⟩ => ?_) (two_of call_ct)).mono
      (fun a b ⟨s₁, s₂, ⟨q, h₁, h₂⟩, e₁, e₂⟩ => ⟨q, ⟨s₁, h₁.1, h₁.2, e₁⟩, ⟨s₂, h₂.1, h₂.2, e₂⟩⟩) fun _ _ h => h)
  subst e
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  obtain ⟨p, used, n⟩ := q
  dsimp only at e S hu ⊢
  subst e
  exact WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ⟨o, rfl, F, a, hu⟩

/-! ## After the attempt -/

/-- The status of the candidate at the loop point `q`. -/
abbrev Lp.status (q : Lp) : Nat := candidateStatus (candAt q.1.bits q.1.gen q.1.rand q.2.1)

/-- The loop point after the candidate's octets. -/
abbrev Lp.adv (q : Lp) : Lp := (q.1, q.2.1 + q.1.cu q.2.1, q.2.2)

/-- After an attempt from the loop point `q`. -/
def ClsAt (q : Lp) (u : State) : Prop :=
  ∃ o s₀, ofState o = q.1 ∧ Live q.1 o q.2.1 q.2.2 s₀ ∧ St o liveDs (liveF q.1 (o.gpr .esi) q.2.1 q.2.2) u ∧
    u.gpr .eax = BitVec.ofNat 32 q.status ∧
    u.mem.readW (addr (arg o 9) candOff) 32 = BitVec.ofNat 32 (q.1.cu q.2.1)

/-- The status in `edx` compared with `j`, the candidate's octets consumed. -/
def CmpAt (j : Nat) (q : Lp) (t : State) : Prop :=
  LiveAt q.adv t ∧ t.gpr .edx = BitVec.ofNat 32 q.status ∧ isa.eval .e t = some (decide (q.status = j))

theorem cmpAt_pins (j : Nat) : Pins (CmpAt j) [.esi, .esp] := any_pins (fun q => q.1) fun _ _ h => h.1.any

theorem cmp_ok {q : Lp} {t : State} {i : Nat} (h : CmpAt i q t) (j : Nat) (hj : j ≤ 2) :
    WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 j))]) t (CmpAt j q) := by
  obtain ⟨⟨o, L⟩, he, _⟩ := h
  refine wp_cmpi fun t' F _ z => WP.block_nil ⟨⟨o, L.fupd F⟩, by rw [F.gpr]; exact he, ?_⟩
  exact cmp_status (candidateStatus_le _) hj he z

/-- `mov eax, [esi + 56]; mov ecx, [esi + 16]; cmp eax, ecx`: the borrow when the tape holds less than the
entropy cap. -/
theorem capCmp_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    WP isa (.block [.mov .eax (.mem (st leftOff)), .mov .ecx (.mem (st capOff)), .alu .cmp .eax (.reg .ecx)]) s
      fun t => Live p o used n t ∧ isa.eval .b t = some (decide (p.randLen - used < p.cap)) := by
  have S := h.st
  have hnl := h.n_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 6).isLt
  have hc := cap_lt A
  refine S.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) (d := capOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_cmp fun t₃ F₃ c₃ _ => WP.block_nil ⟨(S₂.fupd F₃).live hul hnl, ?_⟩
  show t₃.cf = _
  rw [c₃, o₂ .eax (by decide), g₁, g₂]
  simp only [liveF, leftOff, capOff, ↓reduceIte, Nat.reduceEqDiff]
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]

theorem shortage_ct : RelCT isa (Two LiveAt) shortage fun _ _ => True := by
  unfold shortage
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧
      isa.eval .b t = some (decide (q.1.randLen - q.2.1 < q.1.cap)))
    [.esi, .esp] liveAt_pins (by taint_decide) fun q s ⟨o, L⟩ =>
      WP.mono (capCmp_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  exact two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) request_ct)
    (two_map id (fun _ _ h => h.1.1) exhausted_ct)

theorem classify_ct : RelCT isa (Two ClsAt) classify fun _ _ => True := by
  unfold classify
  refine RelCT.seq (two_piece (Ψ := CmpAt 1) [.esi, .esp]
    (any_pins (fun q => q.1) fun q s ⟨o, _, e, _, S, _⟩ => ⟨o, _, _, e, S⟩) (by taint_decide)
    fun q u ⟨o, s₀, e, L₀, S, he, hcu⟩ => ?_) ?_
  · obtain ⟨p, used, n⟩ := q
    dsimp only at e L₀ S he hcu ⊢
    subst e
    have hlen := rand_length (o := o)
    have hul := L₀.used_le
    have hcl : used + (ofState o).cu used ≤ (ofState o).randLen := by
      have h2 := candUsed_le (ofState o).bits (ofState o).gen (ofState o).rand used
      rw [hlen] at h2
      show used + candUsed _ _ _ _ ≤ _
      have : (ofState o).randLen = (arg o 6).toNat := rfl
      omega
    exact advance_ok (S.withWord hcu) hcl fun t S' hed _ => wp_cmpi fun t' F _ z => WP.block_nil
      ⟨⟨o, (S'.fupd F).live hcl L₀.n_le⟩, by rw [F.gpr, hed, he], cmp_status (candidateStatus_le _) (by decide)
        (hed.trans he) z⟩
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)) ?_
  refine RelCT.seq (two_piece (Ψ := CmpAt 2) [.esi, .esp]
    (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)
    fun q t h => cmp_ok h.1 2 (by decide)) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)) ?_
  exact two_map Lp.adv (fun _ _ h => h.1.1) shortage_ct

end VG.Proof.Ffdh.X86.PSearch

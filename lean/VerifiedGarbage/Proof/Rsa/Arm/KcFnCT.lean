module

public import VerifiedGarbage.Proof.Rsa.Arm.KcCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcFn
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Rsa.Arm.KcTaint
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # The checks of an RSA key on ARMv7: a function is constant time

`fn_ct`: two runs from initial states that agree on what the contracts make
public (`PubF`: the pointers, the lengths, `n` and `e`) are related at every
step by what correctness says of each run (`LiftB`); the entry and the
restore read the stack arguments (`argTaint`), the other pieces the
registers correctness determines, the checks of `n` and `e` branch alike as
both are public, `exponentCheck` is `exponentCheck_ct`, and the checks are
the body's own.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What two runs' initial states agree on. -/
structure PubF (nA : Nat) (σ₁ σ₂ : State) : Prop where
  sp : σ₁.sp = σ₂.sp
  n : Spec.Rsa.bytesAt σ₁.mem (State.addr (σ₁.gpr .r0)) (fK σ₁) =
    Spec.Rsa.bytesAt σ₂.mem (State.addr (σ₂.gpr .r0)) (fK σ₂)
  e : eBytes σ₁ = eBytes σ₂
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  args : ∀ i < nA, stackArg σ₁ i = stackArg σ₂ i

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

theorem PubF.geo_eq {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) (h : iS + 1 < nA) : geo iS σ₁ = geo iS σ₂ := by
  unfold geo fK
  rw [p.args iS (by omega), p.args (iS + 1) h, p.r1]

theorem PubF.nV {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : nV σ₁ = nV σ₂ := congrArg Spec.Rsa.os2ip p.n
theorem PubF.eV {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : eV σ₁ = eV σ₂ := congrArg Spec.Rsa.os2ip p.e
theorem PubF.K {σ₁ σ₂ : State} (p : PubF nA σ₁ σ₂) : fK σ₁ = fK σ₂ := by simp only [fK, p.r1]

/-- What makes a state of a run agree with the other's on the stack arguments. -/
structure RunF (nA iS : Nat) (ins : List (Nat × Nat)) (σ s : State) : Prop where
  pre : FnPre nA iS ins σ
  sp : s.sp = σ.sp
  wr : s.wr = σ.wr
  args : ∀ i < nA, stackArg s i = stackArg σ i

theorem FnBase.run {σ s : State} (h : FnBase nA iS ins σ s) : RunF nA iS ins σ s :=
  ⟨h.pre, h.sp, h.wr, fun _ hi => h.arg hi⟩

theorem RunF.wf {σ s : State} (h : RunF nA iS ins σ s) :
    s.sp.toNat + 4 * nA ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4 * nA⟩ r := by
  refine ⟨by rw [h.sp]; exact h.pre.sp, ?_⟩
  have e : (⟨State.addr s.sp, 4 * nA⟩ : Region) = rA nA σ := by
    simp only [rA, stackArgAddr, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [e, h.wr, h.pre.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact h.pre.sA.symm

theorem agreeF {σ₁ σ₂ s₁ s₂ : State} (p : PubF nA σ₁ σ₂) (h₁ : RunF nA iS ins σ₁ s₁)
    (h₂ : RunF nA iS ins σ₂ s₂) {rs : List Reg} (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (argTaint rs (4 * nA)) s₁ s₂ := by
  have hsp : s₁.sp = s₂.sp := by rw [h₁.sp, h₂.sp, p.sp]
  exact agree_argTaint hr hsp h₁.wf h₂.wf
    (argMem_of (j := nA) hsp (by rw [h₁.sp]; exact h₁.pre.sp) fun i hi => by
      rw [h₁.args i hi, h₂.args i hi, p.args i hi])

/-- A piece the taint analysis checks from the stack arguments and the registers `rs`. -/
theorem pieceF {G H : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (argTaint rs (4 * nA)) c hc).isSome = true)
    (run : ∀ a s, G a s → RunF nA iS ins a s)
    (regs : ∀ a₁ a₂ s t, PubF nA a₁ a₂ → G a₁ s → G a₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (hw : ∀ a s, G a s → WP isa c s (H a)) :
    RelCT isa (LiftB (PubF nA) fun a _ _ s => G a s) c (LiftB (PubF nA) fun a _ _ t => H a t) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := rel_agree (F := G a₁) (F' := G a₂) (G := H a₁) (G' := H a₂) (argTaint rs (4 * nA))
    (fun _ _ h h' => agreeF p (run _ _ h) (run _ _ h') (regs _ _ _ _ p h h')) hc (hw a₁) (hw a₂)
    s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.1, r.2.2⟩

/-- The registers of two states of `Mid` agree on `r8`. -/
theorem mid_r8 {a₁ a₂ s t : State} {A₁ A₂ : Nat → Nat} (h : iS + 1 < nA) (p : PubF nA a₁ a₂)
    (h₁ : Mid nA iS ins a₁ s A₁) (h₂ : Mid nA iS ins a₂ t A₂) : ∀ r ∈ [Reg.r8], s.gpr r = t.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  rw [h₁.ws.r8, h₂.ws.r8, p.geo_eq h]

/-- `exponentCheck` in two runs from the same exponent. -/
theorem expPiece :
    RelCT isa (LiftB (PubF nA) fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
        ExponentInput (a.gpr .r2) (eBytes a) s) exponentCheck
      (LiftB (PubF nA) fun a _ _ t => Mid nA iS ins a t (aEnt ins a) ∧
        t.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a)).toNat) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have pos : 0 < (eBytes a₁).length := by
    rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact h₁.1.base.pre.e1
  have h₂' : ExponentInput (a₁.gpr .r2) (eBytes a₁) t := by rw [p.r2, p.e]; exact h₂.2
  have r := (((exponentCheck_ct pos).mono
    (P' := fun (u₁ u₂ : State) => (Mid nA iS ins a₁ u₁ (aEnt ins a₁) ∧ ExponentInput (a₁.gpr .r2) (eBytes a₁) u₁) ∧
      (Mid nA iS ins a₂ u₂ (aEnt ins a₂) ∧ ExponentInput (a₂.gpr .r2) (eBytes a₂) u₂ ∧
        ExponentInput (a₁.gpr .r2) (eBytes a₁) u₂))
    (fun _ _ h => ⟨h.1.2, h.2.2.2⟩) fun _ _ h => h).wp
    (F₁ := fun (u : State) => Mid nA iS ins a₁ u (aEnt ins a₁) ∧
      u.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a₁)).toNat)
    (F₂ := fun (u : State) => Mid nA iS ins a₂ u (aEnt ins a₂) ∧
      u.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (eV a₂)).toNat)
    fun _ _ h => ⟨expCheck_ok h.1.1 h.1.2, expCheck_ok h.2.1 h.2.2.1⟩) s t tr₁ tr₂ s' t'
    ⟨h₁, h₂.1, h₂.2, h₂'⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

theorem fn_ct {body : Prog isa} {vf : State → Vals} (h4 : 4 * iS < 4096) (hS : iS + 1 < nA)
    (hentry : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] (4 * nA))
      (entry (4 * iS) (ins.map fun p => (4 * p.1, p.2))) hc).isSome = true)
    (hrestore : ∃ hc, (VG.Taint.check taint (argTaint [] (4 * nA)) (.block (restore (4 * iS))) hc).isSome = true)
    (hv : ∀ σ, FnPre nA iS ins σ → aEnt ins σ = vals (vf σ))
    (hA : ∀ σ, FnPre nA iS ins σ → ∀ j < nArr, aEnt ins σ j < 2 ^ (32 * (geo iS σ).w))
    (hbody : RelCT isa (LiftB (PubF nA) fun a σ v s => s = σ ∧ FnBase nA iS ins a σ ∧ BodyIn (geo iS a) v s)
      body (LiftB (PubF nA) fun a σ _ t => FnBase nA iS ins a σ ∧ ∃ A live c, Stg (geo iS a) σ A live c t)) :
    RelCT isa (fun s t => FnPre nA iS ins s ∧ FnPre nA iS ins t ∧ PubF nA s t)
      (fn (4 * iS) (ins.map fun p => (4 * p.1, p.2)) body) fun _ _ => True := by
  unfold fn
  simp only [seqs]
  -- The entry.
  refine RelCT.seq ((pieceF (iS := iS) (ins := ins) (G := fun a s => s = a ∧ FnPre nA iS ins a)
    (H := fun a t => Mid nA iS ins a t (aEnt ins a) ∧ t.z = Spec.Rsa.modulusValid (nV a) (fK a))
    [.r0, .r1, .r2, .r3] hentry (fun a s ⟨e, h⟩ => by subst e; exact ⟨h, rfl, rfl, fun _ _ => rfl⟩)
    (fun a₁ a₂ s t p ⟨e₁, _⟩ ⟨e₂, _⟩ => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      exacts [p.r0, p.r1, p.r2, p.r3])
    fun a s ⟨e, h⟩ => by subst e; exact entry_ok h h4).mono
      (fun s t ⟨h₁, h₂, p⟩ => ⟨s, s, vf s, t, t, vf t, p, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩) fun _ _ h => h) ?_
  -- The branches, to `FnBase` for `restore`.
  refine RelCT.seq (R := LiftB (PubF nA) fun a _ _ s => FnBase nA iS ins a s) (RelCT.ite ?_ ?_ ?_) ?_
  · rintro s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨_, z₁⟩, ⟨_, z₂⟩⟩
    show some s.z = some t.z
    rw [z₁, z₂, p.nV, p.K]
  · -- `n` is valid: `e` checked.
    refine RelCT.seq (R := LiftB (PubF nA) fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
      s.z = Spec.Rsa.exponentValid (eV a)) ?_ ?_
    · unfold eCheck
      simp only [seqs]
      refine RelCT.seq ((pieceB (G := fun a _ _ s => Mid nA iS ins a s (aEnt ins a) ∧
          ExponentInput (a.gpr .r2) (eBytes a) s) [.r8] eLoad_taint
        (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => mid_r8 hS p h₁.1 h₂.1)
        fun a _ _ s h => eLoad_ok h.1).mono (fun _ _ ⟨h, _⟩ => LiftB.mono (fun _ _ _ _ h => h) h)
          fun _ _ h => h) ?_
      refine RelCT.seq expPiece ?_
      exact pieceB [] eCmp_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
        fun a _ _ s h => eCmp_ok h.1 h.2
    refine RelCT.ite ?_ ?_ ?_
    · rintro s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨_, z₁⟩, ⟨_, z₂⟩⟩
      show some s.z = some t.z
      rw [z₁, z₂, p.eV]
    · -- Both are valid: the checks, and the mask returned.
      refine RelCT.seq (hbody.mono (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨h₁, _⟩, ⟨h₂, _⟩⟩, _⟩ =>
        ⟨a₁, s, vf a₁, a₂, t, vf a₂, p, ⟨rfl, h₁.base, h₁.bodyIn _ (hv _ h₁.base.pre) (hA _ h₁.base.pre)⟩,
          ⟨rfl, h₂.base, h₂.bodyIn _ (hv _ h₂.base.pre) (hA _ h₂.base.pre)⟩⟩) fun _ _ h => h) ?_
      exact pieceB [.r8] ret_taint
        (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r rfl
          rw [h₁.ws.r8, h₂.ws.r8, p.geo_eq hS])
        fun a σ _ s ⟨b, A, live, c, h⟩ => WP.mono (ret_ok (b.keep h.keep (fun j hj => List.mem_range.mp hj)
          (by decide) (by decide) h.rest.sp h.rest.rd h.rest.wr) h.ws.r8 h.mask) fun _ h => h.1
    · exact (pieceB [] ret0_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
        fun a _ _ s h => wp_mov (op2_imm (by decide)) fun u up => WP.block_nil
          (h.1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem)).mono
        (fun _ _ ⟨h, _⟩ => h) fun _ _ h => h
  · -- `n` is not valid.
    exact (pieceB [] ret0_taint (fun _ _ _ _ _ _ _ _ _ _ _ => by simp)
      fun a _ _ s h => wp_mov (op2_imm (by decide)) fun u up => WP.block_nil
        (h.1.base.of_rest (up.rest (ws := [.r0]) (by simp)) up.mem)).mono
      (fun _ _ ⟨h, _⟩ => h) fun _ _ h => h
  · -- `restore`.
    exact (pieceF (iS := iS) (ins := ins) (G := fun a s => FnBase nA iS ins a s) (H := fun _ _ => True) []
      hrestore (fun _ _ h => h.run) (fun _ _ _ _ _ _ _ => by simp)
      fun a s h => WP.mono (restore_ok h h4) fun _ _ => trivial).mono (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.Rsa.Arm.KeyCheck

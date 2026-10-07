import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: constant time

Two runs whose public data agree (`encK.pub`: the pointers and lengths, `n`
and `e`) have the same layout, so between the frames' pushes and pops they
are related by `Two`: both satisfy what correctness says of that point
(`Φ`), with the same layout, whatever their secrets. Each piece of code
between the call is checked by the taint analysis from the registers both
runs agree on there (pointers and counters, which the layout fixes; never
`PS`, the zero test or the mask), and correctness carries `Two` past it
(`two_wp`); the call is constant time for its callee's contract, whose
public data agree too (`RelCT.call`). The frames leak only `sp`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- `n` and `e` agree in the two runs' memories. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- What correctness says of a point of the code. -/
abbrev Inv := Lay → (Reg → BitVec 64) → (VReg → BitVec 128) → Mem → State → Prop

/-- Two runs with the same layout, each satisfying `Φ`. -/
def Two (S : Nat) (Φ : Inv) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ e.L.P = S + 1 ∧ LeakEq e.L e.m₁ e.m₂ ∧ RegsOf e.L e.g₁ ∧ RegsOf e.L e.g₂ ∧
    Φ e.L e.g₁ e.v₁ e.m₁ a ∧ Φ e.L e.g₂ e.v₂ e.m₂ b

/-- Code whose runs leak the same, and which establishes `Ψ`. -/
theorem two_wp {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (hct : RelCT isa (Two S Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → RegsOf L g → Φ L g vv m₀ t →
      WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hP, hk, r₁, r₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL hP r₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL hP r₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hP, hk, r₁, r₂, y₁, y₂⟩

/-- Code checked by the taint analysis from the registers `rs`, which both
runs agree on, with `sp`. -/
theorem two_taint {S : Nat} {c : Prog isa} {Φ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa (Two S Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨_, hL, _, _, _, _, f₁, f₂⟩ => by
    obtain ⟨hsp, hr⟩ := hag _ _ _ _ _ _ _ _ _ hL f₁ f₂
    exact ⟨hsp, fun r hr' => hr r (Taint.mem_ofRegs.mp hr')⟩) h

/-- Both of the pieces. -/
theorem two {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → RegsOf L g → Φ L g vv m₀ t →
      WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) :=
  two_wp (two_taint rs h hag) hw

/-! ## The pieces -/

theorem psLoop_ct (S : Nat) :
    RelCT isa (Two S fun L g vv m₀ t => PsInv L g vv m₀ 0 t) psLoop
      (Two S fun L g vv m₀ t => PsInv L g vv m₀ L.pl.toNat t) :=
  two [.x11, .x12, .x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm, f₁.x13.trans f₂.x13.symm]⟩)
    fun _ _ _ _ _ hL _ _ h => psLoop_ok hL h

theorem sep_ct (S : Nat) :
    RelCT isa (Two S fun L g vv m₀ t => PsInv L g vv m₀ L.pl.toNat t) (.block sep)
      (Two S fun L g vv m₀ t => MsgInv L g vv m₀ 0 t) :=
  two [.x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      exact f₁.x13.trans f₂.x13.symm⟩)
    fun _ _ _ _ _ hL _ hg h => sep_inv hL ⟨hg.2.2.2.2.2.2.1.symm, hg.2.2.2.2.2.2.2.symm⟩ h

theorem msgCopy_ct (S : Nat) :
    RelCT isa (Two S fun L g vv m₀ t => MsgInv L g vv m₀ 0 t) msgCopy
      (Two S fun L g vv m₀ t => MsgInv L g vv m₀ L.ml.toNat t) :=
  two [.x6, .x7, .x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x6.trans f₂.x6.symm, f₁.x7.trans f₂.x7.symm, f₁.x13.trans f₂.x13.symm]⟩)
    fun _ _ _ _ _ hL _ _ h => msgCopy_ok hL h

theorem callArgs_ct (S : Nat) :
    RelCT isa (Two S fun L g vv m₀ t => MsgInv L g vv m₀ L.ml.toNat t) (.block callArgs)
      (Two S CallReady) :=
  two [] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL _ hg h => callArgs_inv hL hg h

theorem pub_pub' {L : Lay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : CallReady L g₁ v₁ m₁ a) (hb : CallReady L g₂ v₂ m₂ b) :
    (pubK S).pub (a.callEntry.withRegions (pubRd L) (pubWr L)) (b.callEntry.withRegions (pubRd L) (pubWr L)) := by
  have bn : ∀ {g v m} {t : State}, CallReady L g v m t →
      Spec.Rsa.bytesAt t.mem L.n L.k.toNat = Spec.Rsa.bytesAt m L.n L.k.toNat := fun h =>
    bytesAt_eq fun i hi => h.ctx.byte_ro (R := L.N) hL.oN.symm hL.nS hL.kN.symm (Nat.le_of_lt L.k.isLt) hi
  have be : ∀ {g v m} {t : State}, CallReady L g v m t →
      Spec.Rsa.bytesAt t.mem L.e L.el.toNat = Spec.Rsa.bytesAt m L.e L.el.toNat := fun h =>
    bytesAt_eq fun i hi => h.ctx.byte_ro (R := L.E) hL.oE.symm hL.eS hL.kE.symm (Nat.le_of_lt L.el.isLt) hi
  simp only [pubK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    stackArg_ce, ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, hb.x0, hb.x1, hb.x2, hb.x3, hb.x4, hb.x5,
    hb.x6, hb.x7, ha.ctx.sp, hb.ctx.sp, bn ha, bn hb, be ha, be hb, Nat.mul_zero, Nat.mul_one, true_and]
  exact ⟨by rw [ha.ctx.kept.scr, hb.ctx.kept.scr], by rw [ha.ctx.kept.sl, hb.ctx.kept.sl], hk.1, hk.2⟩

theorem call_ct (v : PubImpl) :
    RelCT isa (Two v.S CallReady) (.call v.name v.code) (Two v.S Called) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hP, hk, _, _, f₁, f₂⟩ := hp
    have c₁ := covers_pub hL f₁.ctx
    have c₂ := covers_pub hL f₂.ctx
    exact RelCT.call (n := v.name) v.correct v.ct (P := fun a b => a = s₁ ∧ b = s₂) (pubRd e.L) (pubWr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨pub_pre' hL hP f₁, pub_pre' hL hP f₂, pub_pub' hL hk f₁ f₂, c₁.1, c₁.2, c₂.1, c₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂)
    fun _ _ _ _ _ hL hP _ h => pub_call v hL hP h

theorem maskArgs_ct (S : Nat) :
    RelCT isa (Two S Called) (.block maskArgs)
      (Two S fun L g vv m₀ t => ∃ y r z, MaskInv L g vv m₀ y r z 0 t) :=
  two [] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ t _ _ _ h => WP.mono (maskArgs_inv h) fun _ h' => ⟨_, _, _, h'⟩

theorem maskLoop_ct (S : Nat) :
    RelCT isa (Two S fun L g vv m₀ t => ∃ y r z, MaskInv L g vv m₀ y r z 0 t) maskLoop fun _ _ => True :=
  two_taint [.x11, .x12, .x13] (by taint_decide) fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, f₁⟩ ⟨_, _, _, f₂⟩ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm, f₁.x13.trans f₂.x13.symm]⟩

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (encK (S + 1)).pre s₁ ∧ (encK (S + 1)).pre s₂ ∧ (encK (S + 1)).pub s₁ s₂ ∧ a = entered s₁ ∧
    b = entered s₂

theorem setup_ct (S : Nat) :
    RelCT isa (Entered S) (.block setup) (Two S fun L g vv m₀ t => PsInv L g vv m₀ 0 t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, hn, he⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay (S + 1) s₂ = lay (S + 1) s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, hsp]
  refine ⟨ht, ⟨lay (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, rfl,
    ⟨?_, ?_⟩, regsOf _ s₁, e ▸ regsOf _ s₂, setup_inv y₁.1 y₁.2, e ▸ setup_inv y₂.1 y₂.2⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5]

theorem enc_ct (v : PubImpl) :
    ConstantTime isa (encK (v.S + 1)).pre (encK (v.S + 1)).pub (code v.name v.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [body_eq]
  refine ((setup_ct v.S).seq ((psLoop_ct v.S).seq ((sep_ct v.S).seq ((msgCopy_ct v.S).seq
    ((callArgs_ct v.S).seq ((call_ct v).seq ((maskArgs_ct v.S).seq (maskLoop_ct v.S)))))))).mono ?_
    fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Enc

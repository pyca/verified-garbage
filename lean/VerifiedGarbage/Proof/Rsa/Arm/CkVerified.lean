module

public import VerifiedGarbage.Proof.Rsa.Arm.CkCorrect
import VerifiedGarbage.Proof.Rsa.Arm.CkTaint
import VerifiedGarbage.Proof.Rsa.Arm.CckVerified
public import VerifiedGarbage.Proof.Rsa.Arm.KcFnCT
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyWCT
import VerifiedGarbage.Proof.Rsa.Arm.KcTaintW
public import VerifiedGarbage.Proof.Rsa.Arm.KcShape
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target

/-! # `vg_rsa_check_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.X25519.Arm (Rest)

theorem ck_body_ct : RelCT isa
    (LiftB (PubF 14) fun a σ v s => s = σ ∧ FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v s ∧ v = vK a) keyBody
    (LiftB (PubF 14) fun a σ _ t => FnBase 14 12 insK a σ ∧ ∃ A live c, Stg (geo 12 a) σ A live c t) :=
  (keyBody_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide))
    (fun a σ => FnBase 14 12 insK a σ)).mono
    (fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨e, x, b, _⟩ => ⟨e, x, b⟩) h)
    fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨x, _, _, _, _, _, _, _, _, _, _, _, A, live, ht⟩ =>
      ⟨x, A, live, _, ht⟩) h

/-- After `shape`: where the checks started, and Z if the key is balanced. -/
def ShapeOut (a σ : State) (v : Vals) (t : State) : Prop :=
  FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v σ ∧ v = vK a ∧ Rest [.r0, .r1, .r2, .r3] σ t ∧ t.mem = σ.mem ∧
    t.z = decide (Balanced 12 a)

theorem balanced_pub {a₁ a₂ : State} (p : PubF 14 a₁ a₂) : decide (Balanced 12 a₁) = decide (Balanced 12 a₂) := by
  simp only [Balanced]
  rw [p.args 3 (by decide), p.args 5 (by decide), p.geo_eq (iS := 12) (by decide)]

/-- `p` of a balanced key has `w / 2` words, as `q`. -/
theorem balanced_lt {a : State} (h : Balanced 12 a) :
    (vK a).p < Bd (geo 12 a) ∧ (vK a).q < Bd (geo 12 a) := by
  obtain ⟨lp, lq, he⟩ := h
  exact ⟨bytesV_lt (k := (stackArg a 3).toNat) (by omega), bytesV_lt (k := (stackArg a 5).toNat) (by omega)⟩

/-- Where the checks started, before `shape`. -/
abbrev XS (a t : State) : Prop := ∃ σ, FnBase 14 12 insK a σ ∧ Rest [.r0, .r1, .r2, .r3] σ t ∧ t.mem = σ.mem

theorem ck_bodyS_ct : RelCT isa
    (LiftB (PubF 14) fun a σ v s => s = σ ∧ FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v s ∧ v = vK a)
    (keyBodyS 12 20)
    (LiftB (PubF 14) fun a σ _ t => FnBase 14 12 insK a σ ∧ ∃ A live c, Stg (geo 12 a) σ A live c t) := by
  unfold keyBodyS
  refine RelCT.seq (R := LiftB (PubF 14) ShapeOut) (pieceFB (nA := 14) (iS := 12) (ins := insK) [.r11] shape_taint
    (fun a σ v s ⟨e, b, _, _⟩ => by subst e; exact b.run)
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.r11, h₂.r11, p.geo_eq (by decide)])
    fun a σ v s ⟨e, b, bi, ev⟩ => by
      subst e
      refine shape_ok b ?_ (by decide) fun t _ rt mt zt => ⟨b, bi, ev, rt, mt, zt⟩
      rw [bi.r11]
      exact BitVec.eq_of_toNat_eq (by simp [fK])) ?_
  refine RelCT.ite (fun s t ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ => by
    show some s.z = some t.z
    rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2, balanced_pub p]) ?_ ?_
  · refine (keyBodyW_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide)) XS).mono
      (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩, hz⟩ => ?_)
      fun _ _ ⟨a₁, t₁, v₁, a₂, t₂, v₂, p, ⟨⟨σ₁, b₁, r₁, m₁⟩, A₁, l₁, c₁, u₁⟩, ⟨⟨σ₂, b₂, r₂, m₂⟩, A₂, l₂, c₂, u₂⟩⟩ =>
        ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨b₁, A₁, l₁, c₁, u₁.of_pre r₁ m₁⟩, ⟨b₂, A₂, l₂, c₂, u₂.of_pre r₂ m₂⟩⟩
    obtain ⟨b₁, bi₁, ev₁, r₁, m₁, z₁⟩ := h₁
    obtain ⟨b₂, bi₂, ev₂, r₂, m₂, z₂⟩ := h₂
    have hz' : s.z = true := Option.some.inj hz
    have B₁ : Balanced 12 a₁ := of_decide_eq_true (z₁ ▸ hz')
    have B₂ : Balanced 12 a₂ := of_decide_eq_true (by rw [← balanced_pub p]; exact z₁ ▸ hz')
    subst ev₁ ev₂
    exact ⟨a₁, s, _, a₂, t, _, p, ⟨rfl, ⟨σ₁, b₁, r₁, m₁⟩, bi₁.of_rest r₁ m₁, B₁.2.2, balanced_lt B₁⟩,
      ⟨rfl, ⟨σ₂, b₂, r₂, m₂⟩, bi₂.of_rest r₂ m₂, B₂.2.2, balanced_lt B₂⟩⟩
  · refine (keyBody_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide)) XS).mono
      (fun s t ⟨⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩, _⟩ =>
        ⟨a₁, s, v₁, a₂, t, v₂, p, ⟨rfl, ⟨σ₁, h₁.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩,
          h₁.2.1.of_rest h₁.2.2.2.1 h₁.2.2.2.2.1⟩,
          ⟨rfl, ⟨σ₂, h₂.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩, h₂.2.1.of_rest h₂.2.2.2.1 h₂.2.2.2.2.1⟩⟩)
      fun _ _ ⟨a₁, t₁, v₁, a₂, t₂, v₂, p, ⟨⟨σ₁, b₁, r₁, m₁⟩, _, _, _, _, _, _, _, _, _, _, _, A₁, l₁, u₁⟩,
        ⟨⟨σ₂, b₂, r₂, m₂⟩, _, _, _, _, _, _, _, _, _, _, _, A₂, l₂, u₂⟩⟩ =>
        ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, ⟨b₁, A₁, l₁, _, u₁.of_pre r₁ m₁⟩, ⟨b₂, A₂, l₂, _, u₂.of_pre r₂ m₂⟩⟩

theorem ck_contract_ct : ConstantTime isa (Spec.Rsa.checkKeyContract abi 0).pre
    (Spec.Rsa.checkKeyContract abi 0).pub VG.Impl.Rsa.Arm.CheckKey.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := ck_pre s hs
  have it := ck_pre t ht
  sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hp
  have args : ∀ i < 14, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | 12, _ => a12 | 13, _ => a13
    | _ + 14, h => absurd h (by omega)
  rw [code_eq] at e1 e2
  exact (fn_ct (vf := vK) (by decide) (by decide) entry_taint restore_taint (fun σ _ => ck_hv σ)
    (fun _ h => ck_hA h) ck_bodyS_ct s t tr1 tr2 u v ⟨is, it, VG.Proof.Rsa.Arm.CheckCrtKey.pubF_of sp bytes p0 p1 p2 p3 args⟩ e1 e2).1

/-- A 64-byte modulus, one-byte exponents and factors, the working space at
`0x4000`, and the stack arguments at `0x8000`. -/
def ckSatState : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x36 else if a = 0x8004 then 1 else if a = 0x8009 then 0x31
    else if a = 0x800C then 1 else if a = 0x8011 then 0x32 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x33 else if a = 0x801C then 1 else if a = 0x8021 then 0x34
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x35 else if a = 0x802C then 1
    else if a = 0x8031 then 0x40 else if a = 0x8034 then 0x20 else if a = 0x8035 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3600, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩,
    ⟨0x3500, 1⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x4000, 8448⟩]

theorem ck_contract_sat : ∃ s, (Spec.Rsa.checkKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using ckSatState

/-- `vg_rsa_check_key`. -/
theorem check_key_verified :
    Verified target VG.Impl.Rsa.Arm.CheckKey.code (Spec.Rsa.checkKeyContract abi 0) :=
  ⟨ck_contract_correct, ck_contract_ct, ck_contract_sat⟩

end VG.Proof.Rsa.Arm.CheckKey

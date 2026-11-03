module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Correct
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.CT
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Correct
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
meta import VerifiedGarbage.Proof.Scrypt.Whole
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Correct
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.CT

/-!
# scrypt on RISC-V: constant time, up to the indices `j`, and the shared contract

As on PPC64LE (`Proof/Scrypt/PPC64LE/Whole/Verified.lean`): two runs whose
public data agree have the same layout, so in the frame's body they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs), whatever their secrets, and the indices of all the scryptROMix
calls agree (`LeakEq`). The blocks address only the frame, from `s3`, which
`Ctx` fixes (the taint analysis); each call is of constant-time code whose
public data agree (`RelCT.call`); the branch on the pointers' alignment and
the loop's branch agree since both runs have the same pointers and count the
same blocks. The frame leaks nothing (`RelCT.allocFrame`).

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 correct and
constant-time under `pbkK` with at most 992 bytes of stack, is verified
against `Spec.Scrypt.scryptContract` for the 1248 bytes of stack its frame
and calls use (`scrypt_verified_of`); and so is the one calling PBKDF2 made
with SHA-256 (`scrypt_verified`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.Impl.Scrypt.RISCV64.Whole
open VG.Proof.Pbkdf2.Whole.RISCV64 (pbkR)
open VG.Spec.Scrypt (bytesAt roMixIndices)

/-- The indices of every scryptROMix agree in two runs from `m₁` and `m₂`. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN) =
    (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat) L.r.toNat L.pp).flatMap
      (roMixIndices L.r.toNat L.NN)

theorem leak_X {L : Lay} {m₁ m₂ : Mem} (h : LeakEq L m₁ m₂) {k : Nat} (hk : k < L.pp) :
    roMixIndices L.r.toNat L.NN (X L m₁ k) = roMixIndices L.r.toNat L.NN (X L m₂ k) := by
  have h₁ : k < (Spec.Scrypt.blocks (bytesAt m₁ L.pw L.pwl.toNat) (bytesAt m₁ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  have h₂ : k < (Spec.Scrypt.blocks (bytesAt m₂ L.pw L.pwl.toNat) (bytesAt m₂ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
    Option.getD_some]
  exact Whole.indices_eq h h₁ h₂

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  m₁ : Mem
  m₂ : Mem

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ LeakEq e.L e.m₁ e.m₂ ∧ Ctx e.L e.g₁ e.m₁ a ∧ Ctx e.L e.g₂ e.m₂ b ∧
    Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- Two states in the frame's body agree on the stack pointer and `s3`. -/
theorem agree_two {L : Lay} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.s3]) t₁ t₂ :=
  ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
    have : r = .s3 := by simpa using hr
    subst this
    exact c₁.s3.trans c₂.s3.symm⟩

/-- A block whose addresses depend only on `s3`, with what it establishes. -/
theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (taint.check (VG.RISCV64.Taint.ofRegs [.s3]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s3])
    (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂) h) hw

/-- A call of verified code, with the same regions in both runs, after which
`Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ m₁ m₂, L.Ok → LeakEq L m₁ m₂ → Ctx L g₁ m₁ t₁ →
      Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay) m₀ (t : State), L.Ok → Φ L m₀ t → ∀ r ∈ wr L, InBuf L r)
    (hw : ∀ (L : Lay) g m₀ (t : State), L.Ok → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ _ _ hL f₁) (hwsub _ _ _ hL f₁)
    have w₂ := covers c₂ (hsub _ _ _ hL f₂) (hwsub _ _ _ hL f₂)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ hL c₁ f₁, hpre _ _ _ _ hL c₂ f₂,
          hpub _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The calls -/

theorem pbk_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    {t₁ t₂ : State} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) {salt : Addr} {sl : BitVec 64}
    {out : Addr} {ol : BitVec 64} (a₁ : PbkArgs L salt sl out ol t₁) (a₂ : PbkArgs L salt sl out ol t₂) :
    pbkK.pub (t₁.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol))
      (t₂.callEntry.withRegions (pbkRd L salt sl) (pbkWr out ol)) := by
  simp only [pbkK, pbkR, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a6 ∉ linkRegs),
    a₁.a0, a₁.a1, a₁.a2, a₁.a3, a₁.a4, a₁.a5, a₁.a6, a₂.a0, a₂.a1, a₂.a2, a₂.a3, a₂.a4, a₂.a5, a₂.a6,
    c₁.ce_sp, c₂.ce_sp, and_self]

/-- The block ROMix works on in iteration `i`, on entry to it. -/
theorem romix_bytes {L : Lay} {m₀ : Mem} {t : State} {i : Nat} (hi : i < L.pp) (hb : InvB L m₀ i t)
    (rd wr : List Region) :
    bytesAt (t.callEntry.withRegions rd wr).mem (blkAt L i) (128 * L.r.toNat) = X L m₀ i := by
  rw [State.withRegions_mem, State.callEntry_mem, hb.blks i hi]
  simp only [Nat.lt_irrefl, ite_false]

theorem romix_pub_two {L : Lay} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} {t₁ t₂ : State} (hk : LeakEq L m₁ m₂) (c₁ : Ctx L g₁ m₁ t₁)
    (c₂ : Ctx L g₂ m₂ t₂) {i : Nat} (hi : i < L.pp) (b₁ : InvB L m₁ i t₁) (b₂ : InvB L m₂ i t₂)
    (a₁ : RomixArgs L (blkAt L i) t₁) (a₂ : RomixArgs L (blkAt L i) t₂) (wide : Bool) :
    (Proof.Scrypt.roMixRISCV64 wide).pub (t₁.callEntry.withRegions [] (romixWr L i))
      (t₂.callEntry.withRegions [] (romixWr L i)) := by
  simp only [Proof.Scrypt.roMixRISCV64, gpr_ce _ _ _ (by decide : Reg.a0 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a1 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.a4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.a5 ∉ linkRegs), a₁.a0, a₁.a1, a₁.a2, a₁.a3, a₁.a4, a₁.a5, a₂.a0,
    a₂.a1, a₂.a2, a₂.a3, a₂.a4, a₂.a5, c₁.ce_sp, c₂.ce_sp, true_and,
    romix_bytes hi b₁, romix_bytes hi b₂]
  exact leak_X hk hi

/-! ## The loop -/

/-- Iteration `pp - n` of the loop is next. -/
abbrev LoopAt (wide : Bool) (n : Nat) (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t

theorem body_ct (wide : Bool) (n : Nat) :
    RelCT isa (Two (LoopAt wide n)) (.seq (.block romixArgs) (.seq (.call (roMixName wide)
      (Impl.Scrypt.RISCV64.roMix wide)) (.block nextBlock)))
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .t0 != 0) = decide (L.pp - n + 1 ≠ L.pp)) := by
  have a : RelCT isa (Two (LoopAt wide n)) (.block romixArgs) (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧
      n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧ RomixArgs L (blkAt L (L.pp - n)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨hal, h0, hn, hb⟩ =>
      WP.mono (romixArgs_ok hL hc hb.cur) fun _ ⟨hc', hm, ha⟩ =>
        ⟨hc', hal, h0, hn, ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ha⟩
  have b : RelCT isa (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n) t ∧
      RomixArgs L (blkAt L (L.pp - n)) t) (.call (roMixName wide) (Impl.Scrypt.RISCV64.roMix wide))
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t) :=
    two_call RoMix.roMix_correct (RoMix.roMix_ct wide) (fun _ => []) (fun L => romixWr L (L.pp - n))
      (fun _ _ _ _ hL _ ⟨hal, h0, hn, _, ha⟩ => romix_pre hL (by omega) hal ha)
      (fun _ _ _ _ _ _ _ _ hk c₁ c₂ ⟨_, h0, hn, b₁, a₁⟩ ⟨_, _, _, b₂, a₂⟩ =>
        romix_pub_two hk c₁ c₂ (by omega) b₁ b₂ a₁ a₂ wide)
      (fun _ _ _ hL ⟨_, h0, hn, _⟩ => romix_sub hL (by omega))
      (fun _ _ _ hL ⟨_, h0, hn, _⟩ => romix_wsub hL (by omega))
      (fun _ _ _ _ hL hc ⟨hal, h0, hn, hb, ha⟩ =>
        WP.mono (call_step hL (by omega) hc hal hb ha) fun _ ⟨hc', hm⟩ => ⟨hc', hal, h0, hn, hm⟩)
  have c : RelCT isa (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ Mid L m₀ (L.pp - n) t)
      (.block nextBlock)
      (Two fun L m₀ t => Aligned L wide ∧ 0 < n ∧ n ≤ L.pp ∧ InvB L m₀ (L.pp - n + 1) t ∧
        (t.gpr .t0 != 0) = decide (L.pp - n + 1 ≠ L.pp)) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc ⟨hal, h0, hn, hm⟩ =>
      WP.mono (next_step hL (by omega) hc hm) fun _ ⟨hc', hb, hz⟩ => ⟨hc', hal, h0, hn, hb, hz⟩
  exact a.seq (b.seq c)

theorem loop_ct (wide : Bool) :
    RelCT isa (Two fun L m₀ t => Aligned L wide ∧ InvB L m₀ 0 t) (romixLoop wide)
      (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have ev : ∀ x : State, isa.eval (.nonzero .t0) x = some (x.gpr .t0 != 0) := fun x =>
    eval_nonzero x .t0
  have h := fun n => RelCT.loop (M := isa) (c := .nonzero .t0)
    (Q := Two fun L m₀ t => InvB L m₀ L.pp t)
    (fun n => Two (LoopAt wide n)) (fun n => (body_ct wide n).mono (fun _ _ h => h) fun a b hab => by
      obtain ⟨e, hL, hk, c₁, c₂, ⟨hal, h0, hn, b₁, z₁⟩, ⟨hal₂, -, -, b₂, z₂⟩⟩ := hab
      rw [ev, ev, z₁, z₂]
      refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
      · have hl : e.L.pp - n + 1 = e.L.pp := by simpa using hf
        exact ⟨e, hL, hk, c₁, c₂, show InvB e.L _ e.L.pp a from hl ▸ b₁,
          show InvB e.L _ e.L.pp b from hl ▸ b₂⟩
      · have hl : e.L.pp - n + 1 ≠ e.L.pp := by simpa using ht
        have e₁ : e.L.pp - (n - 1) = e.L.pp - n + 1 := by omega
        exact ⟨n - 1, by omega, e, hL, hk, c₁, c₂, ⟨hal, by omega, by omega, e₁ ▸ b₁⟩,
          ⟨hal₂, by omega, by omega, e₁ ▸ b₂⟩⟩) n
  refine (RelCT.exists_ h).mono (fun a b ⟨e, hL, hk, c₁, c₂, ⟨hal₁, b₁⟩, ⟨hal₂, b₂⟩⟩ => ⟨e.L.pp, e, hL, hk,
    c₁, c₂, ⟨hal₁, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₁⟩,
    ⟨hal₂, hL.pp_pos, Nat.le_refl _, by rw [Nat.sub_self]; exact b₂⟩⟩) fun _ _ h => h

theorem all_ct :
    RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) romixAll (Two fun L m₀ t => InvB L m₀ L.pp t) := by
  have a : RelCT isa (Two fun L m₀ t => InvB L m₀ 0 t) (.block alignBits)
      (Two fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hb =>
      WP.mono (alignBits_ok hL hc) fun _ ⟨hc', hm, ht⟩ =>
        ⟨hc', ⟨by rw [hm]; exact hb.cur, by rw [hm]; exact hb.blks⟩, ht⟩
  have ev : ∀ (L : Lay) (x : State), x.gpr .t0 = alBits L →
      isa.eval (.zero .t0) x = some (decide (L.b.toNat % 8 = 0 ∧ L.v.toNat % 8 = 0 ∧ L.scr.toNat % 8 = 0)) :=
    fun L x hx => by rw [eval_zero, hx, al3]
  have ht : RelCT isa (fun s₁ s₂ => Two (fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) s₁ s₂ ∧
      isa.eval (.zero .t0) s₁ = some true) (romixLoop true) (Two fun L m₀ t => InvB L m₀ L.pp t) := by
    refine (loop_ct true).mono (fun _ _ h => ?_) fun _ _ h => h
    obtain ⟨⟨e, hL, hk, c₁, c₂, ⟨b₁, h₁⟩, ⟨b₂, _⟩⟩, hz⟩ := h
    rw [ev _ _ h₁, Option.some.injEq] at hz
    have hal := of_decide_eq_true hz
    exact ⟨e, hL, hk, c₁, c₂, ⟨fun _ => hal, b₁⟩, ⟨fun _ => hal, b₂⟩⟩
  have he : RelCT isa (fun s₁ s₂ => Two (fun L m₀ t => InvB L m₀ 0 t ∧ t.gpr .t0 = alBits L) s₁ s₂ ∧
      isa.eval (.zero .t0) s₁ = some false) (romixLoop false) (Two fun L m₀ t => InvB L m₀ L.pp t) := by
    refine (loop_ct false).mono (fun _ _ h => ?_) fun _ _ h => h
    obtain ⟨⟨e, hL, hk, c₁, c₂, ⟨b₁, _⟩, ⟨b₂, _⟩⟩, _⟩ := h
    exact ⟨e, hL, hk, c₁, c₂, ⟨fun h => Bool.noConfusion h, b₁⟩, ⟨fun h => Bool.noConfusion h, b₂⟩⟩
  refine a.seq (RelCT.ite (fun _ _ h => ?_) ht he)
  obtain ⟨e, _, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ := h
  rw [ev _ _ h₁, ev _ _ h₂]

/-! ## The whole function -/

/-- Two calls whose public data agree, in the frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, scryptRV.pre s₁ ∧ scryptRV.pre s₂ ∧ scryptRV.pub s₁ s₂ ∧
    a = allocd locals s₁ ∧ b = allocd locals s₂

theorem save_ct : RelCT isa Entered (.block setup) (Two fun L _ t => Entry L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp, hlk⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (VG.RISCV64.Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show s₁.sp - _ = s₂.sp - _; rw [hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay s₂ = lay s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, hsp]
  refine ⟨ht, ⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok h₁, ?_, y₁.1, e ▸ y₂.1, y₁.2,
    e ▸ y₂.2⟩
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h6, ← a0] at hlk
  exact hlk

/-- The state a frame's body starts in. -/
theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocd n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do: reserving it accesses no memory. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs]

section
variable {pbk : Prog isa} (hv : PbkOk pbk) (hct : ConstantTime isa pbkK.pre pbkK.pub pbk)
  (hd : sdepth pbk ≤ 992) (name : String)
include hv hct hd

theorem rest_ct : RelCT isa (Two fun L _ t => Entry L t)
    (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixAll
      (.seq (pbkCall name pbk pbk2Args) (.block Impl.Scrypt.RISCV64.Whole.restore)))))
    fun _ _ => True := by
  have p1a : RelCT isa (Two fun L _ t => Entry L t) (.block pbk1Args)
      (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :=
    two_blk (by taint_decide) fun _ _ _ _ _ hc he =>
      WP.mono (pbk1Args_ok hc he) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p1c : RelCT isa (Two fun L _ t => PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t)
      (.call name pbk)
      (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :=
    two_call hv hct (fun L => pbkRd L L.salt L.sl)
      (fun L => pbkWr L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk1_regions hL))
      (fun _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub (pbk1_regions hL)) (fun _ _ _ hL _ => pbk_wsub (pbk1_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk1_call_ok hv hd name hL hc ha) fun _ ⟨hc', _, hx⟩ => ⟨hc', hx⟩)
  have c0 : RelCT isa (Two fun L m₀ t => ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k)
      (.block cur0) (Two fun L m₀ t => InvB L m₀ 0 t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc hx => (start_ok hL hc hx).mono fun _ h => h
  have p2a : RelCT isa (Two fun L m₀ t => InvB L m₀ L.pp t) (.block pbk2Args)
      (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t) :=
    two_blk (by taint_decide) fun _ _ _ _ hL hc _ =>
      WP.mono (pbk2Args_ok hL hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have p2c : RelCT isa (Two fun L _ t => PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t)
      (.call name pbk) (Two fun _ _ _ => True) :=
    two_call hv hct (fun L => pbkRd L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)))
      (fun L => pbkWr L.out L.ol)
      (fun _ _ _ _ hL hc ha => pbk_pre' hL hc ha (pbk2_regions hL))
      (fun _ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => pbk_pub_two c₁ c₂ a₁ a₂)
      (fun _ _ _ hL _ => pbk_sub (pbk2_regions hL)) (fun _ _ _ hL _ => pbk_wsub (pbk2_regions hL))
      (fun _ _ _ _ hL hc ha =>
        WP.mono (pbk_call hv hd name hL hc ha (pbk2_regions hL)) fun _ h => ⟨h.1, trivial⟩)
  have rs : RelCT isa (Two fun _ _ _ => True) (.block Impl.Scrypt.RISCV64.Whole.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s3])
      (fun _ _ ⟨_, _, _, c₁, c₂, _, _⟩ => agree_two c₁ c₂) (by taint_decide)
  exact (p1a.seq p1c).seq (c0.seq (all_ct.seq ((p2a.seq p2c).seq rs)))

theorem scrypt_ct : ConstantTime isa scryptRV.pre scryptRV.pub (scrypt name pbk) := by
  refine RelCT.constantTime (RelCT.allocFrame ?_)
  refine (save_ct.seq (rest_ct hv hct hd name)).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, pa, pb⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, alloc_eq pa, alloc_eq pb⟩

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified RISCV64.target (scrypt name pbk) (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hd name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hct hd name) scrypt_implies

end

/-! ## With PBKDF2 made with SHA-256 -/

/-- PBKDF2-HMAC-SHA256's code. -/
abbrev pbkCode : Prog isa := Proof.Pbkdf2.Whole.RISCV64.Sha256.F.pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name

theorem pbk_ok : PbkOk pbkCode := fun _ hs =>
  Proof.Pbkdf2.Whole.RISCV64.correct Proof.Pbkdf2.Whole.RISCV64.Sha256.okF hs

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbkCode :=
  Proof.Pbkdf2.Whole.RISCV64.ct Proof.Pbkdf2.Whole.RISCV64.Sha256.okF
    Proof.Pbkdf2.Whole.RISCV64.Sha256.checks

theorem sdepth_noFrames : ∀ c : Prog isa, c.noFrames = true → sdepth c = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames a h.1, sdepth_noFrames b h.2, Nat.max_self]
  | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames a h.1, sdepth_noFrames b h.2, Nat.max_self]
  | .loop b _, h => sdepth_noFrames b h
  | .call _ b, h => sdepth_noFrames b h
  | .frame .., h => by cases h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [sdepth, sdepth_noFrames b h.1, sdepth_noFrames n h.2, Nat.max_self]

theorem pbk_sdepth : sdepth pbkCode ≤ 992 := by
  have h1 := Proof.Pbkdf2.Whole.RISCV64.hi_sdepth Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH
  have h2 := Proof.Pbkdf2.Whole.RISCV64.hf_sdepth Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH
  have h3 := Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.hH.updSd
  have h4 := sdepth_noFrames _ Proof.Pbkdf2.Whole.RISCV64.Sha256.okF.itNf
  have h5 : Proof.Pbkdf2.Whole.RISCV64.Sha256.F.itB + Proof.Pbkdf2.Whole.RISCV64.Sha256.F.frB +
      Proof.Pbkdf2.Whole.RISCV64.Sha256.F.X = 992 := by decide
  simp only [Impl.Pbkdf2.Whole.RISCV64.Fns.X] at h5
  simp only [pbkCode, Impl.Pbkdf2.Whole.RISCV64.Fns.pbkdf2, Impl.Pbkdf2.Whole.RISCV64.Fns.main,
    Impl.Pbkdf2.Whole.RISCV64.Fns.callHi, Impl.Pbkdf2.Whole.RISCV64.Fns.callHf,
    Impl.Pbkdf2.Whole.RISCV64.Fns.callIt, Impl.Pbkdf2.Whole.RISCV64.Fns.block,
    Impl.Pbkdf2.Whole.RISCV64.Fns.outLen, Impl.Pbkdf2.Whole.RISCV64.Fns.outLoop,
    Impl.Hmac.Stream.RISCV64.Hash.callUpd, sdepth, Instr.frameBytes, h4]
  omega

/-- `vg_scrypt` calling `vg_pbkdf2_hmac_sha256`. -/
theorem scrypt_verified :
    Verified RISCV64.target (scrypt pbkName pbkCode) (Spec.Scrypt.scryptContract RISCV64.abi stackBytes) :=
  scrypt_verified_of pbk_ok pbk_ct pbk_sdepth pbkName

end VG.Proof.Scrypt.RISCV64.Whole

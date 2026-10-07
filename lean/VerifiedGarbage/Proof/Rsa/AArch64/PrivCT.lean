import VerifiedGarbage.Proof.Rsa.AArch64.PrivCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# `vg_rsa_private_checked` on AArch64: constant time

Two runs whose public data agree (the pointers and lengths, `n` and `e`)
have the same layout, so between the frames' pushes and pops they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the
next piece needs), whatever their secrets. The blocks are checked by the
taint analysis, from the registers `Φ` fixes as functions of the layout;
each call is of constant-time code whose public data agree (`RelCT.call`):
`n` and `e`, and `n`'s values, which are a function of `n`. The frames leak
only `sp`.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The public data of the two runs' memories agree. -/
def PubEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
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

/-- Two runs with the same layout, each satisfying `Ctx` and `Φ`. -/
def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ ArgsAt e.L e.m₁ ∧ ArgsAt e.L e.m₂ ∧ PubEq e.L e.m₁ e.m₂ ∧
    Ctx e.L e.g₁ e.v₁ e.m₁ a ∧ Ctx e.L e.g₂ e.v₂ e.m₂ b ∧ Φ e.L e.m₁ a ∧ Φ e.L e.m₂ b

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, a₁, a₂, hk, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL a₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL a₂ c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, a₁, a₂, hk, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- A block whose addresses and branches depend only on `sp` and the
registers `rs`, which `Φ` fixes as functions `f` of the layout. -/
theorem two_blk {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop} (rs : List Reg)
    (f : Lay → Reg → BitVec 64) (hf : ∀ L m t, Φ L m t → ∀ r ∈ rs, t.gpr r = f L r)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) :=
  two_wp (RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
      rw [Taint.mem_ofRegs] at hr
      rw [hf _ _ _ f₁ r hr, hf _ _ _ f₂ r hr]⟩) h) hw

/-- A call of verified code, with the same regions in both runs, after
which `Ψ` holds. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ (L : Lay) t₁ t₂ g₁ g₂ v₁ v₂ m₁ m₂, L.Ok → PubEq L m₁ m₂ → Ctx L g₁ v₁ m₁ t₁ →
      Ctx L g₂ v₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (hsub : ∀ (L : Lay), L.Ok → ∀ r ∈ rd L ++ wr L, ∃ R ∈ L.regions, Within r R)
    (hwsub : ∀ (L : Lay), L.Ok → ∀ r ∈ wr L, InW L r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → ArgsAt L m₀ → Ctx L g vv m₀ t → Φ L m₀ t →
      WP isa (.call n c) t fun t' => Ctx L g vv m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.call n c) (Two Ψ) :=
  two_wp (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => by
    obtain ⟨e, hL, a₁, a₂, hk, c₁, c₂, f₁, f₂⟩ := hp
    have w₁ := covers c₁ (hsub _ hL) (hwsub _ hL)
    have w₂ := covers c₂ (hsub _ hL) (hwsub _ hL)
    exact RelCT.call (n := n) hv hct (P := fun a b => a = s₁ ∧ b = s₂) (rd e.L) (wr e.L)
      (fun _ _ ⟨h₁, h₂⟩ => by
        subst h₁ h₂
        exact ⟨hpre _ _ _ _ _ hL a₁ c₁ f₁, hpre _ _ _ _ _ hL a₂ c₂ f₂,
          hpub _ _ _ _ _ _ _ _ _ hL hk c₁ c₂ f₁ f₂, w₁.1, w₁.2, w₂.1, w₂.2⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂) hw

/-! ## The tail -/

/-- After the comparison's set-up. -/
abbrev PhiB (L : Lay) (_ : Mem) (t : State) : Prop :=
  Slots L t.mem ∧ t.gpr .x11 = L.out ∧ t.gpr .x12 = L.inp ∧ t.gpr .x13 = L.k ∧ t.gpr .x14 = 0 ∧
    (t.gpr .x9 = 0 ∨ t.gpr .x9 = 1)

/-- After the comparison. -/
abbrev PhiC (L : Lay) (_ : Mem) (t : State) : Prop := Slots L t.mem ∧ (t.gpr .x9 = 0 ∨ t.gpr .x9 = 1)

/-- After the masks. -/
abbrev PhiD (L : Lay) (_ : Mem) (t : State) : Prop :=
  t.gpr .x11 = L.out ∧ t.gpr .x14 = L.B + BitVec.ofNat 64 oM ∧ t.gpr .x15 = L.k

/-- The registers `PhiB`, `PhiD` fix. -/
def fixB (L : Lay) : Reg → BitVec 64
  | .x11 => L.out | .x12 => L.inp | .x13 => L.k | _ => 0

def fixD (L : Lay) : Reg → BitVec 64
  | .x11 => L.out | .x14 => L.B + BitVec.ofNat 64 oM | .x15 => L.k | _ => 0

theorem cmpArgs_ct : RelCT isa (Two fun L _ t => Slots L t.mem) (.block cmpArgs) (Two PhiB) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ t hL _ hc hs => WP.mono (cmpArgs_ok hL hc hs rfl rfl)
      fun t' ⟨hm, hk, x9, x11, x12, x13, x14⟩ =>
        ⟨hc.keep hk hm, by rw [hm]; exact hs, x11, x12, x13, x14, x9 ▸ Proof.Rsa.gOf_cases _ _ _⟩

theorem cmpLoop_ct : RelCT isa (Two PhiB) cmpLoop (Two PhiC) := by
  refine two_blk [.x11, .x12, .x13] fixB (fun L _ t ⟨_, x11, x12, x13, _⟩ r hr => ?_) (by taint_decide)
    fun L _ _ _ t hL _ hc ⟨hs, x11, x12, x13, x14, x9⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [fixB] <;> with_reducible assumption
  · have hk := hL.khi
    have hk1 : 1 ≤ L.k.toNat := by have := hL.klo; omega
    have hok : L.out.toNat + L.k.toNat ≤ 2 ^ 64 := hL.olk ▸ hL.bo
    have hik : L.inp.toNat + L.k.toNat ≤ 2 ^ 64 := hL.ilk ▸ hL.bi
    have hOk : L.OUT = ⟨L.out, L.k.toNat⟩ := by rw [Lay.OUT, hL.olk]
    refine WP.mono (cmpLoop_ok (op := L.out) (ip := L.inp) hk1 (by omega) x11 x12
      (by rw [x13, BitVec.ofNat_toNat, BitVec.setWidth_eq]) x14
      (fun i hi => ⟨L.OUT, by rw [hc.rd, hc.wr]; simp, hOk ▸ contains_of_lt _ (by omega) hi⟩)
      (fun i hi => ⟨L.IN, by rw [hc.rd, hc.wr]; simp, by rw [Lay.IN, hL.ilk]; exact contains_of_lt _ (by omega) hi⟩))
      fun t' hI => ⟨hc.keep (hI.keep.mono (by decide)) hI.mem, by rw [hI.mem]; exact hs, ?_⟩
    rw [hI.keep.gpr _ (by decide)]; exact x9

theorem masks_ct : RelCT isa (Two PhiC) (.block masks) (Two PhiD) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ t hL _ hc ⟨hs, x9⟩ => WP.mono (masks_ok (eq := decide (t.gpr .x14 = 0)) hL hc hs rfl x9
      (by simp)) fun t' ⟨hm, hk, _, _, _, x11, x14, x15⟩ => ⟨hc.keep hk hm, x11, x14, x15⟩

theorem release_ct :
    RelCT isa (Two PhiD) (.seq releaseLoop (.block [.addImm .x .x0 .x13 0])) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x11, .x14, .x15])
    (fun _ _ ⟨_, _, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨c₁.sp.trans c₂.sp.symm, fun r hr => by
      rw [Taint.mem_ofRegs] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [f₁.1, f₂.1]
      · rw [f₁.2.1, f₂.2.1]
      · rw [f₁.2.2, f₂.2.2]⟩) (by taint_decide)

theorem tail_ct : RelCT isa (Two fun L _ t => Slots L t.mem) (seqs tail) fun _ _ => True := by
  rw [tail_eq]
  exact cmpArgs_ct.seq (cmpLoop_ct.seq (masks_ct.seq release_ct))

/-! ## The calls -/

theorem ce_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (8 * i)) 64 := rfl

theorem crt_ct (v : CrtImpl) :
    RelCT isa (Two fun L _ t => Slots L t.mem ∧ CrtArgs L t) (.call v.name v.code)
      (Two fun L _ t => Slots L t.mem) :=
  two_call v.crt_ok v.crt_ct crtRd crtWr (fun _ _ _ _ _ hL _ hc ⟨_, ha⟩ => crtCall_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨_, a₁⟩ ⟨_, a₂⟩ => by
      have st : ∀ i < 10, stackArg (t₁.callEntry.withRegions (crtRd L) (crtWr L)) i =
          stackArg (t₂.callEntry.withRegions (crtRd L) (crtWr L)) i := fun i hi => by
        rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, a₁.stk i hi, a₂.stk i hi]
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_, ?_⟩
      · have hl : r ∉ linkRegs := by
          simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [gpr_ce _ _ _ hl, gpr_ce _ _ _ hl]
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm, a₁.x6.trans a₂.x6.symm,
          a₁.x7.trans a₂.x7.symm]
      · simp only [stackArgs_ten, st 0 (by omega), st 1 (by omega), st 2 (by omega), st 3 (by omega),
          st 4 (by omega), st 5 (by omega), st 6 (by omega), st 7 (by omega), st 8 (by omega),
          st 9 (by omega)]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, c₁.n_bytes hL, c₂.n_bytes hL]
        exact hk.1)
    (fun _ hL => crt_sub hL) (fun _ hL => crt_wsub hL)
    (fun _ _ _ _ _ hL _ hc ⟨hs, ha⟩ => WP.mono (crt_call v hL hc hs ha) fun _ ⟨hc', hs', _⟩ => ⟨hc', hs'⟩)

/-- `n`'s values, as `vg_rsa_public_precompute` writes them for `n`. -/
def preVal (L : Lay) (nB : List Byte) : List (BitVec 64) :=
  match Spec.Rsa.publicPrecompute nB with
  | some ws => ws
  | none => List.replicate L.pw 0

/-- `n`'s values are in the inner frame. -/
abbrev PreW (L : Lay) (m₀ : Mem) (t : State) : Prop :=
  Spec.Rsa.wordsAt t.mem (L.B + BitVec.ofNat 64 oPre) L.pw = preVal L (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)

theorem pcArgs_ct : RelCT isa (Two fun L _ t => Slots L t.mem) (.block pcArgs)
    (Two fun L _ t => Slots L t.mem ∧ PcArgs L t) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun _ _ _ _ _ hL ha hc hs => WP.mono (pcArgs_ok hL ha hc hs) fun _ ⟨hc', hs', pa, _⟩ => ⟨hc', hs', pa⟩

theorem pc_ct (v : CrtImpl) :
    RelCT isa (Two fun L _ t => Slots L t.mem ∧ PcArgs L t) (.call v.pcName v.pc)
      (Two fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) :=
  two_call v.pc_ok v.pc_ct pcRd pcWr (fun _ _ _ _ _ hL _ hc ⟨_, ha⟩ => pcCall_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨_, a₁⟩ ⟨_, a₂⟩ => by
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [gpr_ce _ _ _ (by decide), gpr_ce _ _ _ (by decide)]
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, c₁.n_bytes hL, c₂.n_bytes hL]
        exact hk.1)
    (fun _ hL => pc_sub hL) (fun _ hL => pc_wsub hL)
    (fun _ _ _ _ _ hL _ hc ⟨hs, ha⟩ => WP.mono (pc_call v hL hc hs ha) fun _ ⟨hc', hs', _, hpc⟩ => by
      refine ⟨hc', hs', ?_⟩
      simp only [PcOut, hc.n_bytes hL] at hpc
      simp only [PreW, preVal]
      split <;> rename_i h <;> simp only [h] at hpc <;> exact hpc.2)

theorem pdArgs_ct : RelCT isa (Two fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) (.block pdArgs)
    (Two fun L m₀ t => Slots L t.mem ∧ PdArgs L t ∧ PreW L m₀ t) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun L _ _ _ _ hL ha hc ⟨hs, hp⟩ => WP.mono (pdArgs_ok hL ha hc hs) fun _ ⟨hc', hs', pda, _, f₃⟩ => by
      refine ⟨hc', hs', pda, ?_⟩
      have hnB := hL.nB
      have hk := hL.khi
      have d3 := slot_disj hL (d := oR3) (by decide)
      have hP16 : L.PRE.Disjoint ⟨L.B, 16⟩ :=
        Offset.disjoint_base _ (by decide) (by simp only [oPre, Lay.pw]; omega)
      rw [PreW, frame_wordsAt f₃ (fun r hr => ?_) (by unfold Lay.pw; omega)]
      · exact hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (by rw [Nat.mul_comm]; exact d3.1.symm)
        · exact (by rw [Nat.mul_comm]; exact hP16)

theorem pd_ct (v : CrtImpl) :
    RelCT isa (Two fun L m₀ t => Slots L t.mem ∧ PdArgs L t ∧ PreW L m₀ t) (.call v.pdName v.pd)
      (Two fun L _ t => Slots L t.mem) :=
  two_call v.pd_ok v.pd_ct pdRd pdWr (fun _ _ _ _ _ hL _ hc ⟨_, ha, _⟩ => pdCall_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ m₁ m₂ hL hk c₁ c₂ ⟨_, a₁, p₁⟩ ⟨_, a₂, p₂⟩ => by
      refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, c₁.sp, c₂.sp], ?_, ?_,
        ?_, ?_⟩
      · have hl : r ∉ linkRegs := by
          simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [gpr_ce _ _ _ hl, gpr_ce _ _ _ hl]
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a₁.x0.trans a₂.x0.symm, a₁.x1.trans a₂.x1.symm, a₁.x2.trans a₂.x2.symm,
          a₁.x3.trans a₂.x3.symm, a₁.x4.trans a₂.x4.symm, a₁.x5.trans a₂.x5.symm, a₁.x6.trans a₂.x6.symm,
          a₁.x7.trans a₂.x7.symm]
      · rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, Nat.mul_zero, BitVec.add_zero, a₁.s0, a₂.s0]
      · rw [ce_stackArg, ce_stackArg, c₁.sp, c₂.sp, a₁.s1, a₂.s1]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
          a₁.x2, a₁.x3, a₂.x2, a₂.x3, toNat_pw hL]
        rw [p₁, p₂, hk.1]
      · simp only [State.withRegions_mem, State.callEntry_mem,
          gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
          a₁.x4, a₁.x5, a₂.x4, a₂.x5, c₁.e_bytes hL, c₂.e_bytes hL]
        exact hk.2)
    (fun _ hL => pd_sub hL) (fun _ hL => pd_wsub hL)
    (fun _ _ _ _ _ hL _ hc ⟨hs, ha, _⟩ => WP.mono (pd_call v hL hc hs ha) fun _ ⟨hc', hs', _⟩ => ⟨hc', hs'⟩)

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (a b : State) : Prop :=
  ∃ s₁ s₂, chkA.pre s₁ ∧ chkA.pre s₂ ∧ chkA.pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem lay_eq {s₁ s₂ : State} (hp : chkA.pub s₁ s₂) : lay s₂ = lay s₁ := by
  obtain ⟨hr, hsp, ha, -⟩ := hp
  simp only [stackArgs_twelve, List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ha
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  simp only [lay, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hsp]

theorem crtArgs_ct : RelCT isa Entered (.block crtArgs) (Two fun L _ t => Slots L t.mem ∧ CrtArgs L t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  have e := lay_eq hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp, entered_sp, e]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := crtArgs_ok (lay_ok h₁) (argsAt_entry s₁) (entered_ctx h₁)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨_, u₂, x₂, y₂⟩ := crtArgs_ok (lay_ok h₂) (argsAt_entry s₂) (entered_ctx h₂)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  refine ⟨ht, ⟨lay s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, argsAt_entry s₁,
    e ▸ argsAt_entry s₂, ?_, y₁.1, e ▸ y₂.1, y₁.2, e ▸ y₂.2⟩
  obtain ⟨hr, -, -, hn, he⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨-, -, r2, r3, r4, r5, -, -⟩ := hr
  refine ⟨?_, ?_⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    exact hn.trans (by rw [← r2, ← r3])
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    exact he.trans (by rw [← r4, ← r5])

theorem code_constantTime (v : CrtImpl) : ConstantTime isa chkA.pre chkA.pub (privCodeOf v) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.2.1)
    (RelCT.alloc (R := fun _ _ => True) ?_))
  show RelCT isa _ (body _ _ _ _ _ _) _
  rw [body_eq, check_eq]
  refine (crtArgs_ct.seq ((crt_ct v).seq (pcArgs_ct.seq ((pc_ct v).seq (pdArgs_ct.seq
    ((pd_ct v).seq tail_ct)))))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.Rsa.AArch64

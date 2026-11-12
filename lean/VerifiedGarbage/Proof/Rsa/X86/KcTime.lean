module

public import VerifiedGarbage.Proof.Rsa.X86.KcTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.KcWordChecks
public import VerifiedGarbage.Proof.Rsa.X86.KcResult
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KcLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KcSized
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Slots
public import VerifiedGarbage.TCB.X86.Isa

/-! # The traces of the checks of an RSA key on i686

The runs are related piece by piece: what the taint analysis checks with
the arguments, `edi` and `esp` public (`τV`), from states that keep them
(`Run`), and the loops counted in the header by `WordRt`'s relations. Up to
the guard, each run's values are known (`Stg`); the guard, of the arguments
and `n`'s top word, is the same in both runs when their `n` is; after it,
each piece keeps only the frame (`Fm`).
-/

/-! ## Once the modulus and exponent are accepted

The width is read from the arguments on the stack, so the taint analysis
takes them public with `edi` and `esp` (`τV`, `sizedCheck`), from states whose
permissions are narrowed to the working space, apart from the arguments
(`ArgsOk`); runs of `sized` from the states themselves leak the same traces
(`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top top_iff val32_low sub0_beq exec_seqs_append RelCT.seqs_append RelCT.seqs_cons RelCT.seqs_all relLift)

/-! ## Runs -/

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (full : Bool) (s : State) : Prop :=
  (s.gpr .esp).toNat + argSpan full ≤ 2 ^ 32 ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan full⟩ r

theorem τV_wf {full : Bool} {s : State} (A : ArgsOk full s) : VG.X86.Taint.Wf (τV full) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeV {g : CallGeometry} {s₁ s₂ : State} (h₁ : Inputs g s₁) (h₂ : Inputs g s₂)
    (A₁ : ArgsOk g.full s₁) (A₂ : ArgsOk g.full s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) :
    VG.X86.Taint.Agree (τV g.full) s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τV_wf A₁, τV_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τV, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.ws.workspace.edi_toNat.trans h₂.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τV, argSpan] at hk
    rw [show VG.X86.Taint.depth (τV g.full).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.arguments _ (by omega)).value.trans (h₂.arguments _ (by omega)).value.symm)

/-- What a narrowed run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ ArgsOk g.full s ∧ s.gpr .esp = sp

/-- A run through a frame of the working space. -/
theorem Run.frame {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Run g sp u) {rs : List Reg}
    (K : Keeps rs u t) (di : .edi ∉ rs) (spn : .esp ∉ rs) (O : Outside g.base 0 g.size u.mem t.mem) :
    Run g sp t :=
  ⟨h.1.after K di spn (h.1.scratchFrame O), ⟨by rw [K.1 _ spn]; exact h.2.1.1, by rw [K.2.2, K.1 _ spn]; exact h.2.1.2⟩,
    (K.1 _ spn).trans h.2.2⟩

theorem Run.agree {g : CallGeometry} {sp : BitVec 32} {t₁ t₂ : State} (h₁ : Run g sp t₁) (h₂ : Run g sp t₂) :
    VG.X86.Taint.Agree (τV g.full) t₁ t₂ :=
  agreeV h₁.1 h₂.1 h₁.2.1 h₂.2.1 (h₁.2.2.trans h₂.2.2.symm)

/-! ## The frame -/

/-- The frame of the checks, from the state `u` they start from: `Stg` without the values. -/
structure Fm (G : Geo) (u t : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr
  keep : Keep G.B G.w (List.range nArr) bodySlots u.mem t.mem
  rest : Keeps bodyRegs u t
  mask : slot t.mem G.B sMask ≤ 1

theorem Stg.fm {G : Geo} {u t : State} {A : Nat → Nat} {live : List Nat} {c : Bool} (h : Stg G u A live c t) :
    Fm G u t := ⟨h.ws, h.keep, h.rest, bit_le h.mask⟩

theorem Fm.next {G : Geo} {u s t : State} (h : Fm G u s) {js ds : List Nat} {rs : List Reg}
    (hw : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr)
    (k : Keep G.B G.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, d ∈ bodySlots)
    (r : Keeps rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) (mk : slot t.mem G.B sMask ≤ 1) : Fm G u t :=
  ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds), h.rest.trans (r.mono hrs), mk⟩

theorem Fm.mask_keep {G : Geo} {u s : State} (h : Fm G u s) {js ds : List Nat} {m' : Mem}
    (k : Keep G.B G.w js ds s.mem m') (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) :
    slot m' G.B sMask ≤ 1 := by
  rw [k.slot (by decide) hd]; exact h.mask

/-- A run's frame from its start. -/
theorem Fm.run {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Fm (geometry g) u t) (r : Run g sp u) :
    Run g sp t :=
  r.frame h.rest (by decide) (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws h.keep (fun j hj => List.mem_range.mp hj) (by decide))

/-! ## The frame through the pieces of the word steps -/

theorem fm_ltA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr) :
    WP isa (seqs (ltA G.full a b)) t (Fm G u) := by
  rw [ltA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) ha hb)
    fun t1 ⟨h1, k1, _, b1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by simp) r1 subRegs_body (h.mask_keep k1 (by simp))
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h1 (d := sF) (by decide) .ebx) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have f2 := f1.next h2 k2 (by simp) (by decide) r2 (by simp) (f1.mask_keep k2 (by decide))
  show WP isa (.block acc) t2 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h2 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f2.mask (by rw [e2]; exact b1)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f2.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_eqA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr)
    (haW : aW ≠ a) (hbW : aW ≠ b) :
    WP isa (seqs (eqA G.full a b)) t (Fm G u) := by
  rw [eqA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqS_ok h.ws (d := sF) (a := a) (b := b) (t := aW) (by decide) ha hb haW hbW
    (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by decide) r1 opRegs_body (h.mask_keep k1 (by decide))
  show WP isa (.block acc) t1 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h1 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f1.mask (by rw [e1]; split <;> decide)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f1.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_mulShort {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (hw2 : 2 ≤ G.w) (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulShort_ok h.ws hw2 ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem fm_wordMod {G : Geo} {u t : State} (h : Fm G u t) {x r m a : Nat} {top : Option Nat}
    (hm : MLen t G.B G.Z (pLenArg G.full) a) (h4 : 4 ≤ wq a) (hw : wq a ≤ G.w)
    (htop : ∀ k, top = some k → wq a + k ≤ G.w)
    (hx : x < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x) :
    WP isa (wordMod G.full x r m top) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.ws hm hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm
    h4 hw htop) fun _ ⟨h1, k1, _, _, _, r1⟩ =>
    h.next h1 k1 (by
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact hmN
      · exact hr
      · decide) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

/-! ## The word steps' relation -/

/-- A run in the word steps: from its start `u`, with `p`'s length `a` that the guard admits. -/
def WIn (g : CallGeometry) (sp : BitVec 32) (a : Nat) (u t : State) : Prop :=
  Run g sp u ∧ Fm (geometry g) u t ∧ MLen u g.base g.size (pLenArg g.full) a ∧ 4 ≤ wq a ∧
    wq a + 2 ≤ (geometry g).w

/-- Both runs in the word steps. -/
def WR (g : CallGeometry) (sp : BitVec 32) (a : Nat) (t₁ t₂ : State) : Prop :=
  ∃ u₁ u₂, True ∧ WIn g sp a u₁ t₁ ∧ WIn g sp a u₂ t₂

theorem WIn.run {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) : Run g sp t :=
  h.2.1.run h.1

theorem WIn.mlen {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) :
    MLen t g.base g.size (pLenArg g.full) a :=
  h.2.2.1.keep h.2.1.rest (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.2.1.ws.ws h.2.1.keep (fun j hj => List.mem_range.mp hj) (by decide))

theorem τV_regs (full : Bool) : ∀ r ∈ [Reg.edi, .esp], (τV full).regs.mem r = true := by
  intro r hr
  change r ∈ RegSet.ofList [Reg.edi, .esp]
  simpa only [RegSet.mem_ofList] using hr

/-- A piece the taint analysis checks. -/
theorem wTaint {g : CallGeometry} {sp : BitVec 32} {a : Nat} {c : Prog isa}
    (hc : ∃ hint, (VG.Taint.check sseTaint (τV g.full) c hint).isSome = true)
    (hf : ∀ u t, Fm (geometry g) u t → WP isa c t (Fm (geometry g) u)) :
    RelCT isa (WR g sp a) c (WR g sp a) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun _ _ => True) (P := WIn g sp a)
    (VG.RelCT.taint (A := sseTaint) (τV g.full) (fun t₁ t₂ ⟨_, _, _, h₁, h₂⟩ => h₁.run.agree h₂.run) hc)
    fun u t h => WP.mono (hf u t h.2.1) fun t' f => ⟨h.1, f, h.2.2⟩

theorem wMulShort {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : RowsCk g.full o x b (some 2))
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulShort (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulShort h.2.1 (by have := h.2.2.2.2; omega) ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  have w2 : ∀ {u t : State}, WIn g sp a u t → 2 ≤ VG.Proof.Rsa.X86.KeyRt.kw (g.args 1).toNat := fun h => by
    have := h.2.2.2.2; have := h.2.2.2.1; simp only [geometry, Geo.w] at *; omega
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (rows := some 2) (by show 1 ≤ 2; decide) (by show 2 ≤ _; exact w2 h₁) (fun k hk => by cases hk; decide)
    ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem fm_mulHalf {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulHalf_ok h.ws ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem wMulHalf {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : HalfCk g.full o x b)
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulHalf (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulHalf h.2.1 ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulHalf_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.2.1.ws.kw_pos)
    ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem wWordMod {g : CallGeometry} {sp : BitVec 32} {a : Nat} {x r m : Nat} {top : Option Nat}
    (ck : ModCk g.full x r m top) (htop : ∀ k ∈ top, k ≤ 2)
    (hx : x < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x) :
    RelCT isa (WR g sp a) (wordMod g.full x r m top) (WR g sp a) := by
  have ht : ∀ {u t : State}, WIn g sp a u t → ∀ k, top = some k → wq a + k ≤ (geometry g).w :=
    fun h k e => by have := htop k (by rw [e]; rfl); have := h.2.2.2.2; omega
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_wordMod h.2.1 h.mlen h.2.2.2.1 (by have := h.2.2.2.2; simp only [Geo.w] at this ⊢; omega) (ht h)
      hx hr hmN hrT hmT hrm hxr hxt hxm) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.wordMod_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm h₁.2.2.2.1
    (by have := h₁.2.2.2.2; simp only [geometry, Geo.w] at this ⊢; omega) (ht h₁)
    ck.c₀ ck.c₁ ck.c₂ _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run, h₁.mlen⟩, ⟨h₂.2.1.ws, h₂.run, h₂.mlen⟩⟩ e₁ e₂

/-! ## The word branch -/

theorem wEWord {g : CallGeometry} {sp : BitVec 32} {a x m : Nat}
    (hl : ∃ hint, (VG.Taint.check sseTaint (τV g.full) (seqs (ltA g.full x m)) hint).isSome = true)
    (he : ∃ hint, (VG.Taint.check sseTaint (τV g.full) (seqs (eqA g.full aA aOne)) hint).isSome = true)
    (rk : RowsCk g.full aY x aE (some 2)) (mk : ModCk g.full aY aA m (some 2))
    (hx : x < nArr) (hm : m < nArr) (hxY : x ≠ aY) (hxX : x ≠ aY + 1) (hmT : m ≠ aT) (hmA : m ≠ aA)
    (hmY : m ≠ aY) :
    RelCT isa (WR g sp a) (seqs (eWord g.full x m)) (WR g sp a) := by
  unfold eWord
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq (wTaint hl fun _ _ h => fm_ltA h hx hm)
      (RelCT.seqs_cons (by simp) (wMulShort rk (by decide) hx (by decide) hxY hxX (by decide) (by decide))
        (wWordMod mk (by simp) (by decide) (by decide) hm (by decide) hmT (fun e => hmA e.symm) (by decide) (by decide)
          hmY))))
    (wTaint he fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)))

theorem wQInv {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (seqs (qInvWord g.full)) (WR g sp a) := by
  unfold qInvWord
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq (wTaint ck.ltQI fun _ _ h => fm_ltA h (by decide) (by decide))
      (RelCT.seqs_cons (by simp) (wMulHalf ck.rQI (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
        (wWordMod ck.mP (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)))))
    (wTaint ck.eqOne fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)))

theorem wProducts {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (wordProducts g.full) (WR g sp a) := by
  unfold wordProducts
  refine RelCT.seqs_append (by simp [eWord, ltA]) (by simp [qInvWord, ltA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [eWord, ltA]) (by simp [eWord, ltA]) (VG.RelCT.seq
      (wEWord ck.ltDP ck.eqOne ck.rDP ck.mM1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide))
      (wEWord ck.ltDQ ck.eqOne ck.rDQ ck.mM2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide))))
    (wQInv ck))

theorem wDWords {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (dWords g.full) (WR g sp a) := by
  have m₁ : RelCT isa (WR g sp a) (wordMod g.full aD aVR aM1) (WR g sp a) :=
    wWordMod ck.dM1 (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have m₂ : RelCT isa (WR g sp a) (wordMod g.full aD aVR aM2) (WR g sp a) :=
    wWordMod ck.dM2 (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have e₁ := wTaint (sp := sp) (a := a) ck.eqDP fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)
  have e₂ := wTaint (sp := sp) (a := a) ck.eqDQ fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)
  have l := wTaint (sp := sp) (a := a) ck.ltD fun _ _ h => fm_ltA h (by decide) (by decide)
  unfold dWords
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq ?_ e₂)
  refine RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq ?_ m₂)
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq ?_ e₁)
  exact RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq l m₁)

theorem wBranch {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (wordBranch g.full) (WR g sp a) := by
  unfold wordBranch
  split
  · exact VG.RelCT.seq (wProducts ck) (wDWords ck)
  · exact wProducts ck

/-! ## The checks -/

/-- The guard, of the arguments and `n`. -/
def BalN (g : CallGeometry) (n : Nat) : Prop :=
  (g.args 1).toNat % 8 = 0 ∧ 2 * (g.args (pLenArg g.full)).toNat = (g.args 1).toNat ∧
    2 * (g.args (qLenArg g.full)).toNat = (g.args 1).toNat ∧ 128 ≤ (g.args 1).toNat ∧
    2 ^ (32 * (geometry g).w - 1) ≤ n

theorem pLen_lt (full : Bool) : pLenArg full < scratchArg full + 2 := by cases full <;> decide
theorem qLen_lt (full : Bool) : qLenArg full < scratchArg full + 2 := by cases full <;> decide
theorem nLen_lt (full : Bool) : 1 < scratchArg full + 2 := by cases full <;> decide

theorem arg_val {s : State} {B : Addr} {Z i a : Nat} {v : BitVec 32}
    (h : VG.Proof.Bignum.X86.CallArgument s B Z i (BitVec.ofNat 32 a)) (h' : VG.Proof.Bignum.X86.CallArgument s B Z i v)
    (ha : a ≤ 1024) : a = v.toNat := by
  have e := h.value.symm.trans h'.value
  rw [← e, BitVec.toNat_ofNat]; omega

theorem Inputs.arg {g : CallGeometry} {s : State} (h : Inputs g s) {i a : Nat}
    (c : VG.Proof.Bignum.X86.CallArgument s g.base g.size i (BitVec.ofNat 32 a)) (ha : a ≤ 1024)
    (hi : i < scratchArg g.full + 2) : a = (g.args i).toNat :=
  arg_val c (h.arguments i hi) ha

/-- Each run's start: what the checks start from, and its numbers. -/
abbrev RunBase (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) : Prop :=
  Run g sp x.2 ∧ BodyIn (geometry g) x.1 x.2

/-- Both runs, each from its own start, with the same `n`. -/
def Both₂ (P : Vals × State → State → Prop) (t₁ t₂ : State) : Prop :=
  ∃ x₁ x₂, (fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n) x₁ x₂ ∧ P x₁ t₁ ∧ P x₂ t₂

theorem taintLift {g : CallGeometry} {sp : BitVec 32} {c : Prog isa} {P Q : Vals × State → State → Prop}
    (hc : ∃ hint, (VG.Taint.check sseTaint (τV g.full) c hint).isSome = true)
    (hr : ∀ x t, P x t → Run g sp t) (hw : ∀ x t, P x t → WP isa c t (Q x)) :
    RelCT isa (Both₂ P) c (Both₂ Q) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n)
    (VG.RelCT.taint (A := sseTaint) (τV g.full) (fun t₁ t₂ ⟨x₁, x₂, _, h₁, h₂⟩ => (hr x₁ t₁ h₁).agree (hr x₂ t₂ h₂)) hc) hw

theorem stg_run {g : CallGeometry} {sp : BitVec 32} {u t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (r : Run g sp u) (h : Stg (geometry g) u A live c t) : Run g sp t := h.fm.run r

/-- What `start` leaves. -/
def AtStart (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0
    (decide (x.1.p % 2 = 1) && decide (x.1.p * x.1.q = x.1.n)) t

/-- Before the product: the guard in `sG`. -/
def AtBal (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t ∧
    (slot t.mem g.base sG = 0 ↔ BalN g x.1.n)

/-- After the product. -/
def AtProd (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t ∧
    val32 t.mem (geometry g).B (arr (geometry g).w aVQ) (2 * (geometry g).w) = x.1.p * x.1.q

theorem startBal_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State}
    (h : RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)) t
      (AtBal g sp x) := by
  obtain ⟨⟨r, b⟩, h6⟩ := h
  obtain ⟨ap, -, hap, -, parg⟩ := b.pLen
  obtain ⟨aq, -, haq, -, qarg⟩ := b.qLen
  have ep := r.1.arg parg hap (pLen_lt g.full)
  have eq := r.1.arg qarg haq (qLen_lt g.full)
  refine WP.mono (h6.balanced_ok (h6.arg parg) (h6.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, han, cn, _, hg⟩ => ⟨⟨r, b⟩, h7, ?_⟩
  have ea := (stg_run r h6).1.arg cn han (nLen_lt g.full)
  have nv : num t.mem g.base (geometry g).w aN = x.1.n := h6.arrs.get (by decide)
  have tp : 2 ^ 31 ≤ mw t.mem g.base (geometry g).w aN ((geometry g).w - 1) ↔
      2 ^ (32 * (geometry g).w - 1) ≤ x.1.n := by
    rw [← nv]; exact top_iff h6.ws.ws.wpos
  refine hg.trans ?_
  subst ea ep eq
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mpr e⟩⟩

theorem startGuard_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtBal g sp x t) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) t fun t' =>
      AtBal g sp x t' ∧ t'.zf = some (decide (slot t'.mem g.base sG = 0)) := by
  obtain ⟨rb, hs, hg⟩ := h
  refine wp_movS (readSrc_sc hs.ws.ws.workspace (by have := hs.ws.ws.hdr_le; unfold sG hdr at *; omega))
    fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
  have hs' := (hs.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have mm : t'.mem = t.mem := T.mem.trans U.mem
  have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [mm]
  refine ⟨⟨rb, hs', by rw [sl]; exact hg⟩, ?_⟩
  rw [z, U.gpr, sub0_beq, sl]; rfl

/-- Under the guard, the product over the primes' `w / 2` words. -/
theorem halfProd_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State}
    (h : AtBal g sp x t ∧ BalN g x.1.n) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf (lay g.full) aVQ aP aQ) t (AtProd g sp x) := by
  obtain ⟨⟨⟨r, b⟩, hs, _⟩, bal⟩ := h
  obtain ⟨a, -, ha, plt, parg⟩ := b.pLen
  obtain ⟨a', -, ha', qlt, qarg⟩ := b.qLen
  have ea := r.1.arg parg ha (pLen_lt g.full)
  have ea' := r.1.arg qarg ha' (qLen_lt g.full)
  subst ea ea'
  obtain ⟨h8, hp, hq, -, -⟩ := bal
  have e8 : 32 * ((geometry g).w / 2) = 8 * (g.args (pLenArg g.full)).toNat := by
    simp only [geometry, Geo.w, VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega
  exact WP.mono (hs.mulHalf_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by show x.1.p < _; rw [e8]; exact plt)
    (by show x.1.q < _; rw [e8, show 8 * (g.args (pLenArg g.full)).toNat = 8 * (g.args (qLenArg g.full)).toNat by
      omega]; exact qlt)) fun _ ⟨ht, e⟩ => ⟨⟨r, b⟩, ht, e⟩

theorem start_relCT {g : CallGeometry} {sp : BitVec 32} (ck : KcCk g.full) :
    RelCT isa (Both₂ fun x t => RunBase g sp x ∧ t = x.2) (start g.full) (Both₂ (AtStart g sp)) := by
  unfold start
  simp only [seqs]
  -- `setOne` and `bitOf`.
  refine VG.RelCT.assoc (VG.RelCT.seq (R := Both₂ fun x t => RunBase g sp x ∧
    Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t)
    (taintLift ck.first (fun x t h => h.2 ▸ h.1.1) fun x t h => by
      obtain ⟨hb, rfl⟩ := h; exact WP.mono (first_ok hb.2) fun _ ht => ⟨hb, ht⟩) ?_)
  -- The guard.
  refine VG.RelCT.seq (R := Both₂ (AtBal g sp))
    (taintLift ck.bal (fun x t h => stg_run h.1.1 h.2) fun x t h => startBal_ok h) ?_
  -- The product `p q`: over the primes' `w / 2` words where the guard holds.
  refine VG.RelCT.seq (R := Both₂ (AtProd g sp)) ?_ ?_
  · unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
    have zEq : ∀ {t₁ t₂ : State}, Both₂ (fun x t => AtBal g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
        t₁ t₂ → t₁.zf = t₂.zf := fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ => by
      rw [z₁, z₂]
      have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
        rw [g₁.2.2, g₂.2.2]; change BalN g x₁.1.n ↔ BalN g x₂.1.n; rw [hn]
      simp only [this]
    refine VG.RelCT.seq (R := Both₂ fun x t => AtBal g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
      (taintLift ck.guard (fun x t h => stg_run h.1.1 h.2.1) fun x t h => startGuard_ok h)
      (VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_)
    · refine (relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n)
        (P := fun x t => AtBal g sp x t ∧ BalN g x.1.n) ?_ fun x t h => halfProd_ok h).mono ?_ fun _ _ h => h
      · refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
        obtain ⟨x₁, x₂, _, h₁, h₂⟩ := hp
        exact VG.Proof.Rsa.X86.WordRt.mulHalf_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
          (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
          (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.1.2.1.ws.kw_pos)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ck.half.c₀ ck.half.c₁ ck.half.c₂ _ _ _ _ _ _
          ⟨⟨h₁.1.2.1.ws, stg_run h₁.1.1.1 h₁.1.2.1⟩, ⟨h₂.1.2.1.ws, stg_run h₂.1.1.1 h₂.1.2.1⟩⟩ e₁ e₂
      · rintro t₁ t₂ ⟨hb, et⟩
        have et₂ : isa.eval .e t₂ = some true := (zEq hb).symm.trans et
        obtain ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := hb
        have b₁ : BalN g x₁.1.n := g₁.2.2.mp (by
          change t₁.zf = _ at et; rw [z₁] at et; simpa using et)
        have b₂ : BalN g x₂.1.n := g₂.2.2.mp (by
          change t₂.zf = _ at et₂; rw [z₂] at et₂; simpa using et₂)
        exact ⟨x₁, x₂, hn, ⟨g₁, b₁⟩, ⟨g₂, b₂⟩⟩
    · refine (relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n) (P := AtBal g sp) ?_ fun x t h =>
        WP.mono (h.2.1.mulWide_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide)
          (by decide)) fun _ ⟨ht, e⟩ => ⟨h.1, ht, e⟩).mono ?_ fun _ _ h => h
      · refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
        obtain ⟨x₁, x₂, _, h₁, h₂⟩ := hp
        exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
          (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
          (rows := none) (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.2.1.ws.kw_pos) (Nat.le_refl _)
          (fun k hk => by cases hk) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ck.rows.c₀ ck.rows.c₁ ck.rows.c₂ _ _ _ _ _ _
          ⟨⟨h₁.2.1.ws, stg_run h₁.1.1 h₁.2.1⟩, ⟨h₂.2.1.ws, stg_run h₂.1.1 h₂.2.1⟩⟩ e₁ e₂
      · rintro t₁ t₂ ⟨⟨x₁, x₂, hn, ⟨g₁, _⟩, ⟨g₂, _⟩⟩, _⟩
        exact ⟨x₁, x₂, hn, g₁, g₂⟩
  · -- `p q = n`, and'ed into the mask.
    refine taintLift ck.eqAcc (fun x t h => stg_run h.1.1 h.2.1) fun x t h => ?_
    refine WP.seq (WP.mono (h.2.1.eqWide_ok (o := aVQ) (n := aN) (by decide) (by decide)) fun t1 ⟨h1, e1⟩ => ?_)
    refine WP.mono (h1.acc_ok (d := decide (x.1.p * x.1.q = x.1.n)) ?_) fun _ ht => ⟨h.1, ht⟩
    rw [e1, h.2.2]
    change (if x.1.p * x.1.q = x.1.n then 1 else 0) = _
    by_cases hh : x.1.p * x.1.q = x.1.n <;> simp [hh]

/-- Before the guard's branch: `p - 1`, `q - 1`, and the guard in `sG`. -/
def AtGuard (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ (∃ c, Stg (geometry g) x.2 (aFin x.1) liveFin c t) ∧
    (slot t.mem g.base sG = 0 ↔ BalN g x.1.n)

/-- After either branch: the frame. -/
def Done (g : CallGeometry) (sp : BitVec 32) (t₁ t₂ : State) : Prop :=
  ∃ u₁ u₂, (Run g sp u₁ ∧ Fm (geometry g) u₁ t₁) ∧ (Run g sp u₂ ∧ Fm (geometry g) u₂ t₂)

theorem guardPre_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtStart g sp x t) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM1 aP, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM1),
      VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM2 aQ, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM2),
      .block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)]) t
      (AtGuard g sp x) := by
  obtain ⟨⟨r, b⟩, h⟩ := h
  obtain ⟨ap, -, hap, -, parg⟩ := b.pLen
  obtain ⟨aq, -, haq, -, qarg⟩ := b.qLen
  have ep := r.1.arg parg hap (pLen_lt g.full)
  have eq := r.1.arg qarg haq (qLen_lt g.full)
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  have h6' : Stg (geometry g) x.2 (aFin x.1) liveFin _ t6 := h6.congr rfl
  refine WP.mono (h6'.balanced_ok (h6'.arg parg) (h6'.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, han, cn, _, hg⟩ => ⟨⟨r, b⟩, ⟨_, h7⟩, ?_⟩
  have ea := (stg_run r h6').1.arg cn han (nLen_lt g.full)
  have nv : num t6.mem g.base (geometry g).w aN = x.1.n := h6'.arrs.get (by decide)
  have tp : 2 ^ 31 ≤ mw t6.mem g.base (geometry g).w aN ((geometry g).w - 1) ↔
      2 ^ (32 * (geometry g).w - 1) ≤ x.1.n := by
    rw [← nv]; exact top_iff h6'.ws.ws.wpos
  refine hg.trans ?_
  subst ea ep eq
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mpr e⟩⟩

theorem guard_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) t fun t' =>
      AtGuard g sp x t' ∧ t'.zf = some (decide (slot t'.mem g.base sG = 0)) := by
  obtain ⟨rb, ⟨c, hs⟩, hg⟩ := h
  refine wp_movS (readSrc_sc hs.ws.ws.workspace (by have := hs.ws.ws.hdr_le; unfold sG hdr at *; omega))
    fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
  have hs' := (hs.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have mm : t'.mem = t.mem := T.mem.trans U.mem
  have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [mm]
  refine ⟨⟨rb, ⟨c, hs'⟩, by rw [sl]; exact hg⟩, ?_⟩
  rw [z, U.gpr, sub0_beq, sl]; rfl

theorem bits_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t) :
    WP isa (bitsBranch g.full) t fun t' => Run g sp x.2 ∧ Fm (geometry g) x.2 t' := by
  obtain ⟨⟨r, b⟩, ⟨c, hs⟩, _⟩ := h
  unfold bitsBranch
  split
  · refine WP.seq (WP.mono (hs.productsP_ok b.qLen) fun t1 ⟨_, _, _, _, h1⟩ => ?_)
    exact WP.mono (dBits_ok h1) fun _ ⟨_, _, _, _, _, _, h2⟩ => ⟨r, h2.fm⟩
  · exact WP.mono (hs.productsP_ok b.qLen) fun _ ⟨_, _, _, _, h1⟩ => ⟨r, h1.fm⟩

/-- Under the guard, a run is in the word steps. -/
theorem AtGuard.win {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t)
    (bal : BalN g x.1.n) : WIn g sp (g.args (pLenArg g.full)).toNat x.2 t := by
  obtain ⟨⟨r, b⟩, ⟨c, hs⟩, _⟩ := h
  obtain ⟨a, -, ha, -, parg⟩ := b.pLen
  have ea := r.1.arg parg ha (pLen_lt g.full)
  subst ea
  obtain ⟨h8, hp, -, h128, -⟩ := bal
  refine ⟨r, hs.fm, ⟨parg, ha⟩, ?_, ?_⟩
  · simp only [wq]; omega
  · simp only [wq, geometry, Geo.w, VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega

theorem crtChecks_relCT {g : CallGeometry} {sp : BitVec 32} (ck : KcCk g.full) :
    RelCT isa (Both₂ (AtStart g sp)) (crtChecks g.full (wordBranch g.full) (bitsBranch g.full)) (Done g sp) := by
  unfold crtChecks
  refine RelCT.seqs_append (l₁ := [VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM1 aP,
      .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM1), VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM2 aQ,
      .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM2),
      .block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)])
    (l₂ := [VG.Impl.Rsa.X86.WordModRt.ifBalanced sG (wordBranch g.full) (bitsBranch g.full)]) (by simp) (by simp)
    (VG.RelCT.seq (taintLift ck.pre (fun x t h => stg_run h.1.1 h.2) fun x t h => guardPre_ok h) ?_)
  show RelCT isa _ (VG.Impl.Rsa.X86.WordModRt.ifBalanced sG _ _) _
  unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
  have zEq : ∀ {t₁ t₂ : State}, Both₂ (fun x t => AtGuard g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
      t₁ t₂ → t₁.zf = t₂.zf := fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ => by
    rw [z₁, z₂]
    have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
      rw [g₁.2.2, g₂.2.2]; change BalN g x₁.1.n ↔ BalN g x₂.1.n; rw [hn]
    simp only [this]
  refine VG.RelCT.seq (R := Both₂ fun x t => AtGuard g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
    (taintLift ck.guard (fun x t h => stg_run h.1.1 h.2.1.choose_spec) fun x t h => guard_ok h)
    (VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_)
  · -- Under the guard: the word steps.
    refine (wBranch (sp := sp) (a := (g.args (pLenArg g.full)).toNat) ck.word).mono ?_
      fun _ _ ⟨u₁, u₂, _, w₁, w₂⟩ => ⟨u₁, u₂, ⟨w₁.1, w₁.2.1⟩, ⟨w₂.1, w₂.2.1⟩⟩
    rintro t₁ t₂ ⟨hb, et⟩
    have et₂ : isa.eval .e t₂ = some true := (zEq hb).symm.trans et
    obtain ⟨x₁, x₂, _, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := hb
    have b₁ : BalN g x₁.1.n := g₁.2.2.mp (by
      change t₁.zf = _ at et; rw [z₁] at et; simpa using et)
    have b₂ : BalN g x₂.1.n := g₂.2.2.mp (by
      change t₂.zf = _ at et₂; rw [z₂] at et₂; simpa using et₂)
    exact ⟨x₁.2, x₂.2, trivial, g₁.win b₁, g₂.win b₂⟩
  · -- Else bit by bit.
    refine ((taintLift (P := AtGuard g sp) ck.bits (fun x t h => stg_run h.1.1 h.2.1.choose_spec)
      fun x t h => bits_ok h).mono (fun t₁ t₂ ⟨⟨x₁, x₂, hn, ⟨g₁, _⟩, ⟨g₂, _⟩⟩, _⟩ => ⟨x₁, x₂, hn, g₁, g₂⟩)
      fun _ _ ⟨x₁, x₂, _, h₁, h₂⟩ => ⟨x₁.2, x₂.2, h₁, h₂⟩)

/-! ## `sized` -/

theorem body_eq (full : Bool) : (if full then keyBody full else crtBody full) =
    seqs [start full, crtChecks full (wordBranch full) (bitsBranch full)] := by
  cases full <;> rfl

theorem loads_run {g : CallGeometry} {sp : BitVec 32} {s t : State} (h : Run g sp s) (it : Inputs g t)
    (K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t) : Run g sp t :=
  ⟨it, ⟨by rw [K.1 _ (by decide)]; exact h.2.1.1, by rw [K.2.2, K.1 _ (by decide)]; exact h.2.1.2⟩,
    (K.1 _ (by decide)).trans h.2.2⟩

/-- Two runs of `sized` with the same `n` leak the same trace. -/
theorem sized_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (sized g.full) fun _ _ => True := by
  have ck := kcCk g.full
  unfold sized
  simp only [seqs]
  refine VG.RelCT.seq (R := Both₂ fun x t => RunBase g sp x ∧ t = x.2) ?_ (VG.RelCT.seq (R := Done g sp) ?_ ?_)
  · obtain ⟨_, hc⟩ := ck.loads
    have T := VG.RelCT.wpDep (VG.RelCT.taint (A := sseTaint) (τV g.full)
      (P := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (fun t₁ t₂ h => h.1.1.agree h.1.2) hc)
      (F := fun (σ t : State) => Run g sp t ∧ BodyIn (geometry g) (numbers g σ.mem) t) fun s₁ s₂ h =>
        ⟨WP.mono (loads_ok h.1.1.1 len) fun t ⟨it, b, _, K⟩ => ⟨loads_run h.1.1 it K, b⟩,
          WP.mono (loads_ok h.1.2.1 len) fun t ⟨it, b, _, K⟩ => ⟨loads_run h.1.2 it K, b⟩⟩
    refine T.mono (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨_, σ₁, σ₂, hp, ⟨r₁, b₁⟩, ⟨r₂, b₂⟩⟩
    refine ⟨(numbers g σ₁.mem, t₁), (numbers g σ₂.mem, t₂), ?_, ⟨⟨r₁, b₁⟩, rfl⟩, ⟨⟨r₂, b₂⟩, rfl⟩⟩
    show Spec.Rsa.os2ip (inputBytes g σ₁.mem 0) = Spec.Rsa.os2ip (inputBytes g σ₂.mem 0)
    rw [hp.2]
  · rw [body_eq]
    exact RelCT.seqs_cons (by simp) (start_relCT ck) (crtChecks_relCT ck)
  · obtain ⟨_, hc⟩ := ck.last
    exact VG.RelCT.taint (A := sseTaint) (τV g.full)
      (fun t₁ t₂ ⟨_, _, ⟨r₁, f₁⟩, ⟨r₂, f₂⟩⟩ => (f₁.run r₁).agree (f₂.run r₂)) hc

open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheckRt (sized)
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- What the runs of `sized` from the states themselves need: the inputs, `esp`, and the arguments apart
from what the body writes. -/
def SizedAt (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ s.gpr .esp = sp ∧ sp.toNat + argSpan g.full ≤ 2 ^ 32 ∧
    ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, argSpan g.full⟩ r

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs g (s.withRegions (s.rd ++ s.wr) g.writes) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, CallGeometry.writes], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j hj => ?_, h.inputApart⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j hj
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_run {g : CallGeometry} {sp : BitVec 32} {s : State} (S : SizedAt g sp s) :
    Run g sp (s.withRegions (s.rd ++ s.wr) g.writes) := by
  obtain ⟨h, esp, fit, apart⟩ := S
  refine ⟨narrow_inputs h, ⟨?_, fun r hr => ?_⟩, esp⟩
  · show (s.gpr .esp).toNat + argSpan g.full ≤ _; rw [esp]; exact fit
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan g.full⟩ r; rw [esp]; exact apart r hr

theorem sizedNarrow_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => Both (SizedAt g sp) s₁ s₂ ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (sized g.full) fun _ _ => True := by
  refine relCT_narrow (Pn := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
    (fun s => s.rd ++ s.wr) (fun _ => g.writes) (fun s₁ s₂ ⟨⟨S₁, S₂⟩, hn⟩ => ?_) (sized_relCT g len sp)
  have cov : ∀ {s : State}, SizedAt g sp s → Covers g.writes s.wr := by
    intro s S
    apply Covers.of_forall
    intro r hr
    simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Covers.of_mem (by simpa using S.1.ws.workspace.wr)
  have wp : ∀ {s : State}, SizedAt g sp s →
      ∃ F, WP isa (sized g.full) (s.withRegions (s.rd ++ s.wr) g.writes) F :=
    fun S => ⟨_, sized_wp (narrow_inputs S.1) len⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    ⟨narrow_run S₁, narrow_run S₂⟩, hn⟩

end VG.Proof.Rsa.X86.KeyCheck

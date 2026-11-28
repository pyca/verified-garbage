module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGen
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGen
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public meta import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: key generation is constant time

Its two blocks by the taint analysis, with the pointers public, and the call
of `xmssTree` by its contract (`RelCT.call`), whose public data are pointers
too (`keyGen_ct`); then `keyGen_verified`, against `keyGenContract`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.KeyGen

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)

/-- The six SHAKE parameter sets. -/
abbrev Shake6 (p : Params) : Prop :=
  p = shake_128s ∨ p = shake_128f ∨ p = shake_192s ∨ p = shake_192f ∨ p = shake_256s ∨ p = shake_256f

theorem Shake6.sz {p : Params} (h : Shake6 p) : Sz p := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem Shake6.hps {p : Params} (h : Shake6 p) : Hps p.hp := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Shake6.d {p : Params} (h : Shake6 p) : p.d - 1 < 2 ^ 16 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Code the taint analysis proves constant time from the registers `rs`,
public in both runs. -/
theorem taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VectorTaint.taint.T}
    (h : (VectorTaint.taint.check (VectorTaint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VectorTaint.taint) (VectorTaint.ofRegs rs) (fun x y hp =>
    ⟨⟨(hr x y hp).1, fun r h => (hr x y hp).2 r (Taint.mem_ofRegs.mp h)⟩,
      fun _ h => absurd (RegSet.mem_ofList.mp h) List.not_mem_nil⟩) h

/-- Two runs of `c₁` then `c₂`, from the states each run's correctness
proof describes. -/
theorem relSeq {A₁ A₂ B₁ B₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hct : RelCT isa (fun a b => A₁ a ∧ A₂ b) c₁ fun _ _ => True)
    (h₁ : ∀ a, A₁ a → WP isa c₁ a B₁) (h₂ : ∀ b, A₂ b → WP isa c₁ b B₂)
    (hr : RelCT isa (fun a b => B₁ a ∧ B₂ b) c₂ Q) : RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.mono (RelCT.wp hct fun a b h => ⟨h₁ a h.1, h₂ b h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hr

section
variable {P : State → State → Prop}

theorem ct_pro {p : Params} (hp : Shake6 p) (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x0, .x1, .x2, .x3], x.gpr r = y.gpr r) :
    RelCT isa P (.block (proCode p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

theorem ct_tail {p : Params} (hp : Shake6 p) (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ [Reg.x19, .x20, .x21], x.gpr r = y.gpr r) :
    RelCT isa P (.block (tailCode p)) fun _ _ => True := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact taintR _ hr (by taint_decide)

end

/-- After the call, in one run. -/
structure After (σ : State) (S : Addr) (w : State) : Prop where
  x19 : w.gpr .x19 = S
  x20 : w.gpr .x20 = σ.gpr .x1
  x21 : w.gpr .x21 = σ.gpr .x2
  sp : w.sp = σ.sp

theorem call_after {p : Params} (hz : Sz p) (hh : Hps p.hp) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    {σ : State} {S X : Addr} (hK : KG p σ) (hS : σ.gpr .x3 = S) {u : State} (hu : KPro p σ S X u) :
    WP isa (.call f.xmssName (Impl.SlhDsa.AArch64.Shake.xmssCode p f)) u (After σ S) := by
  obtain ⟨hpre, hc, hw⟩ := call_pre hz hh hK hS hu
  exact WP.callV hx.1 hpre hc hw (fun s' _ _ hsp _ hpres _ _ _ =>
    ⟨by rw [hpres _ (by decide) (by decide), hu.x19], by rw [hpres _ (by decide) (by decide), hu.x20],
      by rw [hpres _ (by decide) (by decide), hu.x21], by rw [hsp, hu.sp]⟩) hxn

/-- `keyGen` is constant time: its timing depends only on the pointers. -/
theorem keyGen_ct {p : Params} (hp : Shake6 p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true) :
    ConstantTime isa (kgK p).pre (kgK p).pub (Impl.SlhDsa.AArch64.Shake.keyGen p f) := by
  have hz := hp.sz
  have hh := hp.hps
  have hd := hp.d
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨p0, p1, p2, p3, psp⟩ := hpub
  have hK₁ : KG p s₁ := h₁
  have hK₂ : KG p s₂ := h₂
  obtain ⟨S, hS₁⟩ : ∃ S, s₁.gpr .x3 = S := ⟨_, rfl⟩
  have hS₂ : s₂.gpr .x3 = S := by rw [← p3, hS₁]
  have ent : ∀ {σ : State}, KG p σ → σ.gpr .x3 = S →
      WP isa (.block (proCode p)) σ (KPro p σ S (σ.gpr .x0)) := fun {σ} hK hS =>
    pro_ok hz hd hS rfl (by rw [hK.wr, hS]; simp) (by rw [hK.rd]; simp) hK.f_seed (by rw [← hS]; exact hK.f_scr)
      (by rw [← hS]; exact hK.d_seed_scr)
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.AArch64.Shake.keyGen p f) fun _ _ => True := by
    rw [keyGen_eq]
    refine relSeq (ct_pro hp fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, psp], fun r hr => ?_⟩)
      (fun x hx => by rw [hx]; exact ent hK₁ hS₁) (fun y hy => by rw [hy]; exact ent hK₂ hS₂) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx, hy, p0]
      · rw [hx, hy, p1]
      · rw [hx, hy, p2]
      · rw [hx, hy, p3]
    refine relSeq (RelCT.call hx.1 hx.2.1 [] (callW p S) fun x y ⟨hx', hy'⟩ => ?_)
      (fun x hx' => call_after hz hh hx hxn hK₁ hS₁ hx') (fun y hy' => call_after hz hh hx hxn hK₂ hS₂ hy')
      (ct_tail hp fun x y ⟨hx', hy'⟩ => ⟨by rw [hx'.sp, hy'.sp, psp], fun r hr => ?_⟩)
    · obtain ⟨q₁, c₁, w₁⟩ := call_pre hz hh hK₁ hS₁ hx'
      obtain ⟨q₂, c₂, w₂⟩ := call_pre hz hh hK₂ hS₂ hy'
      refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [xmssContract, State.withRegions_gpr]
      rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
        State.callEntry_gpr _ (by decide), hx'.x0, hy'.x0, hx'.x2, hy'.x2]
      exact ⟨rfl, rfl, by simp only [State.withRegions, State.callEntry]; rw [hx'.sp, hy'.sp, psp]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx'.x19, hy'.x19]
      · rw [hx'.x20, hy'.x20, p1]
      · rw [hx'.x21, hy'.x21, p2]
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The contract -/

/-- A state of `keyGenContract`'s precondition. -/
def kgSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, 3 * p.n⟩]
  wr := [⟨0x2000, p.skLen⟩, ⟨0x3000, p.pkLen⟩, ⟨0x10000, scratchWords * 8⟩]

theorem kg_implies {p : Params} (hz : Sz p) :
    (kgK p).Implies (Spec.SlhDsa.keyGenContract p AArch64.abi 0) := by
  have hn := hz.n32
  refine ⟨fun s h => ?_, fun s s' _ h => ?_, fun s₁ s₂ _ _ h => ?_, ⟨kgSat p, ?_⟩⟩
  · sig_pre [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
    sig_split h
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, h⟩
  · sig_post [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
    exact h
  · sig_pub [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
    obtain ⟨hsp, -, h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hsp⟩
  · have hsk : p.skLen ≤ 128 := by simp only [Params.skLen]; omega
    have hpk : p.pkLen ≤ 64 := by simp only [Params.pkLen]; omega
    sig_pre [Spec.SlhDsa.keyGenContract, Spec.SlhDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs, kgSat]
    sig_and_intros
    all_goals first
      | rfl
      | omega
      | (simp only [BitVec.reduceToNat]; omega)
      | (simp only [scratchWords, BitVec.reduceToNat]; omega)
      | (apply Offset.disjoint_of_le <;> dsimp only <;> simp only [scratchWords, BitVec.reduceToNat] <;> omega)

/-! ## `Verified` -/

/-- `vg_slhdsa_shake_*_keygen` for a SHAKE parameter set `p`, over any
`xmssTree` verified against its contract, meets `keyGenContract` in
constant time. -/
theorem keyGen_verified {p : Params} (hp : Shake6 p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true) :
    Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.keyGen p f) (Spec.SlhDsa.keyGenContract p AArch64.abi 0) :=
  Verified.of_correct (fun _ h => keyGen_wp hp.sz hp.hps hp.d hx hxn h) (keyGen_ct hp hx hxn) (kg_implies hp.sz)

end VG.Proof.SlhDsa.AArch64.KeyGen

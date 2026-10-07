import VerifiedGarbage.Proof.X25519.AArch64.Base.Main
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# X25519 of the base point on AArch64: constant time and the contract

As for Ed25519's `scalarBase`: the scalar's bits, the comb and the encoding
have a public trace (one taint check of the engine, whose addresses are the
working space `x0` plus constants or public counters), and so do the setup and
the finish.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64

theorem engine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engine (fun _ _ => True) := by
  apply CT.taintS (L := [combSym]) (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
  intro x y h
  refine ⟨agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  · simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.2.2.2.2.2.trans h.2.2.2.2.2.2.symm

private def BaseStart (base k out T : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base ∧ s.syms combSym = T

private def BasePrepared (base k out T : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out T : Addr} {s : State} (hs : BaseStart base k out T s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out T) := by
  obtain ⟨⟨hr, hw, hd, hn, hct⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  have htb : TblAt s base T := by
    rw [← hb, ← hT]; exact hct.tblAt (by rw [hr]; simp) (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, ma, _⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, mb⟩ syb => ?_
  rw [ga, hb] at pb ob mb
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_, ?_, by rw [syb, sya]; exact hT⟩,
    ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)
  · exact htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega)), ma x (Or.inr (by omega))]

private theorem start_ct (base k out T : Addr) :
    CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y) := by
  have hc : CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {base k out T : Addr} {s : State} (hs : BasePrepared base k out T s) :
    WP isa engine s (BaseReady base out) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ho⟩ := hs
  refine WP.mono (engine_ok h1 h2 h3 h4 h5 h6) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch h1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans ho⟩

private theorem engine_ct' (base k out T : Addr) :
    CT (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k out T _ ∧ BasePrepared base k out T _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem x25519Base_ct : ConstantTime isa baseLocal.pre baseLocal.pub x25519Base := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb, hsy⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
    (CT.seq (engine_ct' (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hsy.symm⟩⟩
    ex ey).1

theorem x25519Base_ok (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  x25519Base_correct hs

/-- The shared contract's precondition, from its facts. -/
theorem x25519Base_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x1, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem x25519Base_sat :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre baseSatState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, baseSatState.mem.readW (baseSatState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine x25519Base_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem x25519Base_implies : baseLocal.Implies
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, -, -, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, x25519Base_sat⟩

theorem x25519Base_verified :
    Verified AArch64.target x25519Base (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519Base_ok x25519Base_ct x25519Base_implies

end VG.Proof.X25519.AArch64.Base

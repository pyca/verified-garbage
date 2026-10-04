import VerifiedGarbage.Proof.X25519.AArch64.Base.Main
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.Contract

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

theorem engine_ct (base k : Addr) :
    CT (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y) engine (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0, .x1]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.x0.trans h.2.1.x0.symm
  · exact h.1.2.1.trans h.2.2.1.symm

private def BaseStart (base k out : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base

private def BasePrepared (base k out : Addr) (s : State) : Prop :=
  BaseEnginePre base k s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out : Addr} {s : State} (hs : BaseStart base k out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out) := by
  obtain ⟨⟨hr, hw, hd, hn⟩, ho, hk, hb⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, _, _⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, _⟩ => ?_
  rw [ga, hb] at pb ob
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)

private theorem start_ct (base k out : Addr) :
    CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y) := by
  have hc : CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {base k out : Addr} {s : State} (hs : BasePrepared base k out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct' (base k out : Addr) :
    CT (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k).mono
    (fun _ _ (h : BasePrepared base k out _ ∧ BasePrepared base k out _) => ⟨h.1.1, h.2.1⟩)
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
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
    (CT.seq (engine_ct' (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm⟩⟩ ex ey).1

theorem x25519Base_ok (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  x25519Base_correct hs

theorem x25519Base_verified :
    Verified AArch64.target x25519Base (Spec.X25519.x25519BaseContract AArch64.abi) :=
  Verified.of_correct x25519Base_ok x25519Base_ct (by
    sig_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, baseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.X25519.AArch64.Base

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFirstBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev Absorbed (v : Nat) (σ s : State) := Env v σ s ∧
  (∀p,2*p+1<v → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1))) ∧
  ∀k<v,s.mem.readW (countP σ k) 64=256

private theorem initial_relCT {v : Nat} {σ τ : State} {P Q : State → Prop} {c : Prog isa}
    (pub : Pub v σ τ) (hc : PointerCT [.x0,.x1,.x2] c)
    (ws : WP isa c σ P) (wt : WP isa c τ Q) :
    RelCT isa (fun s t => s=σ ∧ t=τ) c (fun s t => P s ∧ Q t) := by
  have ct : RelCT isa (fun s t => s=σ ∧ t=τ) c (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    rcases h with ⟨rfl,rfl⟩
    have ha : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2]) s t := by
      refine ⟨pub.2.2.2.1,?_⟩
      simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
      intro r hr
      rcases hr with rfl | rfl | rfl
      · exact pub.1
      · exact pub.2.1
      · exact pub.2.2.1
    exact ⟨hc _ _ _ _ _ _ True.intro True.intro ha es et,True.intro⟩
  exact (ct.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem startFour_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.init++Four.initCounts))
      (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t) :=
  initial_relCT pub startFour_ct (startFour_ok hp) (startFour_ok hq)

theorem startTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block (Impl.MlDsa.AArch64.Sample.Rej4.pro++Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
        Impl.MlDsa.AArch64.Sample.Rej4.absorbPair 0++Two.initCounts))
      (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t) :=
  initial_relCT pub startTwo_ct (startTwo_ok hp) (startTwo_ok hq)

theorem firstFour_left_relCT {σ τ : State} (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => Absorbed 4 σ s ∧ Absorbed 4 τ t)
      (.seq (.seq (.block (Four.squeezeSetup 0 5)) (five .x22 .x24 .x25)) (five .x23 .x26 .x27))
      (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ _ _ h => h) (by taint_decide))
    (fun _ h => WP.assoc' (firstFour_setup_ok hp h.1 h.2.1 h.2.2))
    (fun _ h => WP.assoc' (firstFour_setup_ok hq h.1 h.2.1 h.2.2))

theorem firstTwo_relCT {σ τ : State} (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => Absorbed 2 σ s ∧ Absorbed 2 τ t)
      (.seq (.block (Two.squeezeSetup 0 5)) (five .x22 .x24 .x25))
      (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t) :=
  env_relCT pub (fun _ h => h.1) (fun _ h => h.1) firstTwo_ct
    (fun _ h => firstTwo_setup_ok hp h.1 h.2.1 h.2.2)
    (fun _ h => firstTwo_setup_ok hq h.1 h.2.1 h.2.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

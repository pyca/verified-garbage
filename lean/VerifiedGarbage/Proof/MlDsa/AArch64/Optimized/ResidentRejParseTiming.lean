import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejControlTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def Start (s : State) (b p : Addr) (n : Nat) (L : List Zq) : Prop :=
  s.gpr .x2=b ∧ s.gpr .x3=coeffAddr p L.length ∧ (s.gpr .x4).toNat=256-L.length ∧
    (s.gpr .x5).toNat=n ∧ (s.gpr .x9).toNat=q ∧ Stored s.mem p L

theorem vectorSetup_start {σ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (h : Start σ b p n L) : WP isa (.block vectorSetup) σ (ParseInv σ b p n L 0) := by
  refine WP.mono (vectorSetup_ok (s := σ) h.2.2.2.2.1) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
    Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
  · rw [ha.only.get .x2,h.1]; exact (ptr_zero b).symm
  · rw [ha.only.get .x3]; exact h.2.1
  · rw [ha.only.get .x4]; exact h.2.2.1
  · rw [ha.only.get .x5]; exact h.2.2.2.1
  · rw [ha.only.mem]; exact h.2.2.2.2.2

theorem parse_relCT (v : Nat) {σ τ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (ss : Start σ b p n L) (st : Start τ b p n L)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : n%4=0) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (parse v) (fun _ _ => True) := by
  unfold parse
  apply RelCT.seq (R := fun s t => WideReady σ b p n 0 L s ∧ WideReady τ b p n 0 L t)
  · rw [List.append_assoc]
    apply RelCT.block_append
    apply RelCT.seq (R := fun s t => ParseInv σ b p n L 0 s ∧ ParseInv τ b p n L 0 t)
    · exact control_pair (fun _ _ h1 h2 => by subst h1; subst h2; exact hsp)
        (fun s h => by subst s; exact vectorSetup_start ss)
        (fun t h => by subst t; exact vectorSetup_start st) (by taint_decide)
    · exact wideControl_relCT hsp
  · apply RelCT.seq (widePhase_relCT hs ht hm hsp)
    intro s t tr ur s' t' hp es et
    obtain ⟨j,hj,hk,hjm⟩ := hp
    exact parseFour_relCT v hs ht hm hsp (by rw [hjm,hmod]) _ _ _ _ _ _ ⟨hj,hk⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

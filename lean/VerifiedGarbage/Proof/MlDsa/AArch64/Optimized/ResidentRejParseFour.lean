import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejInit

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem vectorSetup_inv {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block vectorSetup) s fun t => ParseInv s₀ b p n L d t ∧ t.gpr .x17=4 := by
  refine WP.mono (vectorSetup_ok (s := s) h.constants.qreg) fun t ⟨ht,hc,h17,h0,h10⟩ => ?_
  refine ⟨⟨(h.keep.trans ht.only.keep).mono (by decide),by rw [ht.only.mem]; exact h.frame,
    hc,h.bound,?_,?_,?_,?_,h10,h0,?_⟩,h17⟩
  · rw [ht.only.get .x2]; exact h.x2
  · rw [ht.only.get .x3]; exact h.x3
  · rw [ht.only.get .x4]; exact h.x4
  · rw [ht.only.get .x5]; exact h.x5
  · rw [ht.only.mem]; exact h.stored

theorem fourSetup_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block (vectorSetup++guard)) s fun t =>
      ParseInv s₀ b p n L d t ∧ t.gpr .x17=4 ∧
      t.gpr .x16=(if 4≤(t.gpr .x4).toNat then t.gpr .x5 else 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (vectorSetup_inv h) fun a ⟨ha,h17⟩ => ?_
  refine WP.mono (guard_ok h17 ha.zero) fun t ⟨ht,hv,hg⟩ => ?_
  exact ⟨ha.of_control (ht.mono (by decide)) hv,by rw [ht.get .x17]; exact h17,
    by rw [hg,ht.get .x4,ht.get .x5]⟩

/-- Four-candidate processing followed by scalar cleanup consumes the
entire available segment, unless the polynomial becomes full first. -/
theorem parseFour_ok (v : Nat) {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (hL : L.length≤256) (hmod : n%4=d%4) :
    WP isa (parse4 v) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧
        (d'=n ∨ (parsed s₀ b L d').length=256) := by
  refine WP.seq (WP.mono (fourSetup_ok h) fun a ⟨ha,h17,hg⟩ => ?_)
  refine WP.seq (WP.mono (fourPhase_ok hl ha h17 hmod hg)
    fun b ⟨j,hj,hdj,_,_,_⟩ => ?_)
  refine WP.mono (scalarPhase_ok hl hj hL) fun t ⟨k,hk,hjk,hend⟩ => ?_
  exact ⟨k,hk,Nat.le_trans hdj hjk,hend⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

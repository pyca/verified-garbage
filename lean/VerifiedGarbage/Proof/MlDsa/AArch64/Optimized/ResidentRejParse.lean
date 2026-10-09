import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParseFour

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem wideControl_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard)) s fun t =>
      ParseInv s₀ b p n L d t ∧ t.gpr .x17=16 ∧
      t.gpr .x16=(if 16≤(t.gpr .x4).toNat ∧ 16≤(t.gpr .x5).toNat then 16 else 0) := by
  have hm : WP isa (.block [.movz .x .x17 16 0]) s fun t =>
      Only [.x17] s t ∧ t.gpr .x17=16 := wp_movz fun t ht et => wp_nil ⟨ht,et⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by decide) hm) fun a ⟨⟨ha,h17⟩,hav⟩ => ?_
  have hi := h.of_control (ha.mono (by decide)) hav
  refine WP.mono (wideGuard_ok h17 hi.zero) fun t ⟨ht,hv,hg⟩ => ?_
  exact ⟨hi.of_control (ht.mono (by decide)) hv,by rw [ht.get .x17]; exact h17,
    by rw [hg,ht.get .x4,ht.get .x5]⟩

/-- The complete selected parser implements the shared byte-stream fold;
wide, narrow, and scalar paths share one accepted-prefix invariant. -/
theorem parse_ok (v : Nat) {s : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hl : StreamLayout s b p n) (hmod : n%4=0) (hL : L.length≤256)
    (h2 : s.gpr .x2=b) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (h5 : (s.gpr .x5).toNat=n)
    (h9 : (s.gpr .x9).toNat=q) (hst : Stored s.mem p L) :
    WP isa (parse v) s fun t => Keep parseRegs s t ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (rnFold L (candidateBytes s.mem b n)).length ∧
      (t.gpr .x4).toNat=256-(rnFold L (candidateBytes s.mem b n)).length ∧
      Stored t.mem p (rnFold L (candidateBytes s.mem b n)) := by
  unfold parse
  refine WP.seq ?_
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (vectorSetup_ok (s := s) h9) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  have hi : ParseInv s b p n L 0 a := by
    refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
      Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
    · rw [ha.only.get .x2,h2]; exact (ptr_zero b).symm
    · rw [ha.only.get .x3]; exact h3
    · rw [ha.only.get .x4]; exact h4
    · rw [ha.only.get .x5]; exact h5
    · rw [ha.only.mem]; exact hst
  refine WP.mono (wideControl_ok hi) fun a ⟨ha,h17,hg⟩ => ?_
  refine WP.seq (WP.mono (widePhase_ok hl ha h17 hg) fun a ⟨j,hj,_,hjm,_,_⟩ => ?_)
  refine WP.mono (parseFour_ok v hl hj hL (by rw [hmod,hjm])) fun t ⟨k,hk,_,hend⟩ => ?_
  have he := parsed_done s b L hk.bound hend
  have hp := hk.x3
  have hc := hk.x4
  have hs := hk.stored
  rw [he] at hp hc hs
  exact ⟨hk.keep,hk.frame,hp,hc,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

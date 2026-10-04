import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Impl.AesSiv.Arm

/-!
# AES-SIV on ARMv7: the calls of `vg_cmac_aes_finalize`

Untrusted: everything here is checked by Lean. As streaming AES-CMAC's
(`Proof/CmacAes/Stream/Arm/Call.lean`, `fin_call`, `fin_rel`), but with the
two stack arguments pushed from `r12` (`last_len`) and `lr` (the working
space), which `encrypt` and `decrypt` do not keep across calls: what a call
needs (`FArgs`), what it leaves (`FPost`), and that two calls with the same
arguments leak the same (`fin_rel`). The calls of `vg_cmac_aes_update` are
AES-CCM's (`Proof.AesCcm.Arm.upd_call`, `upd_rel`), and those of
`vg_aes_ctr32` AES-GCM's (`Proof.AesGcm.Arm.ctr_call`, `ctr_rel`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Stream.Arm (view blw16 view_gpr view_sp view_arg0 view_arg1 view_argAddr view_blw spA
  slot_sub push_frame cov_push covW_push WP.frameCallF RelCT.frameCall stackUse_finalize fRd fWr)
open VG.Proof.CmacAes.Arm (toNat_rounds)

structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = St
  r3 : s.gpr .r3 = P
  r12 : s.gpr .r12 = BitVec.ofNat 32 L
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  hsp : 16 ≤ s.sp.toNat
  kst : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ks : (⟨State.addr K, 272⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  pst : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr St, 16⟩
  ps : (⟨State.addr P, L⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  sts : (⟨State.addr St, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bk : (blw16 s).Disjoint ⟨State.addr K, 272⟩
  bp : (blw16 s).Disjoint ⟨State.addr P, L⟩
  bst : (blw16 s).Disjoint ⟨State.addr St, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr St, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr St) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr K) (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 240) 16)
        (Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt s.mem (State.addr P) L))
        (Spec.Aes.bytesAt s.mem (State.addr St) 16))

theorem FArgs.pre {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    Proof.CmacAes.Arm.finalizeArm.pre (view .r12 .lr s (fRd s K P L) (fWr St S)) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := fRd s K P L) (wr := fWr St S) h.hsp
  simp only [Proof.CmacAes.Arm.finalizeArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hL, State.withRegions_rd, State.withRegions_wr]
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, (h.bst.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bk.sub_left hb, h.bp.sub_left hb, h.bst.sub_left hb, h.bs.sub_left hb,
    h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
  · rw [view_sp, hspv]; omega
  · rw [view_sp, hspv]; have := s.sp.isLt; omega

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.AesSiv.Arm.finFrame s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.len; omega)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.finalizeRawArm) (fun _ hs => Proof.CmacAes.Arm.finalize_raw_wp hs)
    stackUse_finalize rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bst
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r12 .lr
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h' | h' | h' <;> omega
  simp only [Proof.CmacAes.Arm.finalizeRawArm, Proof.CmacAes.Arm.finalizeRaw, Proof.CmacAes.Arm.mn,
    Proof.CmacAes.Arm.ciph, Proof.CmacAes.Arm.ciphAt, Proof.CmacAes.Arm.W, Proof.CmacAes.Arm.R,
    Proof.CmacAes.Arm.St, Proof.CmacAes.Arm.Dp, Proof.CmacAes.Arm.N, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hL, State.withRegions_mem, State.callEntry_mem] at hpost
  have eK := keep (h.bk.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK1 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 240) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 240) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s.mem (State.addr K + BitVec.ofNat 64 256) 16 :=
    keep (h.bk.sub_right (Offset.sub_base (State.addr K) (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := keep h.bst (by decide)
  have eP := keep h.bp (by have := h.len; omega)
  rw [eK, eK1, eK2, eSt, eP] at hpost
  rw [hm]
  exact hpost

theorem fin_rel {K St P S sp₀ : BitVec 32} {L R : Nat} {Pr : State → State → Prop}
    (h : ∀ s₁ s₂, Pr s₁ s₂ → FArgs s₁ K St P S L R ∧ FArgs s₂ K St P S L R ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa Pr Impl.AesSiv.Arm.finFrame fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.finalizeArm) (rd := [⟨State.addr K, 272⟩,
    ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := fWr St S)
    (fun _ hs => Proof.CmacAes.Arm.finalize_wp hs) Proof.CmacAes.Arm.finalize_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : fRd s₁ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₁]
  have r₂ : fRd s₂ K P L = [⟨State.addr K, 272⟩, ⟨State.addr P, L⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [fRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r12) (rb := .lr) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r12) (rb := .lr) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega, by have := h₂.hsp; omega, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.finalizeArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesSiv.Arm

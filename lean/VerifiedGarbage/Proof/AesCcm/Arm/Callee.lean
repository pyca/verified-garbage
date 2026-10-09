import VerifiedGarbage.Proof.AesCcm.Arm.Env
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call
import VerifiedGarbage.Proof.AesGcm.Arm.Callee

/-!
# AES-CCM on ARMv7: the calls of `vg_cmac_aes_update`

Untrusted: everything here is checked by Lean. As streaming AES-CMAC's
(`Proof/CmacAes/Stream/Arm/Call.lean`, `upd_call`, `upd_rel`), but with the
two stack arguments pushed from `r12` (the number of blocks) and `lr` (the
working space), which `seal` and `open` do not keep across calls: what a
call needs (`UArgs`), what it leaves (`UPost`), and that two calls with the
same arguments leak the same (`upd_rel`). The calls of `vg_aes_ctr32` are
AES-GCM's (`Proof.AesGcm.Arm.ctr_call`, `ctr_rel`).
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.CmacAes.Stream.Arm (view blw16 view_gpr view_sp view_arg0 view_arg1 view_argAddr view_blw spA
  slot_sub push_frame cov_push covW_push WP.frameCallF RelCT.frameCall stackUse_update uRd uWr)
open VG.Proof.CmacAes.Arm (toNat_rounds)

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`, with `n` in `r12` and `S` in `lr`, to push. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 32
  hsp : 16 ≤ s.sp.toNat
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  dc : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (blw16 s).Disjoint ⟨State.addr W, 240⟩
  bd : (blw16 s).Disjoint ⟨State.addr D, 16 * n⟩
  bc : (blw16 s).Disjoint ⟨State.addr C, 16⟩
  bs : (blw16 s).Disjoint ⟨State.addr S, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr S, 2176⟩, blw16 s] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (State.addr C) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (State.addr W) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (State.addr C) 16) (Spec.Cmac.blocksAt s.mem (State.addr D) 16 n)

theorem UArgs.pre {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    Proof.CmacAes.Arm.updateArm.pre (view .r12 .lr s (uRd s W D n) (uWr C S)) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega_arith)
  have hb := view_blw (ra := .r12) (rb := .lr) (rd := uRd s W D n) (wr := uWr C S) h.hsp
  have hslot : Region.Sub ⟨stackArgAddr (view .r12 .lr s (uRd s W D n) (uWr C S)) 0, 8⟩ (blw16 s) := by
    rw [view_argAddr h.hsp]; exact slot_sub
  simp only [Proof.CmacAes.Arm.updateArm, view_arg0 h.hsp, view_arg1 h.hsp, view_argAddr h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hR, hN, State.withRegions_rd, State.withRegions_wr]
  rw [view_argAddr h.hsp] at hslot
  have hspv := spA h.hsp
  have := h.hsp
  refine ⟨rfl, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, (h.bc.sub_left slot_sub).symm,
    (h.bs.sub_left slot_sub).symm, h.bw.sub_left hb, h.bd.sub_left hb, h.bc.sub_left hb, h.bs.sub_left hb,
    h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
  · rw [view_sp, hspv]; omega_arith
  · rw [view_sp, hspv]; have := s.sp.isLt; omega_arith

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.AesCcm.Arm.updFrame s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := h.hn; omega_arith)
  refine WP.frameCallF (k := Proof.CmacAes.Arm.updateArm) (fun _ hs => Proof.CmacAes.Arm.update_wp hs)
    stackUse_update rfl h.hsp h.pre (cov_push h.hsp h.reads h.writes) (covW_push h.writes) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.bc
      · exact h.bs) fun s' s₂ hrd hwr hsp hf hcs hm hpost => ?_
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  have fP := push_frame h.hsp .r12 .lr
  have keep : ∀ {p : Addr} {k : Nat}, (blw16 s).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem p k = Spec.Aes.bytesAt s.mem p k := fun hd hk =>
    Proof.Cmac.bytesAt_frame fP (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact (hd.sub_left slot_sub).symm) hk
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_arith
  simp only [Proof.CmacAes.Arm.updateArm, Proof.CmacAes.Arm.ciphAt, view_arg0 h.hsp,
    view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide), view_gpr .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, h.r12, hR, hN, State.withRegions_mem, State.callEntry_mem] at hpost
  rw [hm, hpost, keep (h.bw.sub_right (Region.sub_prefix hRb)) (by omega_arith), keep h.bc (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep (h.bd.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega_arith

theorem upd_rel {W C D S sp₀ : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀) :
    RelCT isa P Impl.AesCcm.Arm.updFrame fun _ _ => True := by
  refine RelCT.frameCall (k := Proof.CmacAes.Arm.updateArm) (rd := [⟨State.addr W, 240⟩,
    ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩]) (wr := uWr C S)
    (fun _ hs => Proof.CmacAes.Arm.update_wp hs) Proof.CmacAes.Arm.update_ct rfl fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have r₁ : uRd s₁ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₁]
  have r₂ : uRd s₂ W D n = [⟨State.addr W, 240⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr sp₀ - 8, 8⟩] := by
    rw [uRd, e₂]
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [r₁] at p₁
  rw [r₂] at p₂
  have c₁ := cov_push (ra := .r12) (rb := .lr) h₁.hsp h₁.reads h₁.writes
  have c₂ := cov_push (ra := .r12) (rb := .lr) h₂.hsp h₂.reads h₂.writes
  rw [e₁] at c₁
  rw [e₂] at c₂
  have := h₁.hsp
  refine ⟨e₁.trans e₂.symm, by omega_arith, by have := h₂.hsp; omega_arith, p₁, p₂, ?_, c₁, covW_push h₁.writes, c₂,
    covW_push h₂.writes⟩
  simp only [Proof.CmacAes.Arm.updateArm, view_sp, view_arg0 h₁.hsp, view_arg1 h₁.hsp, view_arg0 h₂.hsp,
    view_arg1 h₂.hsp, view_gpr .r0 (by decide), view_gpr .r1 (by decide), view_gpr .r2 (by decide),
    view_gpr .r3 (by decide), h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12,
    h₂.lr, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCcm.Arm

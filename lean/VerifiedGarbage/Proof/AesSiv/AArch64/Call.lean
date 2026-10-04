import VerifiedGarbage.Proof.AesSiv.AArch64.Env

/-!
# AES-SIV on AArch64: calling `vg_cmac_aes_finalize` with any subkeys

`vg_cmac_aes_finalize`'s contract gives the CMAC of the message only when the
subkeys in its `key` are those of the key schedule's cipher. Its code needs
no such thing: it computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key`
holds, for the chaining value `C` at `state` and the last block `Mₙ` of
§6.2 step 4 (`finalize_raw_wp`). AES-SIV's contracts compute with the
subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use this
(`finr_call`), with `WP.call` from this correctness of the same code.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (FPre finPre_wp ctr_call finalizeAArch64 mn restoreF_ok wr_in finalize_keepsV
  callEntry_x0 callEntry_x1 callEntry_x2 callEntry_x3 callEntry_x4 toNat_rounds)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs finalize_noFrames toNat_ofNat)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawAArch64 : Contract isa where
  pre := finalizeAArch64.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
      Spec.Cmac.aesWith (s.gpr .x1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
        (Spec.Cmac.xor (mn s.mem (s.gpr .x0) (s.gpr .x3) (s.gpr .x4).toNat)
          (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16))
  pub := finalizeAArch64.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa (Impl.CmacAes.AArch64.finalize v.callee) s₀
      fun s' => GprAbi s₀ s' ∧ finalizeRawAArch64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .x0 = W at hp
  generalize hSt : s₀.gpr .x2 = St at hp
  generalize hP : s₀.gpr .x3 = P at hp
  generalize s₀.gpr .x5 = S at hp
  generalize hL : (s₀.gpr .x4).toNat = L at hp
  generalize hR' : (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), h₁.x19]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, mem₃⟩ := restoreF_ok s₂ x19₂
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2072) (n := 8) (by decide)))
    (by rw [rdwr₂]; exact wr_in (hp.inScr (d := 2064) (n := 8) (by decide)))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.st_scr.symm.sub_left (FPre.scrD (by omega)))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2064 (by decide) (by decide), h₁.slot19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2072 (by decide) (by decide), h₁.slot30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · show Spec.Aes.bytesAt s₃.mem (s₀.gpr .x2) 16 = _
    rw [hW, hSt, hP, hL, hR', mem₃, h₂.out, sch, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawAArch64.pre s) :
    ∃ t s', Exec isa (Impl.CmacAes.AArch64.finalize v.callee) s t s' ∧ abiPreserved s s' ∧
      finalizeRawAArch64.post s s' :=
  WP.withPreservedV (finalize_raw_wp v hs) (finalize_keepsV v)

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem St 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
      (Spec.Cmac.xor (mn s.mem K P L) (Spec.Aes.bytesAt s.mem St 16))

theorem finr_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) s (FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeRawAArch64) (finalize_raw_correct v) h.pre h.reads h.writes ?_
    (finalize_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeRawAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hL] at hpost
  exact hpost

end VG.Proof.AesSiv.AArch64

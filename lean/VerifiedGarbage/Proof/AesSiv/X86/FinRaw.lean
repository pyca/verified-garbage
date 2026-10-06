import VerifiedGarbage.Proof.CmacAes.Stream.X86.Call
import VerifiedGarbage.Proof.AesSiv.X86.Contract

/-!
# AES-SIV on x86: calling `vg_cmac_aes_finalize` with any subkeys

Untrusted: everything here is checked by Lean. `vg_cmac_aes_finalize`'s
contract gives the CMAC of the message only when the subkeys in its `key`
are those of the key schedule's cipher. Its code needs no such thing: it
computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key` holds, for the chaining
value `C` at `state` and the last block `Mₙ` of §6.2 step 4
(`finalize_raw_wp`, as x86-64's AES-SIV has it). AES-SIV's contracts compute
with the subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use
this (`finr_call`), with `WP.callWith` from this correctness of the same
code.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.CmacAes.X86
open VG.Proof.CmacAes.Stream.X86 (FArgs rs6 hrs6 fin_nosp fin_stack entry_bytes eq_ofNat fRd fWr)
open VG.Impl.CmacAes.X86 (finalize finPre saved)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawX86 : Contract isa where
  pre := finalizeX86.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 16 =
      Spec.Cmac.aesWith (arg s 1).toNat (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
        (Spec.Cmac.xor (mn s) (Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16))
  pub := finalizeX86.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ finalizeRawX86.post s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have cA := hp.cA
  unfold finalize
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = stkR s₀ := by rw [h₁.esp]; exact hp.below_eq
  have f₁ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
  have f₂ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    refine f₁.trans (fr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have big₁ := UPre.big_of f₁
  have big₂ := UPre.big_of f₂
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp]
  have rdwr₂ : s₂.rd ++ s₂.wr = [keyR s₀, lastR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s₂.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := saved_bound _ hrd
    rw [f₂.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide), savedMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame big₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.b_key.symm.sub_left (Region.sub_prefix (by omega))) (by omega)
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [hrw₂]; exact hp.arg_in (by decide)) (hp.arg_keep big₂ (by decide))
    fun s₃ u₃ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₃.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₃.gpr, u₃.mem]; exact sl p.1 p.2 hp') fun s₄ r₄ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₃.gpr, u₃.rd, u₃.wr, rdwr₂]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₄.abi (by decide) (by decide) (by rw [u₃.other _ (by decide), esp₂]), ?_⟩, ?_⟩
  · rw [r₄.mem, u₃.mem]
    have rs : (retR s₀).Disjoint (stkR s₀) := by
      have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
      rw [add0] at this
      exact this.symm
    exact big₂.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_scr
      · exact rs) (by decide)
  · show Spec.Aes.bytesAt s₄.mem ((St s₀).setWidth 64) 16 = _
    rw [r₄.mem, u₃.mem, h₂.out, sch, cA, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawX86.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeRawX86.post s s' :=
  finalize_raw_wp v hs

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (St.setWidth 64) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (K.setWidth 64) (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (P.setWidth 64) L))
        (Spec.Aes.bytesAt s.mem (St.setWidth 64) 16))

theorem finr_call (v : Ctr32Impl) {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa (Impl.CmacAes.Stream.X86.call6 ("vg_cmac_aes_finalize" ++ v.suffix) (finalize v.callee)) s
      (FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := rs6) (k := finalizeRawX86) (fun _ hs => finalize_raw_wp v hs) (fin_nosp v) (by simp)
    hrs6 (by rw [(fin_stack v)]; simp only [List.length_cons, List.length_nil]; omega)
    ⟨h.callPre.pre, h.callPre.cov, h.callPre.covw⟩
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [(fin_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : Addr} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed rs6 s).callEntry.mem p k = Spec.Aes.bytesAt s.mem p k :=
    fun hd hk => entry_bytes h.fit hrs6 (by simp) he hd hk
  simp only [finalizeRawX86, mn, W, Dp, N, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hL,
    m₂] at post
  have eK := keep (h.bK.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK1 := keep (p := K.setWidth 64 + BitVec.ofNat 64 240) (k := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 := keep (p := K.setWidth 64 + BitVec.ofNat 64 256) (k := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := keep h.bSt (by decide)
  have eP := keep h.bP (by omega)
  rw [eK, eK1, eK2, eSt, eP] at post
  exact post

end VG.Proof.AesSiv.X86

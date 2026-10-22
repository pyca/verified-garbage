module

import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Loops
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Setup
public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group

/-! # CBC decryption, including the unchanged scratch buffer -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem data_size {s₀ : State} (hp : UPre s₀) : 16*N s₀ < 2^64 := by
  refine Nat.lt_of_not_le fun hc => hp.data_scr (S s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (S s₀-Dp s₀).isLt
  omega

theorem initial {s₀ s : State} (hK : DKeys (R s₀) (wK s₀) s)
    (h2 : s.gpr .x2=Dp s₀) (h3 : s.gpr .x3=s₀.gpr .x4) (h11 : s.gpr .x11=Iv s₀)
    (h31 : s.v .v31=s₀.mem.readW (Iv s₀) 128) (hm : s.mem=s₀.mem)
    (hrd : s.rd=s₀.rd) (hwr : s.wr=s₀.wr) : Inv s₀ 0 0 s := by
  refine ⟨Nat.zero_le _,hK,by simpa [blk] using h2,by simpa using h3,h11,h31,?_,?_,hrd,hwr⟩
  · intro i _; simp [hm]
  · rw [hm]; exact Frame.refl _ _

theorem finish_iv {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block [.strq .v31 .x11 0]) s fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_,exec_strq (off := 0) (t := .v31) (n := .x11) (by decide) (by
    rw [hI.x11,BitVec.add_zero,hI.wr,hp.wr]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  simp only [hI.x11,BitVec.add_zero]
  have hf : Frame [ivR s₀] s.mem (s.mem.write (Iv s₀) 16 (s.v .v31)) :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd := ecbInv_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.symm) (data_size hp) hI.data
  have hi : Spec.Aes.bytesAt (s.mem.write (Iv s₀) 16 (s.v .v31)) (Iv s₀) 16 =
      Spec.Cbc.next (iv0 s₀) (blks s₀) := by
    rw [bytesAt_toList,← st_readW]
    have hm : (s.mem.write (Iv s₀) 16 (s.v .v31)).readW (Iv s₀) 128 = s.v .v31 :=
      Mem.readW_writeW_self s.mem (Iv s₀) 16 (s.v .v31) (by decide)
    rw [hm,hI.chain,chaining_bytes _ _ (Nat.le_refl _),List.take_of_length_le (by rw [length_blocksAt])]
  exact ⟨⟨data_done hd,hi⟩,(hI.frame.mono (by regions_sub)).trans (hf.mono (by regions_sub))⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.body (R s₀)) s₀ fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Decrypt.body
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨hK,_,h2,h3,h11,h31,hm,hrd,hwr⟩ => ?_)
  have hi := initial hK h2 h3 h11 h31 hm hrd hwr
  exact WP.seq (WP.mono (loops_ok hp hi) fun _ hI => finish_iv hp hI)

theorem code_ok {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.AesCbc.AArch64.Decrypt.code s₀ fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Decrypt.code
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 10) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 12) (by decide),WP.block_nil ?_⟩
  let s := (s₀.write .x .x9 (s₀.gpr .x1-10)).write .x .x10 (s₀.gpr .x1-12)
  have hs : UPre s := ⟨hp.rd,hp.wr,hp.sch_iv,hp.sch_data,hp.sch_scr,
    hp.iv_data,hp.iv_scr,hp.data_scr,hp.iv_wrap,hp.data_wrap,hp.scr_wrap,hp.rounds⟩
  have hR : R s=R s₀ := rfl
  have hpost : ∀ t, (cbcAArch64 false).post s t=(cbcAArch64 false).post s₀ t := fun _ => rfl
  have hb : WP isa (Impl.AesCbc.AArch64.Decrypt.body (R s₀)) s (fun t =>
      (cbcAArch64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem) := by
    have h := body_ok hs
    rw [hR] at h
    exact WP.mono h fun t ht => by rw [hpost t] at ht; exact ht
  have hx9 : s.gpr .x9 = BitVec.ofNat 64 (R s₀)-10 := by simp [s,State.write,R]
  have hx10 : s.gpr .x10 = BitVec.ofNat 64 (R s₀)-12 := by simp [s,State.write,R]
  change WP isa (.ite (.zero .x .x9) _ _) s _
  obtain hr | hr | hr := hp.rounds
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => by cases h)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · simpa only [hr] using hb
  · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · refine WP.ite true ?_ (fun _ => ?_) (fun h => by cases h)
      · simp [eval,State.read,hx10,hr] <;> decide +kernel
      · simpa only [hr] using hb
  · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
    · simp [eval,State.read,hx9,hr] <;> decide +kernel
    · refine WP.ite false ?_ (fun h => by cases h) (fun _ => ?_)
      · simp [eval,State.read,hx10,hr] <;> decide +kernel
      · simpa only [hr] using hb

end VG.Proof.AesCbc.AArch64.Decrypt

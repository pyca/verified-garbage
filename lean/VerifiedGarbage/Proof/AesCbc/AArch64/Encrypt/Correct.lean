module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Loops
import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.Result
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Correct
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! CBC encryption correctness and the complete memory frame. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem finish_iv {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) s) :
    WP isa (.block [.vop (.logic .eor .v31 .v31 .v30),.strq .v31 .x11 0]) s fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  let u := s.setV .v31 (s.v .v31 ^^^ s.v .v30)
  have he : exec (.vop (.logic .eor .v31 .v31 .v30)) s=some u := rfl
  refine ⟨_,he,?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_strq (off:=0) (t:=.v31) (n:=.x11) (by decide) (by
    change InRegions s.wr (s.gpr .x11+BitVec.ofNat 64 0) 16
    rw [hI.env.iv,BitVec.add_zero,hI.env.wr,hp.wr]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  have hptr : u.gpr .x11=Iv s₀ := hI.env.iv
  have hv : u.v .v31=chain s₀ (N s₀) := hI.chain
  simp only [hptr,BitVec.add_zero]
  have hf : Frame [ivR s₀] s.mem (s.mem.write (Iv s₀) 16 (u.v .v31)) :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd := ecbInv_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp.iv_data.symm) (Decrypt.data_size hp) hI.data
  have hi : Spec.Aes.bytesAt (s.mem.write (Iv s₀) 16 (u.v .v31)) (Iv s₀) 16=
      Spec.Cbc.next (iv0 s₀)
        (Spec.Cbc.encrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)) := by
    rw [bytesAt_toList,←st_readW]
    have hm : (s.mem.write (Iv s₀) 16 (u.v .v31)).readW (Iv s₀) 128=u.v .v31 :=
      Mem.readW_writeW_self s.mem (Iv s₀) 16 (u.v .v31) (by decide)
    rw [hm,hv,←(chain_blocks s₀ (N s₀) (Nat.le_refl _)).2]
    change Spec.Cbc.next _ (outK (cbcMode true) s₀ (N s₀))=_
    rw [outK,List.take_of_length_le (by rw [length_blocksAt])]
    rfl
  exact ⟨⟨data_done hd,hi⟩,(hI.env.frame.mono (by regions_sub)).trans (hf.mono (by regions_sub))⟩

theorem body_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (Impl.AesCbc.AArch64.Encrypt.body (R s₀)) s₀ fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  rw [Impl.AesCbc.AArch64.Encrypt.body]
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨he,h2,h3,hch,hm⟩ => ?_)
  exact WP.seq (WP.mono (middle_ok hp he h2 h3 hch hm) fun _ hi => finish_iv hp hi)

theorem code_ok {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.AesCbc.AArch64.Encrypt.code s₀ fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem := by
  unfold Impl.AesCbc.AArch64.Encrypt.code
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 10) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 12) (by decide),WP.block_nil ?_⟩
  let s := (s₀.write .x .x9 (s₀.gpr .x1-10)).write .x .x10 (s₀.gpr .x1-12)
  have hs : UPre s := ⟨hp.rd,hp.wr,hp.sch_iv,hp.sch_data,hp.sch_scr,
    hp.iv_data,hp.iv_scr,hp.data_scr,hp.iv_wrap,hp.data_wrap,hp.scr_wrap,hp.rounds⟩
  have hR : R s=R s₀ := rfl
  have hpost : ∀ t, (cbcAArch64 true).post s t=(cbcAArch64 true).post s₀ t := fun _ => rfl
  have hb : WP isa (Impl.AesCbc.AArch64.Encrypt.body (R s₀)) s (fun t =>
      (cbcAArch64 true).post s₀ t ∧ Frame [ivR s₀,dataR s₀] s₀.mem t.mem) := by
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

end VG.Proof.AesCbc.AArch64.Encrypt

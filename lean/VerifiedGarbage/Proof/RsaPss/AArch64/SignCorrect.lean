import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec

/-!
# RSASSA-PSS signing on AArch64: correctness

Zeros to `out` (`fail_ok`); the checks and the encoding with the private
operation, or `fail` (`body_ok`), which is `RsaPss.sign` (`signOut_eq`);
the restores (`restore_ok`); the whole function (`code_ok`).
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.RsaPkcs1Sig.AArch64 (psLoop)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov fill_ok PrivChecked)
open VG.Proof.RsaPkcs1Sig (bytesAt_writeBytes frame_writeBytes)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV smear_ok emLen_ok saltFits_ok)

theorem oR_eq {D K : Nat} {s : State} (hp : PreS D K s) :
    (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = oR s := by
  show (⟨s.gpr .x0, (s.gpr .x3).toNat⟩ : Region) = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  rw [hp.ol]

/-- Zeros to `out`, and 0 returned. -/
theorem fail_ok {D K : Nat} {s t : State} (hp : PreS D K s) (hm : Mid s t) (h23 : t.gpr .x23 = s.gpr .x3) :
    WP isa signFail t fun t' => Mid s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .x0) (s.gpr .x3).toNat ((t'.gpr .x0).setWidth 32) .invalid := by
  have hk1 := hp.k1; have hk2 := hp.k2
  unfold signFail ld
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x14, .x13, .x15] t u ∧ u.gpr .x14 = s.gpr .x0 ∧
      u.gpr .x13 = BitVec.ofNat 64 (s.gpr .x3).toNat ∧ (u.gpr .x15).setWidth 8 = 0) ?_
    fun u ⟨O, h14, h13, h15⟩ => ?_)
  · have hr : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 sOut) 8 := by
      rw [hm.sp, hm.rd, hm.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
    refine wp_ldrSp (by decide) hr fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_nil
      ⟨(o₁.trans (o₂.trans o₃)).mono, ?_, ?_, ?_⟩
    · rw [o₃.get .x14, o₂.get .x14, e₁, hm.sp]; exact hm.fr.rs (.x0, sOut) (by simp [regSlots])
    · rw [o₃.get .x13, e₂, o₁.get .x23, h23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [e₃]; rfl
  have hO := oR_eq hp
  refine WP.seq (WP.mono (fill_ok (p := s.gpr .x0) (n := (s.gpr .x3).toNat) (b := 0) (by omega) (by omega) h14 h13
    h15 fun i hi => ?_) fun v ⟨kv, mv⟩ => ?_)
  · rw [O.wr, hm.wr]
    exact ⟨_, List.mem_cons_of_mem _ hp.hwo, by
      rw [← hO]; exact Offset.contains_base _ (by omega) (by have := hp.wo; rw [hp.ol] at this; omega)⟩
  refine wp_movz fun w o e => wp_nil ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_⟩, by rw [e]; rfl, ?_⟩
  · rw [o.sp, kv.sp, O.sp, hm.sp]
  · rw [o.rd, kv.rd, O.rd, hm.rd]
  · rw [o.wr, kv.wr, O.wr, hm.wr]
  · rw [o.vcs r hr, kv.vcs r hr, O.vcs r hr, hm.v r hr]
  · have fw : Frame [⟨s.gpr .x0, (s.gpr .x3).toNat⟩] u.mem w.mem := by
      rw [o.mem, mv]; have := frame_writeBytes u.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0)
      rwa [List.length_replicate] at this
    rw [hO] at fw
    exact (O.mem ▸ hm.fr).frame fw
      (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.ko.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))))
      (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (hp.ko.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))))
  · rw [o.mem, mv]
    have := bytesAt_writeBytes u.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

end VG.Proof.RsaPss.AArch64.Sgn

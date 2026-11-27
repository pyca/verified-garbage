module

public import VerifiedGarbage.Proof.AesGcm.Arm.Contiguous.Payload
public import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt
import VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! The contiguous seal authenticates the ciphertext written by the payload. -/

@[expose] public section
namespace VG.Proof.AesGcm.Arm.Contiguous
open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Impl.AesGcm.Arm.Contiguous
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm

private theorem extendSafe {r stk : Region} {regions : List Region}
    (safe : ∀ q ∈ regions, r.Disjoint q) (stack : r.Disjoint stk) :
    ∀ q ∈ regions ++ [stk], r.Disjoint q := by
  intro q h
  rcases List.mem_append.mp h with old | tail
  · exact safe q old
  · exact List.mem_singleton.mp tail ▸ stack

abbrev source (b : State) := bytesAt b.mem (State.addr (arg b 5)) (arg b 3).toNat

structure Layout (b : State) : Prop where
  basic : onePre 7 6 b
  writable : (⟨State.addr (arg b 2), (arg b 3).toNat⟩ : Region) ∈ b.wr
  readable : DataOk (oSt b 6) (arg b 6) b.sp b (arg b 5) (arg b 3).toNat
  mode : CrMode true (b.gpr .r0) (oSt b 6) (arg b 6) b.sp (arg b 5) (arg b 2) (arg b 3).toNat
  tagW : (⟨State.addr (arg b 4), 16⟩ : Region) ∈ b.wr
  tagDst : (⟨State.addr (arg b 2), (arg b 3).toNat⟩ : Region).Disjoint ⟨State.addr (arg b 4), 16⟩
  tagWork : (⟨State.addr (arg b 4), 16⟩ : Region).Disjoint ⟨State.addr (arg b 6), 2560⟩
  tagFit : (arg b 4).toNat + 16 ≤ 2 ^ 32

theorem body_wp [VG.Proof.Gcm.Arm.GhashLaw] {b : State} (h : Layout b) :
    WP isa body b fun z => abiPreserved b z ∧
      encryptWith (sealCipher b) (sealH b) 16 (sealNonce b) (source b) (sealAad b) =
      (sealData b z, bytesAt z.mem (State.addr (arg b 4)) 16) := by
  have one := h.basic
  have lay := oneLay one
  obtain ⟨_, spFit, stackCtx, stackSt, stackWork, _, _⟩ := h.mode
  have rounds := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have argFit := one.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (one1_wp one (by decide) (by decide) fun u entry => WP.seq ((oneAad_ok one (by decide) entry).mono fun v aad => ?_))
  obtain ⟨k7, env⟩ := aad.env
  let counter := inc32 (j0 (sealH b) (sealNonce b))
  have dst := one_dataW one h.writable aad.args k7 (b.gpr .r1)
  have payload := payload_wp (icb := counter) lay env rounds aad.args argFit one.1.2.2.2
    (h.readable.of_eq aad.args.rd aad.args.wr) dst h.mode
  have combined := WP.with_rdwr payload
  rw [WP.seq_iff] at combined
  refine WP.seq (combined.mono fun s crypt => WP.seq (crypt.mono fun z ⟨out, rd, wr, sp⟩ => ?_))
  have initSafe {r : Region} (w : r.Disjoint ⟨State.addr (arg b 6), 2560⟩)
      (stack : (below b.sp).Disjoint r) :
      ∀ q ∈ [savedR (arg b 6)] ++ j0Frame (oSt b 6) (arg b 6) b.sp, r.Disjoint q := by
    intro q hq
    rcases List.mem_append.mp hq with first | rest
    · exact List.mem_singleton.mp first ▸ w.sub_right (Lay.wSub (by decide))
    · exact one_dataJ0 one w stack q rest
  have initFrame := (entry.frame.mono fun r hr => List.mem_append_left (j0Frame (oSt b 6) (arg b 6) b.sp) hr).trans
    (aad.frame.mono fun r hr => List.mem_append_right [savedR (arg b 6)] hr)
  have cipher := ciph_keep initFrame (initSafe lay.cw' lay.kc) rounds
  have plain := bytesAt_frame initFrame (initSafe h.readable.w h.readable.stk) (Nat.le_of_lt h.readable.lt)
  have cSafe := extendSafe (ctx_crFrame lay dst) stackCtx.symm
  have stateSafe (d k : Nat) (bound : d+k ≤ 48) :=
    extendSafe (stp_crFrame lay dst (d:=d) (k:=k) bound)
      ((stackSt.sub_right (Lay.stSub (by omega : d+k≤80))).symm)
  have savedSafe := extendSafe (saved_crFrame lay dst)
    ((stackWork.sub_right (Lay.wSub (by decide : 128+36≤2560))).symm)
  have argSafe : ∀ r ∈ crFrameG true (oSt b 6) (arg b 6) b.sp (arg b 2) (arg b 3).toNat,
      (args b 7).Disjoint r := by
    apply extendSafe _ (below12_args b argFit spFit).symm
    intro r hr
    simp only [crFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact one.2.1.2.2 _ h.writable
    · rw [oSt_addr one, add_ofNat_assoc]
      exact (one.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub (by decide))).symm
    · exact (one.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args b argFit).symm
  have c0 := Proof.Gcm.ctr_zero v.mem _ (State.addr (oSt b 6) + 64#64)
    (ciphOf v.mem (State.addr (b.gpr .r0)) (b.gpr .r1).toNat) aad.cb
  have rem := Nat.mod_lt (sealAad b ++ zeros (padLen (sealAad b).length)).length (by decide : 0 < 16)
  have ready : TagReady 7 6 b z (source b) := by
    refine ⟨⟨_, out.env⟩, aad.args.frame argFit out.frame argSafe ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_,
      (entry.saved.frame aad.frame (saved_j0Frame lay)).frame out.frame savedSafe⟩
    · exact out.env.sp.trans env.sp.symm
    · exact rd
    · exact wr
    · rw [blockAt_frame out.frame (fun r hr => (cSafe r hr).sub_left (Lay.ctxSub (by decide)))]; exact aad.hH
    · exact aad.abs.congr (blockAt_frame out.frame (stateSafe 16 16 (by decide)))
        (bytesAt_frame out.frame (stateSafe 32 _ (by change 32 + (sealAad b ++ zeros (padLen (sealAad b).length)).length % 16 ≤ 48; omega)) (by omega))
    · rw [blockAt_frame out.frame (fun r hr => by simpa only [BitVec.add_zero] using stateSafe 0 16 (by decide) r hr)]; exact aad.j
    · exact (ciph_frame out.frame cSafe rounds).trans cipher
    · rw [sealData, out.out c0, Proof.Gcm.gctr_eq, cipher, plain]
  exact seal_tag_wp one (by decide) h.tagW h.tagDst h.tagWork h.tagFit ready

end VG.Proof.AesGcm.Arm.Contiguous

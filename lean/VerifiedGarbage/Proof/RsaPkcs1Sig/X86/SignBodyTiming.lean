module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStages
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEraseTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCallPublic
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish

/-! # Signing traces agree for independent secret digests and CRT components -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode sp_agree pair_seq_ct)

theorem privateCall_relCT (v : CrtImpl) {g : Geometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => CallReady g bs1 s ∧ CallReady g bs2 t)
      (.call (privName v) (privCode v)) (fun _ _ => True) := by
  have verified := VG.Proof.Rsa.X86.PrivChecked.code_verified v
  apply RelCT.call verified.1 verified.2.1 (privateRd g) (privateWr g)
  intro s t h
  exact ⟨privateCall_pre h.1.context h.1.args, privateCall_pre h.2.context h.2.args,
    privateCall_pub h.1.context h.2.context h.1.args h.2.args nb eb,
    (privateCovers h.1.context).1, (privateCovers h.1.context).2,
    (privateCovers h.2.context).1, (privateCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

structure Compared (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop extends EncodeDone g bs s where
  flag : s.zf = some (s.gpr .eax == 0)

theorem compare_ready {g : Geometry} {bs : Fin 8 → List Byte} {s : State} (h : EncodeDone g bs s) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s (Compared g bs) := by
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨h.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (by rw [F.gpr]), ?_⟩, ?_⟩
  · simpa only [Encoded, F.gpr, F.mem] using h.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem cmp_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .eax]))
    (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) :=
  (checkedBlockInvariant rfl rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem callThenWipe_relCT (v : CrtImpl) {g : Geometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => Context g bs1 s ∧ Context g bs2 t)
      (.seq (.block callArgs) (.seq (.call (privName v) (privCode v)) wipe)) (fun _ _ => True) := by
  apply pair_seq_ct (callArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (privateCall_relCT v nb eb) (fun _ h => privateCall_ready v h)
    (fun _ h => privateCall_ready v h) wipe_relCT

theorem afterEnc_relCT (v : CrtImpl) {g : Geometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => EncodeDone g bs1 s ∧ EncodeDone g bs2 t)
      (afterEnc (privName v) (privCode v)) (fun _ _ => True) := by
  unfold afterEnc
  apply pair_seq_ct (cmp_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.context.sp.trans h.2.context.sp.symm
    · exact encoded_status h.1 h.2)) (fun _ _ _ => trivial))
    (fun _ h => compare_ready h) (fun _ h => compare_ready h)
  apply RelCT.ite
  · intro s t h
    change s.zf = t.zf
    rw [h.1.flag, h.2.flag, encoded_status h.1.toEncodeDone h.2.toEncodeDone]
  · exact zeroOut_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · exact (callThenWipe_relCT v nb eb).mono
      (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)

theorem encodeReady_agree {g : Geometry} {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : EncodeReady g bs1 s) (ht : EncodeReady g bs2 t) : VG.X86.Taint.Agree encodeTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.len.trans ht.len.symm
  · exact hs.hash.trans ht.hash.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem body_relCT (v : CrtImpl) {g : Geometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => Context g bs1 s ∧ Context g bs2 t)
      (body (privName v) (privCode v)) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (encArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => encArgs_ready h) (fun _ h => encArgs_ready h)
  exact pair_seq_ct (encode_relCT.mono (fun _ _ h => encodeReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => encode_done h) (fun _ h => encode_done h) (afterEnc_relCT v nb eb)

end VG.Proof.RsaPkcs1Sig.X86.Sgn

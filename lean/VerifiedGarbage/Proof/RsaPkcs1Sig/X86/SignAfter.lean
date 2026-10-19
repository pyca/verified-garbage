module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipe
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.PrivContext

/-! # Compose checked signing or public encoding rejection with output clearing -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Sign
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

def result (g : Geometry) (bs : Fin 8 → List Byte) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Sig.signId (bs 0) (bs 1) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7) g.hash.toNat (bs 2)

theorem result_eq {g : Geometry} {bs : Fin 8 → List Byte} (length : (bs 0).length = g.length) :
    result g bs = match encodeId g.hash (bs 2) g.length with
      | none => .invalid
      | some em => Spec.Rsa.privateChecked (bs 0) (bs 1) em (bs 3) (bs 4) (bs 5) (bs 6) (bs 7) := by
  unfold result Spec.RsaPkcs1Sig.signId encodeId
  cases hh : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
  | none => rfl
  | some hv =>
    simp only [Option.bind_some]
    unfold Spec.RsaPkcs1Sig.sign
    rw [length]
    cases Spec.RsaPkcs1Sig.encode hv (bs 2) g.length <;> rfl

def clobbers : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

theorem outgoing_frame {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) {m : Mem} (F : Frame [⟨byteAddr g.stack, 80⟩] s.mem m) :
    Frame (bodyWrites g) s.mem m := F.sub (by
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [bodyWrites], h.outgoingSub⟩)

theorem callee_frame {g : Geometry} {m m' : Mem}
    (F : Frame (privateWr g ++ [g.calleeRegion]) m m') : Frame (bodyWrites g) m m' := F.sub (by
  intro r hr
  simp only [privateWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)

theorem afterEnc_ok (v : CrtImpl) {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (enc : Encoded g bs s) :
    WP isa (afterEnc (privName v) (privCode v)) s fun t => Context g bs t ∧
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax) (result g bs) ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t := by
  unfold afterEnc
  refine WP.seq (wp_cmpS rfl fun c C Z => WP.block_nil ?_)
  have hc := h.after (by rw [C.mem]; exact Frame.refl _ _) (C.keeps []) (by rw [C.gpr])
  have encC : Encoded g bs c := by simpa only [Encoded, C.gpr, C.mem] using enc
  cases encoded : encodeId g.hash (bs 2) g.length with
  | none =>
    have zero : c.gpr .eax = 0 := by simpa only [Encoded, encoded] using encC
    refine WP.ite true (by simp [eval, Z, show s.gpr .eax = 0 by rw [← congrFun C.gpr .eax]; exact zero]) (fun _ => ?_) (by simp)
    refine WP.mono (zeroOut_ok hc) ?_
    rintro t ⟨ht, B, A, F, K⟩
    refine ⟨ht, ?_, ?_, (C.keeps clobbers).trans (K.mono (by decide))⟩
    · rw [result_eq (h.sources 0).length, encoded]
      exact ⟨A, B⟩
    · rw [C.mem] at F
      exact F.sub (by intro r hr; obtain rfl := List.mem_singleton.mp hr
                      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)
  | some em =>
    obtain ⟨one, bytes⟩ : c.gpr .eax = 1 ∧ Spec.Rsa.bytesAt c.mem (byteAddr g.temporary) g.length = em := by
      simpa only [Encoded, encoded] using encC
    refine WP.ite false (by simp [eval, Z, show s.gpr .eax = 1 by rw [← congrFun C.gpr .eax]; exact one]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (callArgs_ok hc) ?_)
    rintro a ⟨ha, args, F, K⟩
    have retained : Spec.Rsa.bytesAt a.mem (byteAddr g.temporary) g.length = em := by
      exact (VG.Proof.Rsa.rsa_bytes_frame F (by have := h.valid.maxLength; omega)
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hc.temporaryArgs)).trans bytes
    refine WP.seq (WP.mono (private_call v ha args retained) ?_)
    rintro b ⟨hb, Fb, Kb, out⟩
    refine WP.mono (wipe_ok hb) ?_
    rintro t ⟨ht, _, ax, Ft, Kt⟩
    have output : Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
        Spec.Rsa.bytesAt b.mem (byteAddr g.output) g.length :=
      VG.Proof.Rsa.rsa_bytes_frame Ft (by have := h.valid.maxLength; omega)
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr
            exact (h.valid.stackOutput.sub_left h.valid.innerSub).symm)
    refine ⟨ht, ?_, ?_, (C.keeps clobbers).trans ((K.mono (by decide)).trans
      ((Kb.mono (by decide)).trans (Kt.mono (by decide))))⟩
    · rw [result_eq (h.sources 0).length, encoded]
      unfold PrivateOut at out
      rw [ax]
      cases r : Spec.Rsa.privateChecked (bs 0) (bs 1) em (bs 3) (bs 4) (bs 5) (bs 6) (bs 7) <;>
        simp only [r, Spec.Rsa.writtenOutcome] at out ⊢ <;> exact ⟨out.1, output.trans out.2⟩
    · have Fc := outgoing_frame hc F
      rw [C.mem] at Fc
      exact Fc.trans ((callee_frame Fb).trans (Ft.sub (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)))

end VG.Proof.RsaPkcs1Sig.X86.Sgn

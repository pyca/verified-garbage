module

public import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
public import VerifiedGarbage.Proof.Rsa.PrivCheckLogic32
public import VerifiedGarbage.Proof.Rsa.X86.PrivTailContext

/-! # Re-exponentiate, compare, and release only a checked private result -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem check_ok (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} (s : State)
    (h : PrivContext g bs s) :
    WP isa (check v.pcName v.pc v.pdName v.pd) s fun t => PrivContext g bs t ∧
      t.gpr .eax = (Rsa.checkResult ((s.gpr .eax).setWidth 64) (bs 0) (bs 1) (bs 2)
        (Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length)).setWidth 32 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
        (if Rsa.released ((s.gpr .eax).setWidth 64) (bs 0) (bs 1) (bs 2)
            (Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length)
          then Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length else List.replicate g.length 0) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold check
  refine WP.seq (WP.mono (precomputeArgs_ok s h) ?_)
  rintro s1 ⟨h1, args1, status1, frame1, rest1⟩
  refine WP.seq (WP.mono (pc_call v h1 args1) ?_)
  rintro s2 ⟨h2, frame2, rest2, pc⟩
  refine WP.seq (WP.mono (publicArgs_ok s2 h2) ?_)
  rintro s3 ⟨h3, args3, status3, keepStatus3, frame3, rest3⟩
  refine WP.seq (WP.mono (pd_call v h3 args3) ?_)
  rintro s4 ⟨h4, frame4, rest4, pd⟩
  have bound := h.valid.maxLength
  have fit : g.length < 2 ^ 64 := by omega
  have tempFit : candidateOffset + g.length ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes := by simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega
  have tempCall : ∀ r ∈ pdWr g ++ [g.calleeRegion], (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint r := by
    rw [temporary_region h.valid]
    exact innerSlice_pdCall h.valid (by decide : 40 ≤ candidateOffset) tempFit
  have m3 : Spec.Rsa.bytesAt s3.mem (byteAddr g.temporary) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length := by
    rw [rsa_bytes_frame frame3 fit (temporary_setup h.valid), rsa_bytes_frame frame2 fit (temporary_pcCall h.valid),
      rsa_bytes_frame frame1 fit (temporary_setup h.valid)]
  have m4 := (rsa_bytes_frame frame4 fit tempCall).trans m3
  have r1 : s4.mem.readW (byteAddr g.stack + BitVec.ofNat 64 crtStatusOffset) 32 = s.gpr .eax := by
    rw [status_frame frame4 (innerSlice_pdCall h.valid (by decide : 40 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)),
      keepStatus3, status_frame frame2 (status_pcCall h.valid (by decide : 24 ≤ crtStatusOffset) (by decide : crtStatusOffset + 4 ≤ 88))]
    exact status1
  have r3 : s4.mem.readW (byteAddr g.stack + BitVec.ofNat 64 precomputeStatusOffset) 32 = s2.gpr .eax := by
    rw [status_frame frame4 (innerSlice_pdCall h.valid (by decide : 40 ≤ precomputeStatusOffset) (by decide : precomputeStatusOffset + 4 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes))]
    exact status3
  have pre := wordsAt_frame frame3 (by simp only [Spec.Rsa.modulusWords]; omega)
    (precomputation_setup h.valid)
  have pcBit : match Spec.Rsa.publicPrecompute (bs 0) with
      | some _ => s2.gpr .eax = 1 | none => s2.gpr .eax = 0 := by
    cases hp : Spec.Rsa.publicPrecompute (bs 0) <;> simp only [PcOut, hp] at pc ⊢ <;> exact pc.1
  have pdBit : (Spec.Rsa.publicPrecompute (bs 0)).isSome = true →
      match Spec.Rsa.publicOpChecked (bs 0) (bs 1) (Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length) with
      | some y => s4.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s4.mem (byteAddr g.output) g.length = y
      | none => s4.gpr .eax = 0 := by
    intro somePre
    obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp somePre
    have pc := pc
    simp only [PcOut, hws] at pc
    have output := pd (bs 0) (h.sources 0).length (by rw [pre, pc.2]; exact hws)
    rw [m3] at output
    cases hp : Spec.Rsa.publicOpChecked (bs 0) (bs 1) (Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length) <;>
      simp only [hp, Spec.Rsa.written] at output ⊢
    · exact output.1
    · exact output
  have logic := check_logic32 (r1 := s.gpr .eax) (r2 := s4.gpr .eax) (r3 := s2.gpr .eax)
    (xb := bs 2) pcBit pdBit
  have accepted : tailAccepted s4 = decide (successBits (s4.gpr .eax) (s.gpr .eax) (s2.gpr .eax) = 1) := by
    unfold tailAccepted
    rw [h4.address (by decide : crtStatusOffset < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80),
      h4.address (by decide : precomputeStatusOffset < VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80), r1, r3]
  have equal : tailEqual s4 g.output (g.sources 2) g.length =
      decide (Spec.Rsa.bytesAt s4.mem (byteAddr g.output) g.length = bs 2) := by
    unfold tailEqual
    have inp : Spec.Rsa.bytesAt s4.mem (byteAddr (g.sources 2)) g.length = bs 2 := (h4.sources 2).bytes
    rw [inp]
  refine WP.mono (tail_ok s4 (h4.tailInput)) ?_
  rintro t ⟨status, output, cleared, frame5, rest5⟩
  have bodyFrame := (frame1.sub setupWrites_sub).trans
    ((frame2.sub (calleeWrites_sub (pcWrites_sub h.valid))).trans
      ((frame3.sub setupWrites_sub).trans ((frame4.sub (calleeWrites_sub pdWrites_sub)).trans
        (frame5.sub (tailWrites_sub h.valid)))))
  refine ⟨h4.after (frame5.sub (tailWrites_sub h.valid)) rest5 (rest5.1 .esp (by decide)), ?_, ?_, cleared, bodyFrame,
    (rest1.mono (by simp)).trans ((rest2.mono (by simp [callClobbers])).trans
      ((rest3.mono (by simp)).trans ((rest4.mono (by simp [callClobbers])).trans rest5)))⟩
  · rw [status, accepted, equal]; exact logic.1
  · rw [output, accepted, equal, m4]
    simp only [Bool.and_eq_true, decide_eq_true_eq, logic.2]
end VG.Proof.Rsa.X86.PrivChecked

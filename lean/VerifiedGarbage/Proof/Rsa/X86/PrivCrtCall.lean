module

public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtPre
public import VerifiedGarbage.Proof.Rsa.X86.PrivCall
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Calling the verified CRT writes its result into the private stack candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem PrivContext.temporaryWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.temporary) g.length := by
  rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)

theorem PrivContext.outgoingWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) {n : Nat} (hn : n ≤ 72) : InRegions s.wr (byteAddr g.stack) n := by
  have W := h.inner.write (d := 0) (n := n) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  simpa only [BitVec.add_zero] using W

theorem crtCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (crtRd g ++ crtWr g) (s.rd ++ s.wr) ∧ Covers (crtWr g) s.wr := by
  have wr : Covers (crtWr g) s.wr := (Covers.one h.temporaryWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one (h.outgoingWrite (Nat.le_refl 72))))
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 2).read).cons
    ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).pair
    (Covers.one (h.sources 7).read))))))

theorem crtWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ crtWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 72 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

theorem PrivContext.callBytes {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (i : Fin 8) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i := by
  have F : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem, h.sp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.X86.below_top (by decide : 4 ≤ 100) h.valid.stackLow (by decide : 4 ≤ 4))
  have E := rsa_bytes_frame F (by have := (h.sources i).fits; omega : g.sourceLength i < 2 ^ 64)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)
  exact E.trans (h.sources i).bytes

def CrtOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  Spec.Rsa.written s.mem (byteAddr g.temporary) g.length (s.gpr .eax)
    (Spec.Rsa.privateCrt (bs 0) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7))

theorem crt_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (args : CrtArgs g s) :
    WP isa (.call v.name v.code) s fun t => PrivContext g bs t ∧
      Frame (crtWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ CrtOut g bs t := by
  refine WP.mono (private_call_ok h v.verified v.stack v.noSp (crtCall_pre h args)
    (crtCovers h).1 (crtCovers h).2 (crtWrites_sub h.valid)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 18) => crtArgs_values h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  simp only [sa (by decide : 0 < 18), sa (by decide : 2 < 18), sa (by decide : 3 < 18),
    sa (by decide : 4 < 18), sa (by decide : 6 < 18), sa (by decide : 7 < 18),
    sa (by decide : 8 < 18), sa (by decide : 9 < 18), sa (by decide : 10 < 18),
    sa (by decide : 12 < 18), sa (by decide : 14 < 18), crtArgument, PrivGeometry.argument,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change Spec.Rsa.written t.mem (byteAddr g.temporary) g.length (t.gpr .eax)
    (Spec.Rsa.privateCrt
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 2)) (g.sourceLength 2))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 7)) (g.sourceLength 7))) at post
  rw [h.callBytes 0, h.callBytes 2, h.callBytes 3, h.callBytes 4, h.callBytes 5, h.callBytes 6, h.callBytes 7] at post
  exact post

end VG.Proof.Rsa.X86.PrivChecked

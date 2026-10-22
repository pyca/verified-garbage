module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Montgomery
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset

/-! Preserve the modulus, inverse and unused slots across an optimized call. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Bignum

def MontgomeryFrame (base : Addr) (sp : BitVec 32) (n o : Nat) (s t : State) : Prop :=
  Frame [⟨off base (slot n o), 8 * n⟩,
    ⟨off base montgomeryScratch, Spec.Rsa.MontMul.scratchBytes n⟩,
    below sp 40] s.mem t.mem

def MontgomerySetupFrame (base : Addr) (sp : BitVec 32) (n : Nat) (s t : State) : Prop :=
  Frame [⟨base, contextBytes n⟩,
    ⟨off base montgomeryScratch, Spec.Rsa.MontMul.scratchBytes n⟩,
    below sp 40] s.mem t.mem

theorem MontgomeryFrame.context {base : Addr} {sp : BitVec 32} {n o : Nat} {s t : State}
    (F : MontgomeryFrame base sp n o s t) (ho : o < 9) :
    MontgomerySetupFrame base sp n s t := by
  have bo := slot_bound (n := n) ho
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, contextBytes n⟩, by simp,
      Offset.sub_base base (by unfold stride at bo; omega)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem montgomery_frame_read {s t : State} {base : Addr} {n o d k : Nat}
    (scr : Scr s base montgomeryBytes) (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (F : MontgomeryFrame base (s.gpr .esp) n o s t)
    (bound : d + 4 * k ≤ montgomeryBytes)
    (outBound : slot n o + 8 * n ≤ montgomeryBytes)
    (scratchBound : montgomeryScratch + Spec.Rsa.MontMul.scratchBytes n ≤ montgomeryBytes)
    (outApart : d + 4 * k ≤ slot n o ∨ slot n o + 8 * n ≤ d)
    (scratchApart : d + 4 * k ≤ montgomeryScratch ∨
      montgomeryScratch + Spec.Rsa.MontMul.scratchBytes n ≤ d) :
    val32 t.mem base d k = val32 s.mem base d k := by
  rw [← read_eq_val32, ← read_eq_val32]
  have nowrap := scr.nowrap
  apply congrArg BitVec.toNat
  apply F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) ?_ (by
    unfold montgomeryBytes at bound; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base outApart (by unfold montgomeryBytes at bound; omega)
      (by unfold montgomeryBytes at outBound; omega)
  · exact Offset.disjoint base scratchApart (by unfold montgomeryBytes at bound; omega)
      (by unfold montgomeryBytes at scratchBound; omega)
  · exact room.apart.symm.sub_left (Offset.sub_base base bound)

theorem montgomery_context_keep {s t : State} {base : Addr} {n m o : Nat}
    (C : Context n m base montgomeryBytes s)
    (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (ho : o < 9) (ho0 : o ≠ 0)
    (cs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) (_rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (F : MontgomeryFrame base (s.gpr .esp) n o s t) :
    Context n m base montgomeryBytes t := by
  have O := montgomery_offsets hn hn' ho ho ho ho0
  have bo := slot_bound (n := n) (i := 0) (by decide)
  have so := slot_le (n := n) (i := 0) (j := o) (by omega)
  have head := slot_header n o
  have modEq := montgomery_frame_read C.scr room F (k := 2 * n) (d := slot n 0)
    (by have := C.size_le; unfold stride at bo; omega) O.o_le O.s_le
    (.inl (by unfold stride at so; omega)) (.inl (by simp only [slot, stride, montgomeryScratch]; omega))
  have invEq := montgomery_frame_read C.scr room F (k := 1) (d := 0)
    (by decide) O.o_le O.s_le (.inl (by omega)) (.inl (by decide))
  have wordEq : w32 t.mem base 0 = w32 s.mem base 0 := by
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using invEq
  refine ⟨C.scr.of_eq (cs .edi (by decide)) (cs .esp (by decide)) wr, C.size_le,
    ⟨C.modulus.n0, C.modulus.mo, C.modulus.tmp, C.modulus.sep, ?_⟩, C.gt_one, ?_⟩
  · change wordsVal t.mem base (slot n 0) n = m
    rw [wordsVal_eq_val32, modEq, ← wordsVal_eq_val32]
    exact C.modulus.val
  · rw [wordEq]; exact C.inverse

theorem montgomery_slot_keep {s t : State} {base : Addr} {n o i : Nat}
    (scr : Scr s base montgomeryBytes) (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (F : MontgomeryFrame base (s.gpr .esp) n o s t)
    (hn : 0 < n) (hn' : n ≤ 48) (ho : o < 9) (ho0 : o ≠ 0)
    (hi : i < 9) (hio : i ≠ o) :
    val32 t.mem base (slot n i) (2 * n) = val32 s.mem base (slot n i) (2 * n) := by
  have O := montgomery_offsets (a := i) (b := i) hn hn' ho hi hi ho0
  have bi := slot_bound (n := n) hi
  have sep := slot_sep (n := n) hio
  apply montgomery_frame_read scr room F (by have := O.a_le; omega) O.o_le O.s_le
  · unfold stride at sep
    omega
  · left
    simp only [contextBytes, slot, stride, montgomeryScratch] at bi ⊢
    omega

end VG.Proof.Dsa.X86.Generation

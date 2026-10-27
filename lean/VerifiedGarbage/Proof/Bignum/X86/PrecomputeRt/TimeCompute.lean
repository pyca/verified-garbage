module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeBase
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Mul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The trace of the precomputation's computation, at a run-time width

`start` and `finish` are checked by the taint analysis (`τA`); the six
squares are related by `mul_relCT`, from what each run keeps (`MulIn`,
`sq_ready`): runs from states each meeting `CIn` (on permissions narrowed to
`pre` and the working space) leak the same trace (`compute_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both mulFrame_val32 mulFrame_hdr numAt wb nw count1_zf)
open VG.Proof.Bignum.X86.PublicContext (pcStart_ok pcFinish_ok PcStarted)

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What a run of `compute` needs. -/
def CIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PcIn base bytes len args s ∧ CallRoom (s.gpr .esp) base bytes ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    ArgsOk s ∧ s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true

/-- What `finish` needs. -/
def FIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PcIn base bytes len args s ∧ ArgsOk s ∧ s.gpr .esp = sp

theorem sq_ready {sp : BitVec 32} {s : State} (I : MulIn base bytes len args sp s) :
    WP isa (PublicRt.mul 4 4 4 5) s fun u => MulIn base bytes len args sp u ∧ u.gpr .esi = s.gpr .esi := by
  obtain ⟨⟨M, C⟩, A, hsp⟩ := I
  have h := C.pi
  have R := C.room
  have nw' := h.scratch.nowrap
  have f5 := (h.fits (j := 5) (by decide)).2
  have f4 := (h.fits (j := 4) (by decide)).1
  have f0 := (h.fits (j := 0) (by decide)).1
  have wbe := VG.Proof.Bignum.X86.PublicRt.wb_eq len
  refine WP.mono (sq_ok h R (by rw [C.mod]; exact C.inv) (by rw [C.mod]; exact C.lt))
    fun u ⟨cs, rd, wr, F, L, _⟩ => ?_
  have Ku : Keeps [.eax, .ecx, .edx] s u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [calleeSaved]), rd, wr⟩
  have Fs : Frame [⟨base, bytes⟩, below (s.gpr .esp) 96] s.mem u.mem := F.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base base (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have sp' : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  have Mu : val32 u.mem base numOff (nw len) = M := by
    rw [← C.mod, show numOff = numAt len 0 by simp [numAt]]
    exact mulFrame_val32 R nw' F (.inl (by simp only [numAt]; omega)) (by simp only [numAt]; omega)
      (by simp only [numAt] at f0 ⊢; omega) f4 f5
  have Iu : w32 u.mem base invOff = w32 s.mem base invOff := by
    unfold w32
    simp only [Mem.readW]
    rw [mulFrame_hdr R nw' F (d := invOff) (k := 4) (by decide) (by simp only [numAt, numOff, invOff] at f0 ⊢; omega)
      f4 f5]
  rw [C.mod] at L
  refine ⟨⟨⟨M, h.keepF Ku (by decide) (by decide) R C.top Fs, by rw [sp']; exact R, by rw [sp']; exact C.top, Mu,
    by rw [Iu]; exact C.inv, L⟩, A.keep Ku, sp'.trans hsp⟩, Ku.1 _ (by decide)⟩

theorem squares_relCT (sp : BitVec 32) :
    RelCT isa (Both (MulIn base bytes len args sp)) PrecomputeFn.squares (Both (FIn base bytes len args sp)) := by
  let I : Nat → State → Prop := fun j t => MulIn base bytes len args sp t ∧ (t.gpr .esi).toNat = 6 - j
  have agr : ∀ {j k : Nat} {s t : State}, I j s → I k t → VG.X86.Taint.Agree τA s t :=
    fun ⟨⟨⟨_, C₁⟩, A₁, e₁⟩, _⟩ ⟨⟨⟨_, C₂⟩, A₂, e₂⟩, _⟩ => agreeA C₁.pi C₂.pi A₁ A₂ (e₁.trans e₂.symm)
  unfold PrecomputeFn.squares
  refine VG.RelCT.seq (taint_both (F := I 0) (fun s t ⟨⟨_, C₁⟩, A₁, e₁⟩ ⟨⟨_, C₂⟩, A₂, e₂⟩ =>
    agreeA C₁.pi C₂.pi A₁ A₂ (e₁.trans e₂.symm)) (.block []) (by taint_decide) fun s ⟨⟨M, C⟩, A, e⟩ =>
      wp_movS rfl fun t u _ => WP.block_nil ?_) ?_
  · refine ⟨⟨⟨M, C.pi.keep u.keeps (by decide) (by decide) (by rw [u.mem]; exact Outside.refl _ _ _ _),
      by rw [u.other _ (by decide)]; exact C.room, by rw [u.other _ (by decide)]; exact C.top, by rw [u.mem]; exact C.mod,
      by rw [u.mem]; exact C.inv, by rw [u.mem]; exact C.lt⟩, A.keep u.keeps, by rw [u.other _ (by decide)]; exact e⟩,
      by rw [u.gpr]; rfl⟩
  refine (VG.Proof.Bignum.X86.CrtRt.relCT_countLoop (N := 6) (by decide) I fun j hj => ?_).mono (fun _ _ h => h)
    fun _ _ ⟨⟨⟨⟨_, C₁⟩, A₁, e₁⟩, _⟩, ⟨⟨⟨_, C₂⟩, A₂, e₂⟩, _⟩⟩ => ⟨⟨C₁.pi, A₁, e₁⟩, ⟨C₂.pi, A₂, e₂⟩⟩
  refine VG.RelCT.seq (R := Both (I j)) (relCT_both ((mul_relCT sp (by taint_decide)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) fun t ⟨M, e⟩ => WP.mono (sq_ready M) fun u ⟨Mu, eu⟩ =>
      ⟨Mu, by rw [eu]; exact e⟩) ?_
  refine taint_both (fun s t h₁ h₂ => agr h₁ h₂) (.block []) (by taint_decide) fun t ⟨⟨⟨M, C⟩, A, e⟩, n⟩ =>
    wp_subZ rfl fun u uu z => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count1_zf (N := 6) (x := t.gpr .esi) n hj
  exact ⟨⟨⟨⟨M, C.pi.keep uu.keeps (by decide) (by decide) (by rw [uu.mem]; exact Outside.refl _ _ _ _),
    by rw [uu.other _ (by decide)]; exact C.room, by rw [uu.other _ (by decide)]; exact C.top,
    by rw [uu.mem]; exact C.mod, by rw [uu.mem]; exact C.inv, by rw [uu.mem]; exact C.lt⟩, A.keep uu.keeps,
    by rw [uu.other _ (by decide)]; exact e⟩, by rw [uu.gpr]; exact c₁⟩, by rw [z, c₂]⟩

theorem compute_relCT (sp : BitVec 32) :
    RelCT isa (Both (CIn base bytes len args sp)) PrecomputeFn.compute fun _ _ => True := by
  unfold PrecomputeFn.compute
  refine VG.RelCT.seq (taint_both (F := MulIn base bytes len args sp)
    (fun _ _ ⟨h₁, _, _, A₁, e₁, _⟩ ⟨h₂, _, _, A₂, e₂, _⟩ => agreeA h₁ h₂ A₁ A₂ (e₁.trans e₂.symm))
    (VG.Taint.hintOf taint τA PrecomputeFn.start) (by taint_decide) fun s ⟨h, R, top, A, e, V⟩ =>
      WP.mono (pcStart_ok h V) fun u S => ?_) ?_
  · have sp' : u.gpr .esp = s.gpr .esp := S.keep.1 _ (by decide)
    exact ⟨⟨_, S.pi, by rw [sp']; exact R, by rw [sp']; exact top, S.mod, S.inv, S.lt⟩, A.keep S.keep,
      sp'.trans e⟩
  refine VG.RelCT.seq (squares_relCT sp) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ ⟨⟨h₁, A₁, e₁⟩, ⟨h₂, A₂, e₂⟩⟩ => agreeA h₁ h₂ A₁ A₂ (e₁.trans e₂.symm))
    (hc := VG.Taint.hintOf taint τA PrecomputeFn.finish) (by taint_decide)

end

end VG.Proof.Bignum.X86.PrecomputeRt

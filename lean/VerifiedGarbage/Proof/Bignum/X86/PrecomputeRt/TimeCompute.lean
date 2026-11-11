module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeBase
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Main
meta import VerifiedGarbage.Proof.Bignum.X86.R2Words.Main
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Mul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The trace of the precomputation's computation, at a run-time width

`finish` and the pieces of `start` but the steps' loop are checked by the
taint analysis (`τA`): the loop, whose count is in the working area, is
related by that count, the same in both runs (`SIn`, `LIn`); the two squares
by `mul_relCT`, from what each run keeps (`MulIn`, `sq_ready`): runs from
states each meeting `CIn` (on permissions narrowed to `pre` and the working
space) leak the same trace (`compute_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both mulFrame_val32 mulFrame_hdr numAt wb nw count1_zf)
open VG.Proof.Bignum.X86.PublicContext (pcStart_ok pcFinish_ok PcStarted pcLoad_ok)

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
  let I : Nat → State → Prop := fun j t => MulIn base bytes len args sp t ∧ (t.gpr .esi).toNat = 2 - j
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
  refine (VG.Proof.Bignum.X86.CrtRt.relCT_countLoop (N := 2) (by decide) I fun j hj => ?_).mono (fun _ _ h => h)
    fun _ _ ⟨⟨⟨⟨_, C₁⟩, A₁, e₁⟩, _⟩, ⟨⟨⟨_, C₂⟩, A₂, e₂⟩, _⟩⟩ => ⟨⟨C₁.pi, A₁, e₁⟩, ⟨C₂.pi, A₂, e₂⟩⟩
  refine VG.RelCT.seq (R := Both (I j)) (relCT_both ((mul_relCT sp (by taint_decide)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) fun t ⟨M, e⟩ => WP.mono (sq_ready M) fun u ⟨Mu, eu⟩ =>
      ⟨Mu, by rw [eu]; exact e⟩) ?_
  refine taint_both (fun s t h₁ h₂ => agr h₁ h₂) (.block []) (by taint_decide) fun t ⟨⟨⟨M, C⟩, A, e⟩, n⟩ =>
    wp_subZ rfl fun u uu z => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count1_zf (N := 2) (x := t.gpr .esi) n hj
  exact ⟨⟨⟨⟨M, C.pi.keep uu.keeps (by decide) (by decide) (by rw [uu.mem]; exact Outside.refl _ _ _ _),
    by rw [uu.other _ (by decide)]; exact C.room, by rw [uu.other _ (by decide)]; exact C.top,
    by rw [uu.mem]; exact C.mod, by rw [uu.mem]; exact C.inv, by rw [uu.mem]; exact C.lt⟩, A.keep uu.keeps,
    by rw [uu.other _ (by decide)]; exact e⟩, by rw [uu.gpr]; exact c₁⟩, by rw [z, c₂]⟩

/-- What `run` needs: the modulus and its inverse. -/
def SIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  (∃ M, PcIn base bytes len args s ∧ R2Words.ModIn s base len M ∧ (M * w32 s.mem base invOff + 1) % 2 ^ 32 = 0) ∧
    CallRoom (s.gpr .esp) base bytes ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ArgsOk s ∧ s.gpr .esp = sp

/-- What the steps' loop keeps after `j` steps, from the state `s₃` before them. -/
def LIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (j : Nat) (u : State) : Prop :=
  ∃ M s₃ z, R2Words.LoopPre s₃ base bytes len args M z ∧ R2Words.StI s₃ base bytes len args M j u ∧
    val32 s₃.mem base (numAt len 0) (nw len) = M ∧
    (∀ o, numAt len 4 + 4 * R2Words.wp len ≤ o → o + 4 ≤ numAt len 5 → (o - numAt len 4) % 4 = 0 →
      w32 s₃.mem base o = 0) ∧
    (M * w32 s₃.mem base invOff + 1) % 2 ^ 32 = 0 ∧ CallRoom (s₃.gpr .esp) base bytes ∧
    (s₃.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ArgsOk s₃ ∧ s₃.gpr .esp = sp

theorem LIn.agree {sp : BitVec 32} {j k : Nat} {u v : State} (h₁ : LIn base bytes len args sp j u)
    (h₂ : LIn base bytes len args sp k v) : VG.X86.Taint.Agree τA u v := by
  obtain ⟨_, _, _, _, I₁, _, _, _, _, _, A₁, e₁⟩ := h₁
  obtain ⟨_, _, _, _, I₂, _, _, _, _, _, A₂, e₂⟩ := h₂
  exact agreeA I₁.pi I₂.pi (A₁.keep I₁.keep) (A₂.keep I₂.keep)
    (((I₁.keep.1 _ (by decide)).trans e₁).trans ((I₂.keep.1 _ (by decide)).trans e₂).symm)

theorem compute_relCT (sp : BitVec 32) :
    RelCT isa (Both (CIn base bytes len args sp)) PrecomputeFn.compute fun _ _ => True := by
  unfold PrecomputeFn.compute PrecomputeFn.start R2Words.run R2Words.stepLoop
  -- The modulus and its inverse.
  refine VG.RelCT.seq (R := Both (MulIn base bytes len args sp)) (VG.RelCT.seq (taint_both (F := SIn base bytes len args sp)
    (fun _ _ ⟨h₁, _, _, A₁, e₁, _⟩ ⟨h₂, _, _, A₂, e₂, _⟩ => agreeA h₁ h₂ A₁ A₂ (e₁.trans e₂.symm))
    (VG.Taint.hintOf taint τA (.seq (load 0 2 3) (.block (VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff))))
    (by taint_decide) fun s ⟨h, R, top, A, e, V⟩ => WP.mono (pcLoad_ok h V) fun u L => ?_) ?_) ?_
  · have sp' : u.gpr .esp = s.gpr .esp := L.keep.1 _ (by decide)
    exact ⟨⟨_, L.pi, L.mod, L.inv⟩, by rw [sp']; exact R, by rw [sp']; exact top, A.keep L.keep, sp'.trans e⟩
  -- `prep`.
  · refine VG.RelCT.seq (R := Both (LIn base bytes len args sp 0)) (taint_both (F := LIn base bytes len args sp 0)
      (fun _ _ ⟨⟨_, h₁, _⟩, _, _, A₁, e₁⟩ ⟨⟨_, h₂, _⟩, _, _, A₂, e₂⟩ => agreeA h₁ h₂ A₁ A₂ (e₁.trans e₂.symm))
      (VG.Taint.hintOf taint τA R2Words.prep) (by taint_decide) fun s ⟨⟨M, h, Mo, inv⟩, R, top, A, e⟩ =>
        WP.mono (R2Words.prep_ok h Mo) fun u ⟨s₃, z, L, I₀, N₃, Z₃, O₃, K₃⟩ => ?lin) ?rest
    case lin =>
      have nw' := L.pi.scratch.nowrap
      have dims := L.pi.dimensions
      have f4 := (L.pi.fits (j := 4) (by decide)).1
      have wbe := VG.Proof.Bignum.X86.PublicRt.wb_eq len
      have sp' : s₃.gpr .esp = s.gpr .esp := K₃.1 _ (by decide)
      refine ⟨M, s₃, z, L, I₀, ?_, Z₃, ?_, by rw [sp']; exact R, by rw [sp']; exact top, A.keep K₃, sp'.trans e⟩
      · rw [← Mo.val]; exact val32_congr fun j hj => N₃ _ (by omega) (by simp [numAt, numOff] at *; omega)
      · rw [O₃.w32 (.inl (by simp only [invOff, R2Words.oP]; omega)) (by decide)]; exact inv
    -- The steps' loop, by its count.
    case rest =>
      by_cases hb : 64 ≤ len ∧ len ≤ 1024
      swap
      · exact VG.RelCT.of_false fun _ _ ⟨⟨_, _, _, L, _⟩, _⟩ => hb ⟨L.pi.lower, L.pi.upper⟩
      refine VG.RelCT.seq (R := Both (LIn base bytes len args sp (R2Words.nSteps len)))
        ((VG.Proof.Bignum.X86.CrtRt.relCT_countLoop (N := R2Words.nSteps len) ?_
        (LIn base bytes len args sp) fun j hj => ?_).mono (fun _ _ h => h) fun _ _ h => h) ?_
      · exact R2Words.nSteps_pos hb.1 hb.2
      · refine taint_both (fun _ _ h₁ h₂ => LIn.agree h₁ h₂)
          (VG.Taint.hintOf taint τA (.seq R2Words.step (.block [.mov .eax (.mem (R2Words.hd R2Words.oSteps)),
            .alu .sub .eax (.imm 1), .store (R2Words.hd R2Words.oSteps) .eax])))
          (by taint_decide) fun u ⟨M, s₃, z, L, I, hM₃, Z₃, inv, R, top, A, e⟩ =>
            WP.mono (R2Words.stepIter_ok L hj I) fun v ⟨I', zv⟩ => ⟨⟨M, s₃, z, L, I', hM₃, Z₃, inv, R, top, A, e⟩, zv⟩
      -- `tail`.
      · refine taint_both (F := MulIn base bytes len args sp) (fun _ _ h₁ h₂ => LIn.agree h₁ h₂)
          (VG.Taint.hintOf taint τA R2Words.tail) (by taint_decide)
          fun u ⟨M, s₃, z, L, I, hM₃, Z₃, inv, R, top, A, e⟩ => WP.mono (R2Words.fin_ok L I hM₃ Z₃)
            fun t ⟨V, Mt, O, K⟩ => ?_
        have h := L.pi
        have nw' := h.scratch.nowrap
        have f0 := (h.fits (j := 0) (by decide)).1
        have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
        have sp' : t.gpr .esp = s₃.gpr .esp := K.1 _ (by decide)
        refine ⟨⟨M, h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by simp only [R2Words.oMask]; omega)),
          by rw [sp']; exact R, by rw [sp']; exact top, by rw [show numOff = numAt len 0 by simp [numAt]]; exact Mt, ?_,
          ?_⟩, A.keep K, sp'.trans e⟩
        · rw [O.w32 (.inl (by simp only [invOff, R2Words.oMask]; omega)) (by decide)]; exact inv
        · rw [V]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) L.hxm)
  refine VG.RelCT.seq (squares_relCT sp) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ ⟨⟨h₁, A₁, e₁⟩, ⟨h₂, A₂, e₂⟩⟩ => agreeA h₁ h₂ A₁ A₂ (e₁.trans e₂.symm))
    (hc := VG.Taint.hintOf taint τA PrecomputeFn.finish) (by taint_decide)

end

end VG.Proof.Bignum.X86.PrecomputeRt

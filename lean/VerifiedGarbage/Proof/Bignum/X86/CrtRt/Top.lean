module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Sized
public import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailure
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.X86.CrtSave
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Functional correctness and cdecl preservation of private CRT RSA at a run-time width

`body_ok`: the modulus checked, then `sized_ok` or the failure; `operation_ok`:
the registers saved and restored around it; `correct`: the contract.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments accepted outputValue specResult specResult_eq)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem frameRt_saved {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame (rtBody base out bytes len sp) m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 48 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (Z : Region.Disjoint (VG.X86.below sp 96) ⟨base, bytes⟩)
    (S : Saved m (off base) g CrtRt.savedRegisters) : Saved m' (off base) g CrtRt.savedRegisters := by
  intro p hp
  have B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
    simp only [CrtRt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨off base 32, 16⟩)
    (Offset.contains base B.1 (by omega) (by decide)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [rtBody, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base base (by decide) (by decide)
  · exact Offset.disjoint base (.inl (by decide)) (by decide) (by omega)
  · exact A.sub_left (Offset.sub_base base (by omega))
  · exact (Z.sub_right (Offset.sub_base base (by omega))).symm

theorem frameRt_full {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame (rtBody base out bytes len sp) m m') (low : 48 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩, VG.X86.below sp 96] m m' := by
  apply F.sub
  intro r hr
  simp only [rtBody, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega)⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem restored_abi {s t u : State} (R : Restored t u s.gpr Crt.savedRegisters)
    (sp : t.gpr .esp = s.gpr .esp)
    (ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s u := by
  refine ⟨?_, by rw [R.mem]; exact ret⟩
  intro reg hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact (R.other _ (by decide)).trans sp

theorem ret_zone40 {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 96) := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]
  exact Offset.base_disjoint_below _ (by decide)

/-- The result and what may change. -/
def Post (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax) (specResult m args) ∧
    Frame (rtBody base (byteAddr (args 0)) bytes len sp) m t.mem

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem sized_post (h : RIn base bytes len args s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    WP isa CrtRt.sized s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (sized_ok h valid) fun t ⟨Y, B, F, K⟩ => ⟨⟨?_, F⟩, K⟩
  rw [specResult_eq, h.crt.modulus_length, valid]
  by_cases acc : accepted s.mem args
  · simp only [ite_true, acc, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_true]; rfl, by simpa only [acc, ite_true] using Y⟩
  · simp only [ite_true, acc, ite_false, Spec.Rsa.written]
    exact ⟨by simp only [B, acc, decide_false]; rfl,
      by simpa only [acc, ite_false, VG.Proof.Bignum.i2osp_zero'] using Y⟩

theorem failure_post (h : RIn base bytes len args s) (failed : specResult s.mem args = none) :
    WP isa PublicFn.failure s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lo := h.lower'
  have hi := h.upper'
  refine WP.mono (publicFailure_ok (by omega) (by omega) h.crt.outFit
    ((h.stack 0 (by decide)).readSrc)
    (by rw [← h.outLen]; exact (h.stack 1 (by decide)).readSrc) h.crt.outWrite)
    fun t ⟨Y, B, O, K⟩ => ?_
  refine ⟨⟨?_, ?_⟩, K.mono (by decide)⟩
  · simp only [failed, Spec.Rsa.written]; exact ⟨B, Y⟩
  · have F := VG.Proof.Bignum.outside_frame O (by omega : 0 + len ≤ 2 ^ 64)
    simp only [BitVec.add_zero] at F
    exact F.mono (by simp [rtBody, byteAddr])

theorem body_ok (h : RIn base bytes len args s) :
    WP isa CrtRt.body s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nf := h.crt.fits 2 (by decide)
  have nr := h.crt.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [h.crt.modulus_length] at nf nr
  unfold CrtRt.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.crt.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower' h.upper' (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  have modulus : componentValue s.mem args 2 =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) := by
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) (args 3).toNat) = _
    rw [h.crt.modulus_length]
  rw [← modulus] at Z
  refine WP.ite (Spec.Rsa.modulusValid (componentValue s.mem args 2) len) Z ?_ ?_
  · intro valid
    refine WP.mono (sized_post hv (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩
  · intro invalid
    have failed : specResult v.mem args = none := by
      rw [specResult_eq, Msv, h.crt.modulus_length, invalid]
      rfl
    refine WP.mono (failure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨by simpa only [Msv, Ksv.1 .esp (by decide)] using R, Ksv.trans T⟩

end

theorem need_le {len words : Nat} (hl : 64 ≤ len) (hw : Spec.Rsa.scratchWords len ≤ words) :
    need len ≤ words * 8 := by
  simp only [need, st, bc, mw, Spec.Rsa.modulusWords, CrtRt.numBase, Spec.Rsa.scratchWords] at *
  omega

theorem entry_eq : CrtRt.entry = Crt.entry := rfl
theorem restore_eq : CrtRt.restore = Crt.restore := rfl
theorem savedRegisters_eq : CrtRt.savedRegisters = Crt.savedRegisters := rfl

theorem operation_ok {s : State} (A : CrtABI s) :
    WP isa CrtRt.code s fun t =>
      Spec.Rsa.written t.mem (argumentPointer s 0) (arg s 3).toNat (t.gpr .eax)
        (specResult s.mem (arg s)) ∧ abiPreserved s t := by
  have low : 48 ≤ (arg s 17).toNat * 8 := by have := A.used; omega
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  unfold CrtRt.code
  rw [entry_eq]
  refine WP.seq (WP.mono (Crt.installed_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  have hI : RIn (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u :=
    In.ofInputs I (need_le A.lengths.1 A.scratchLength)
      (by simp only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))]) rfl
  refine WP.seq (WP.mono (body_ok hI) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have Saved := frameRt_saved F I.outApart low high I.room.apart (savedRegisters_eq ▸ S)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  rw [espu] at F
  have Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩,
      ⟨argumentPointer s 0, (arg s 3).toNat⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    have Start := VG.Proof.Bignum.outside_frame O (by omega)
    simp only [BitVec.add_zero] at Start
    exact (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (frameRt_full F low)
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact A.retScratch
    · rw [← A.outLength]; exact A.retOut
    · exact ret_zone40 A.stackLow
  rw [restore_eq]
  refine WP.mono (Crt.entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low
    (savedRegisters_eq ▸ Saved)) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide)]
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega)
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have Specs : specResult u.mem (arg s) = specResult s.mem (arg s) := by
    unfold specResult
    rw [B 2 (by decide), B 4 (by decide), B 6 (by decide), B 8 (by decide),
      B 10 (by decide), B 12 (by decide), B 14 (by decide)]
  rw [Specs] at V
  exact V

theorem correct (s : State) (h : (Proof.Rsa.privateCrtContract abi 96).pre s) :
    ∃ trace t, Exec isa CrtRt.code s trace t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCrtContract abi 96).post s t := by
  have A := crtABI_of h
  obtain ⟨trace, t, E, V, P⟩ := operation_ok A
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold specResult at V
  rw [A.inLength, A.dpLength, A.dqLength, A.qiLength] at V
  exact V

end VG.Proof.Bignum.X86.CrtRt

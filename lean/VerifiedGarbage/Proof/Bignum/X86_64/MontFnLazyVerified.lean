module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy

import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Mont.Read

/-! # `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx` meet `mulLazyContract` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Spec.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

theorem fnLazy_implies : fnLazyContract.Implies (Spec.Rsa.Mont.mulLazyContract abi) where
  pre := by sig_implies_pre [Spec.Rsa.Mont.mulLazyContract, Spec.Rsa.Mont.sig, fnLazyContract, abi, argRegs]
  post := by sig_implies_post [Spec.Rsa.Mont.mulLazyContract, Spec.Rsa.Mont.sig, fnLazyContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.Mont.mulLazyContract, Spec.Rsa.Mont.sig, fnLazyContract, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, List.singleton_inj.mp hw⟩
  sat := by
    sig_implies_sat [Spec.Rsa.Mont.mulLazyContract, Spec.Rsa.Mont.sig, fnLazyContract, abi, argRegs] [satState]
      using satState

/-- `mulBase_ok` without `[b] < m`: the baseline is lazy too. -/
theorem mulBaseLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (hb1 : b ≠ aAcc) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp, .r13, .r14] (WP.vecKeep (by decide) (mmTailLazy_ok hs₁ hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
    (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
    h8₁ h12 h15 hsi₁ hinv)) (by decide)) fun s₂ ⟨⟨⟨_, _, heq, har, k₂⟩, hx₂, _⟩, _⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_xmm hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  rw [hm₁] at heq har
  rw [← mt] at heq har
  exact ⟨heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

theorem fnLazy_correct (s : State) (h : fnLazyContract.pre s) :
    ∃ t s', Exec isa mulBase s t s' ∧ abiPreserved s s' ∧ fnLazyContract.post s s' := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, hwr, hret, hnw, -, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, ha3⟩, ⟨hb, hb2, hb3⟩, hinv⟩ := h
  suffices hwp : WP isa mulBase s fun s' => gprPreserved s s' ∧ fnLazyContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  refine WP.mono (mulBaseLazy_ok hs rfl hH hZ hw hw' ho ha hb ho2 ho3 ha2 hb2 (idx_eq s .rdx) (idx_eq s .rcx)
    (idx_eq s .r8) hinv) fun t ⟨heq, har, k, hcs⟩ => ?_
  have hn := hs.nowrap
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact k.gpr (by decide)
    all_goals exact hcs _ (by simp)
  · refine Mem.readW_congr fun i hi => har _ fun j hj => Or.inr ?_
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega)
    simp only [ofs]; omega
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'
    exact this

theorem fnLazy_ct : ConstantTime isa fnLazyContract.pre fnLazyContract.pub mulBase :=
  RelCT.constantTime (fn_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx], by simp only [idx, hcx],
        by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_lazy_mont_mul` on x86-64: `vg_rsa_mont_mul`'s code. -/
theorem fnLazy_verified : Verified target mulBase (Spec.Rsa.Mont.mulLazyContract abi) :=
  Verified.of_correct fnLazy_correct fnLazy_ct fnLazy_implies

theorem fnAdxLazy_correct (s : State) (h : fnLazyContract.pre s) :
    ∃ t s', Exec isa mulAdxLazy s t s' ∧ abiPreserved s s' ∧ fnLazyContract.post s s' := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, hwr, hret, hnw, -, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, ha3⟩, ⟨hb, hb2, hb3⟩, hinv⟩ := h
  suffices hwp : WP isa mulAdxLazy s fun s' => gprPreserved s s' ∧ fnLazyContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  refine WP.mono (mulAdxLazy_ok hs rfl hH hZ hw hw' ho ha hb ho2 ho3 ha2 ha3 hb2 hb3 (idx_eq s .rdx) (idx_eq s .rcx)
    (idx_eq s .r8) hinv) fun t ⟨heq, har, k, hcs⟩ => ?_
  have hn := hs.nowrap
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact k.gpr (by decide)
    all_goals exact hcs _ (by simp)
  · refine Mem.readW_congr fun i hi => har _ fun j hj => Or.inr ?_
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega)
    simp only [ofs]; omega
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'
    exact this

theorem fnAdxLazy_rel : RelCT isa (Two FnPhi) mulAdxLazy fun _ _ => True := by
  unfold mulAdxLazy
  rw [show enter ++ slotsIn = zext ++ (saves ++ slotsIn) from by simp [enter]]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := fun d s => AdxIn d.call s)
    (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) fun d s h => ?_)
    (two_map FnData.call (fun _ _ h => h) (two_piece _ pins_adxIn (by taint_decide) head_fw))))
    adxTailLazy_ct
  obtain ⟨hp, hdi, hZ', hw, ho, ha, hb⟩ := h
  obtain ⟨hs, hH, hZ8, -, -⟩ := fn_good hp
  obtain ⟨-, -, -, -, -, ⟨ho8, ho2, ho3⟩, ⟨ha8, ha2, ha3⟩, ⟨hb8, hb2, hb3⟩, -⟩ := hp
  obtain ⟨B, Z, w, o, a, b⟩ := d
  simp only at hdi hZ' hw ho ha hb ⊢
  subst hdi hZ' hw ho ha hb
  simp only [FnData.call]
  exact WP.mono (zextIdx_ok ho8 ha8 hb8 (idx_eq s .rdx) (idx_eq s .rcx) (idx_eq s .r8))
    fun t ⟨hdx, hcx, h8, hm, _, k⟩ => ⟨hs.congr k.2.2, (k.gpr (by decide)), ⟨_, by rw [hm]; exact hH⟩, hZ8,
      ⟨ho8, ha8, hb8, ho2, ho3, ha2, ha3, hb2, hb3⟩, hdx, hcx, h8⟩

theorem fnAdxLazy_ct : ConstantTime isa fnLazyContract.pre fnLazyContract.pub mulAdxLazy :=
  RelCT.constantTime (fnAdxLazy_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx], by simp only [idx, hcx],
        by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_lazy_mont_mul_adx` on x86-64. -/
theorem fnAdxLazy_verified : Verified target mulAdxLazy (Spec.Rsa.Mont.mulLazyContract abi) :=
  Verified.of_correct fnAdxLazy_correct fnAdxLazy_ct fnLazy_implies

end VG.Proof.Bignum.X86_64.MontFn

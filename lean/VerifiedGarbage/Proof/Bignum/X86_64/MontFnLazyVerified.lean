module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy

import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx` meet `mulLazyContract` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

theorem fnLazy_implies : fnLazyContract.Implies (Proof.Rsa.Mont.mulLazyContract abi) where
  pre := by sig_implies_pre [Proof.Rsa.Mont.mulLazyContract, Proof.Rsa.Mont.sig, fnLazyContract, abi, argRegs]
  post := by sig_implies_post [Proof.Rsa.Mont.mulLazyContract, Proof.Rsa.Mont.sig, fnLazyContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.Mont.mulLazyContract, Proof.Rsa.Mont.sig, fnLazyContract, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, List.singleton_inj.mp hw⟩
  sat := by
    sig_implies_sat [Proof.Rsa.Mont.mulLazyContract, Proof.Rsa.Mont.sig, fnLazyContract, abi, argRegs] [satState]
      using satState

/-- `mulBase_ok` without `[b] < m`: the baseline is lazy too. -/
theorem mulBaseLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
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
  refine WP.seq (WP.mono (BaseSquare.tail_ok hs₁ hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hbx h11 h9 h10 h8₁ h12
    h15 hsi₁ hinv) fun s₂ ⟨_, _, heq, har, k₂, hx₂⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_stashed hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
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
  refine WP.mono (mulBaseLazy_ok hs rfl hH hZ hw hw' ho ha hb ho2 ho3 ha2 ha3 hb2 hb3 (idx_eq s .rdx) (idx_eq s .rcx)
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
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega_arith)
    simp only [ofs]; omega_arith
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]]
      exact hj j hj'
    exact this

theorem fnLazy_ct : ConstantTime isa fnLazyContract.pre fnLazyContract.pub mulBase :=
  RelCT.constantTime (fn_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx], by simp only [idx, hcx],
        by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_lazy_mont_mul` on x86-64: `vg_rsa_mont_mul`'s code. -/
theorem fnLazy_verified : Verified target mulBase (Proof.Rsa.Mont.mulLazyContract abi) :=
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
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega_arith)
    simp only [ofs]; omega_arith
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]]
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
theorem fnAdxLazy_verified : Verified target mulAdxLazy (Proof.Rsa.Mont.mulLazyContract abi) :=
  Verified.of_correct fnAdxLazy_correct fnAdxLazy_ct fnLazy_implies

end VG.Proof.Bignum.X86_64.MontFn

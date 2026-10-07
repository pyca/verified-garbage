import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT

/-! # `vg_rsa_mont_mul_adx` meets `vg_rsa_mont_mul`'s contract -/

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Spec.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

theorem fnAdx_correct (s : State) (h : fnContract.pre s) :
    ∃ t s', Exec isa mulAdx s t s' ∧ abiPreserved s s' ∧ fnContract.post s s' := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, hwr, hret, hnw, -, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, ha3⟩, ⟨hb, hb2, hb3⟩, hinv, hB⟩ := h
  suffices hwp : WP isa mulAdx s fun s' => gprPreserved s s' ∧ fnContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  rw [numAt_eq, numAt_eq] at hB
  refine WP.mono (mulAdx_ok hs rfl hH hZ hw hw' ho ha hb ho2 ho3 ha2 ha3 hb2 hb3 (idx_eq s .rdx) (idx_eq s .rcx)
    (idx_eq s .r8) hinv hB) fun t ⟨hlt, heq, har, k, hcs⟩ => ?_
  have hn := hs.nowrap
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · rw [numAt_eq, numAt_eq]; exact hlt
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'
    exact this

/-- The public data, as the ADX code's proofs take it. -/
def FnData.call (d : FnData) : CallData := ⟨d.B, d.Z, d.w, d.o, d.a, d.b⟩

theorem fnAdx_rel : RelCT isa (Two FnPhi) mulAdx fun _ _ => True := by
  unfold mulAdx
  rw [show enter ++ slotsIn = zext ++ (saves ++ slotsIn) from by simp [enter]]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := fun d s => AdxIn d.call s)
    (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) fun d s h => ?_)
    (two_map FnData.call (fun _ _ h => h) (two_piece _ pins_adxIn (by taint_decide) head_fw))))
    adxTail_ct
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

theorem fnAdx_ct : ConstantTime isa fnContract.pre fnContract.pub mulAdx :=
  RelCT.constantTime (fnAdx_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx], by simp only [idx, hcx],
        by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_mont_mul_adx` on x86-64. -/
theorem fnAdx_verified : Verified target mulAdx (Spec.Rsa.Mont.mulContract abi) :=
  Verified.of_correct fnAdx_correct fnAdx_ct fn_implies

end VG.Proof.Bignum.X86_64.MontFn

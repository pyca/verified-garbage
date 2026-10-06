import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked
import VerifiedGarbage.Proof.Bignum.AArch64.PubCT

/-!
# `vg_rsa_public_checked` on AArch64

`Public.code` guarded by the check of `e` (`guarded`), against the contract
on the registers with the checked postcondition (`pubChkContract`), and from
there against the shared contract (`publicChecked_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- `pubContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pubChkContract : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post s s' := Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat))

theorem pubPre_same {s t : State} (h : Same s t) : pubContract.pre t = pubContract.pre s := by
  simp only [pubContract, pdArgs, stackArg_same h, stackArgAddr, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7,
    h.sp, h.rd, h.wr]

theorem pubPub_same {s₁ s₂ t₁ t₂ : State} (h₁ : Same s₁ t₁) (h₂ : Same s₂ t₂) (h : pubContract.pub s₁ s₂) :
    pubContract.pub t₁ t₂ := by
  simp only [pubContract, stackArg_same h₁, stackArg_same h₂, h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₁.x6,
    h₁.x7, h₁.sp, h₁.mem, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, h₂.x6, h₂.x7, h₂.sp, h₂.mem] at h ⊢
  exact h

theorem pub_x1 {s : State} (h : pubContract.pre s) : (s.gpr .x1).toNat = (s.gpr .x3).toNat := by
  simp only [pubContract] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hol, -⟩ := h
  exact hol

theorem pubGeom {s : State} (h : pubContract.pre s) : Geom s := by
  have c := pubCtx_of h
  have h1 := pub_x1 h
  have hk2 := c.hk2
  have hL2 := c.hL2
  exact ⟨by have := c.hk1; omega, by omega, fun j hj => c.hout j (by omega), c.hL1, by omega,
    fun i hi => c.heb.rd i (by rw [bytesAt_length]; exact hi)⟩

theorem publicChecked_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa publicChecked s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s' := by
  refine guarded_correct pubCode_correct (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp
    simp only [pubContract, hs.x0, hs.x2, hs.x3, hs.x4, hs.x5, hs.x6, hs.mem] at hp
    simp only [pubChkContract, Spec.Rsa.publicOpChecked]
    simp only [eValid, eBytes] at hv
    simp only [hv, ↓reduceIte]; exact hp
  · intro s s' h hv hb hax
    have h1 := pub_x1 h
    simp only [eValid, eBytes] at hv
    simp only [pubChkContract, Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, by rw [← h1]; exact hb⟩

theorem publicChecked_constantTime : ConstantTime isa pubContract.pre pubContract.pub publicChecked :=
  guarded_ct pubCode_constantTime (fun _ h => pubGeom h) (fun s t hs h => (pubPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.2.2.1
      · exact hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pubPub_same h₁ h₂ hp

/-- The leak of `n` and `e`, as bytes, determines each when `n`'s length is
the same. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  exact List.append_inj hi hl

/-- A state meeting `pubContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6000`. -/
def pubSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | .x7 => 64 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x80 else if a = 0x6009 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem publicChecked_implies : pubChkContract.Implies (Spec.Rsa.publicCheckedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, pdArgs,
      stackArgs_two, List.append_eq] at h
    sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, pdArgs,
      stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract,
      pdArgs, stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract,
    pubContract, pdArgs, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract, pubContract, pdArgs,
      stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, s0, s1⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, a3]) hl
    exact ⟨hsp, a0, a1, a2, a3, a4, a5, a6, a7, s0, s1, hn, he⟩
  sat := by sig_implies_sat [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, pubChkContract,
    pubContract, pdArgs, stackArgs_two, List.append_eq] [pubSatState, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using pubSatState

theorem publicChecked_verified : Verified target publicChecked (Spec.Rsa.publicCheckedContract abi) :=
  have hct : ConstantTime isa pubChkContract.pre pubChkContract.pub publicChecked := publicChecked_constantTime
  Verified.of_correct (k := pubChkContract) publicChecked_correct hct publicChecked_implies

end VG.Proof.Rsa.AArch64

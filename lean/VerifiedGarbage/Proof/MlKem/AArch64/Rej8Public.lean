module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import Mathlib.Tactic.SplitIfs

/-! # Public stream prefixes determine the rejection loop's cursors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem candidates_eq {s u : State} (h2 : s.gpr .x2=u.gpr .x2)
    (h : ∀i<12,s.mem (s.gpr .x2+BitVec.ofNat 64 i)=u.mem (u.gpr .x2+BitVec.ofNat 64 i)) :
    candidatesAt s=candidatesAt u := by
  apply Ntt16.vhalf_ext
  intro e he
  rw [candidatesAt,candidatesAt,parsed_candidate _ _ he,parsed_candidate _ _ he,candidate,candidate]
  have hr : s.mem.read (s.gpr .x2+BitVec.ofNat 64 (3*(e/2))) 3 =
      u.mem.read (u.gpr .x2+BitVec.ofNat 64 (3*(e/2))) 3 := by
    rw [←h2]
    apply Mem.read_congr
    intro i hi
    simp only [ptr_add]
    have hh := h (3*(e/2)+i) (by omega)
    rwa [←h2] at hh
  rw [hr]

theorem inv_public {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ s u : State} (hs : Scalar.InvW w16 initial N B bP aP s₀ t s)
    (hu : Scalar.InvW w16 initial N B bP aP u₀ t u) (hsp : s₀.sp=u₀.sp) :
    s.sp=u.sp ∧ ∀r∈[Reg.x2,.x3,.x4,.x5,.x9,.x10],s.gpr r=u.gpr r := by
  refine ⟨hs.acc.sp.trans (hsp.trans hu.acc.sp.symm),?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · rw [hs.x2,hu.x2]
  · rw [hs.acc.x3,hu.acc.x3]
  · exact BitVec.eq_of_toNat_eq (hs.acc.x4.trans hu.acc.x4.symm)
  · exact BitVec.eq_of_toNat_eq (hs.x5.trans hu.x5.symm)
  · exact BitVec.eq_of_toNat_eq (hs.acc.x9.trans hu.acc.x9.symm)
  · exact BitVec.eq_of_toNat_eq (hs.x10.trans hu.x10.symm)

theorem inv_candidates {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ s u : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hs : Scalar.InvW w16 initial N B bP aP s₀ t s) (hu : Scalar.InvW w16 initial N B bP aP u₀ t u)
    (ht : t+4≤N) : candidatesAt s=candidatesAt u := by
  apply candidates_eq (by rw [hs.x2,hu.x2])
  intro i hi
  rw [hs.x2,hu.x2,ptr_add]
  rw [byte_frame hs.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact ps.disj)
      (by have := ps.bound; omega) (by omega),ps.buf _ (by omega)]
  rw [byte_frame hu.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact pu.disj)
      (by have := pu.bound; omega) (by omega),pu.buf _ (by omega)]

end VG.Proof.MlKem.AArch64.Rej8

module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Leaves
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Guard
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared

/-! Unsigned selection on nonce, AAD and plaintext sizes, preserving all
caller argument values and memory in either buffer arrangement. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Guard

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.Contiguous
abbrev temps : List Reg := [.x9,.x10,.x11]

structure View (o t : State) : Prop where
  keep : Regs temps o t
  vec : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (o.v r).extractLsb' 0 64
  dit : t.dit=o.dit

theorem standard_ok (s : State) : WP isa (.block standardGuard) s fun t =>
    View s t ∧ (t.gpr .x10 = 0 ↔ standard s) := by
  have run : WP isa (.block standardGuard) s fun t => (t.gpr .x10 = 0 ↔ standard s) ∧ Regs temps s t := by
    refine WP.of_runBlock ⟨_,by unfold standardGuard; arun [gpr_addWithCarry,sp_addWithCarry,rd_addWithCarry,wr_addWithCarry,mem_addWithCarry],?_,?_⟩
    · simp only [gpr_write,gpr_addWithCarry,c_addWithCarry,Size.bits,BitVec.setWidth_eq,ite_true,ite_false,
        reduceCtorEq,Bool.toNat_true,BitVec.shiftLeft_zero,decide_eq_true_eq,standard]
      have aad : (~~~BitVec.setWidth 64 17#16).toNat = 2^64-18 := by decide
      simp only [aad]
      split
      · simp; omega
      · have eq := BitVec.sub_eq_iff_eq_add (x := s.gpr .x3) (y := 12) (z := 0)
        simp at eq
        exact ⟨fun h => ⟨congrArg BitVec.toNat (eq.mp h),by omega⟩,fun h => eq.mpr (BitVec.eq_of_toNat_eq h.1)⟩
    · refine ⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩
      simp only [temps,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp [gpr_write,gpr_addWithCarry,hr.1,hr.2.1,hr.2.2]
  obtain ⟨tr,t,exec,hit,keep⟩ := run
  exact ⟨tr,t,exec,⟨keep,Exec.preservedV exec (by lit_decide),Exec.dit (by lit_decide) exec⟩,hit⟩

/-- A valid destination is disjoint from the 2640-byte frame, leaving room
for the 256-byte bias even when the public payload length is unrestricted. -/
theorem room_for_bias {s : State} (h : Caller s) : (stackArg s 0).toNat + 256 < 2^64 := by
  have mem : dstR s ∈ externalRegions s := by simp [externalRegions]
  have dis := h.stack (dstR s) mem
  have nowrap := h.nowrap (dstR s) mem
  have room := h.room
  by_contra big
  apply dis (s.sp - 512)
  · simp only [Region.Contains]
    bv_omega
  · simp only [Region.Contains]
    bv_omega

abbrev limitCode (n : Nat) : List Instr :=
  if n=97 then [.addImm .x .x10 .x10 31,.lsr .x .x11 .x10 7] else
  if n=225 then [.lsr .x .x11 .x10 8] else [.addImm .x .x11 .x10 225,.lsr .x .x11 .x11 10]

private theorem shifted_zero (x : Addr) (sh : Nat) :
    x >>> sh = 0 ↔ x.toNat < 2^sh := by
  constructor
  · intro h
    have val := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at val
    exact (Nat.div_eq_zero_iff.mp val).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt h

theorem limit_ok {n : Nat} (bound : n=97 ∨ n=225 ∨ n=768) {v : Addr} (s : State)
    (room : v.toNat+256<2^64) (load : s.gpr .x10 = if n=97 then v else v+31) :
    WP isa (.block (limitCode n)) s fun t =>
      View s t ∧ t.gpr .x10=v+31 ∧ (t.gpr .x11=0 ↔ v.toNat<n) := by
  have fit : (v+31).toNat=v.toNat+31 := by
    rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by simp; omega)]; rfl
  have fit' : (v+31+225).toNat=v.toNat+256 := by
    rw [BitVec.toNat_add,fit,show (225:Addr).toNat=225 from rfl,Nat.mod_eq_of_lt (by omega)]
  have short : (v+31) >>> 7 = 0 ↔ v.toNat<97 := by rw [shifted_zero,fit]; omega
  have bounded : (v+31) >>> 8 = 0 ↔ v.toNat<225 := by rw [shifted_zero,fit]; omega
  have bulk : (v+31+225) >>> 10 = 0 ↔ v.toNat<768 := by rw [shifted_zero,fit']; omega
  have run : WP isa (.block (limitCode n)) s fun t =>
      (t.gpr .x11=0 ↔ v.toNat<n) ∧ t.gpr .x10=v+31 ∧ Regs temps s t := by
    rcases bound with rfl|rfl|rfl
    all_goals
      simp at load
      refine WP.of_runBlock ⟨_,by arun [limitCode],?_,?_,?_⟩
      · simp only [gpr_write,ite_true,BitVec.setWidth_eq,load]
        first | exact short | exact bounded | exact bulk
      · simp [gpr_write,load]
      · exact ⟨by others_tac,rfl,rfl,rfl,rfl⟩
  obtain ⟨tr,t,exec,hit,x10,keep⟩ := run
  exact ⟨tr,t,exec,⟨keep,Exec.preservedV exec (by rcases bound with rfl|rfl|rfl <;> lit_decide),
    Exec.dit (by rcases bound with rfl|rfl|rfl <;> lit_decide) exec⟩,x10,hit⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Guard

module

public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.P256.X86_64.Half
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `P256.X86_64.Half`, which this module and modules that import it used -/

section

/-! Arithmetic and instruction proofs for the branchless P-256 halving block. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64
open VG.Proof.X25519.X86_64 VG.Proof.Weierstrass.X86_64

/-- The odd input is made even by adding the odd modulus. -/
def halfValue (x : Nat) : Nat := (x + Spec.P256.p * (x % 2)) / 2

theorem halfValue_lt {x : Nat} (hx : x < Spec.P256.p) : halfValue x < Spec.P256.p := by
  dsimp only [halfValue, Spec.P256.p] at hx ⊢
  omega_using [hx]

theorem halfValue_twice {x : Nat} (hx : x < Spec.P256.p) :
    (2 * halfValue x) % Spec.P256.p = x := by
  dsimp only [halfValue, Spec.P256.p] at hx ⊢
  omega_using [hx]

theorem half_lowbit (a b c d : BitVec 64) :
    val4 a b c d % 2 = a.toNat % 2 := by
  dsimp only [val4]
  omega_using []

theorem half_mask_value (a : BitVec 64) :
    val4 (0#64-(a&&&1)) ((0#64-(a&&&1))>>>32) 0
      (0xffffffff00000001#64 &&& (0#64-(a&&&1))) = Spec.P256.p * (a.toNat%2) := by
  have h : a&&&1 = BitVec.ofNat 64 (a.toNat%2) := by
    apply BitVec.eq_of_toNat_eq
    change a.toNat &&& 1 = (a.toNat%2)%2^64
    rw [Nat.and_one_is_mod]
    omega_using []
  have hm : a.toNat%2=0 ∨ a.toNat%2=1 := by omega_using []
  rcases hm with hm | hm <;> rw [h,hm] <;> decide +revert

theorem half_shift_value (a b c d e : BitVec 64) (he : e.toNat < 2) :
    val4 ((a>>>1)|||(b<<<63)) ((b>>>1)|||(c<<<63))
      ((c>>>1)|||(d<<<63)) ((d>>>1)|||(e<<<63)) = nafVal5 a b c d e/2 := by
  have h := nafShift5_value a b c d e
  have hz : (e>>>1).toNat=0 := by
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega_using [he]
  simpa only [nafVal5,val4,hz,Nat.mul_zero,Nat.add_zero] using h

theorem half_mask_ok (s : State) :
    WP isa (.block Half.mask) s fun t =>
      val4 (t.gpr .rcx) (t.gpr .rdx) 0 (t.gpr .rbp) =
        Spec.P256.p * ((s.gpr .r8).toNat%2) ∧ t.gpr .r12=0 ∧
      Keeps [.rax,.rcx,.rdx,.rbp,.r12] s t := by
  apply WP.of_runBlock
  simp only [Half.mask,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,
    show 1≤32 ∧ 32≤63 from by decide,show ¬(32=1) from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨half_mask_value _,rfl,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]

theorem half_shift_ok (s : State) (he : (s.gpr .r12).toNat<2) :
    WP isa (.block Half.shift) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11)=
        nafVal5 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12)/2 ∧
      Keeps [.rax,.r8,.r9,.r10,.r11] s t := by
  apply WP.of_runBlock
  simp only [Half.shift,List.range_succ,List.range_zero,
    List.flatMap_cons,List.flatMap_nil,List.nil_append,List.append_nil,
    List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    List.cons_append,
    runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,execShift,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    ite_true,ite_false,and_self,reduceCtorEq,
    show 1≤63 ∧ 63≤63 from by decide,show 1≤1 ∧ 1≤63 from by decide,
    show ¬(63=1) from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨half_shift_value _ _ _ _ _ he,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_setReg,RegUpd.gpr_setFlags,RegUpd.gpr_arithFlags,
    hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]


theorem half_add_ok (s : State) (hz : s.gpr .r12=0) :
    WP isa (.block Half.add) s fun t =>
      nafVal5 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) (t.gpr .r12)=
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        val4 (s.gpr .rcx) (s.gpr .rdx) 0 (s.gpr .rbp) ∧
      (t.gpr .r12).toNat<2 ∧ Keeps [.r8,.r9,.r10,.r11,.r12] s t := by
  have h := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .rcx) (s.gpr .rdx) 0 (s.gpr .rbp)
  apply WP.of_runBlock
  simp only [Half.add,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,
    readSrc,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg,RegUpd.cf_arithFlags,
    ite_true,ite_false,reduceCtorEq,hz,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · simpa only [nafVal5,val4,show (0#32).signExtend 64=0#64 from rfl,BitVec.ofNat_eq_ofNat,BitVec.zero_add,toNat_ofBool] using h
  · simp only [show (0#32).signExtend 64=0#64 from rfl,BitVec.ofNat_eq_ofNat,BitVec.zero_add,toNat_ofBool]
    exact Nat.lt_succ_of_le (Bool.toNat_le _)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]


/-- The register computation, including the carry beyond 256 bits. -/
theorem half_core_ok (s : State) :
    WP isa (.block (Half.mask ++ Half.add ++ Half.shift)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11)=
        halfValue (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)) ∧
      Keeps [.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12] s t := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (half_mask_ok s) fun u ⟨hu,hz,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (half_add_ok u hz) fun v ⟨hv,he,kv⟩ => ?_
  refine WP.mono (half_shift_ok v he) fun t ⟨ht,kt⟩ => ?_
  refine ⟨?_,(ku.mono (by regions_sub)).trans ((kv.mono (by regions_sub)).trans (kt.mono (by regions_sub)))⟩
  rw [ht,hv,hu]
  have e (r : Reg) (hr : r∉[.rax,.rcx,.rdx,.rbp,.r12]) : u.gpr r=s.gpr r := ku.1 r hr
  rw [e .r8 (by decide),e .r9 (by decide),e .r10 (by decide),e .r11 (by decide)]
  simp only [halfValue,half_lowbit]

end VG.Proof.P256.X86_64

end

end

/-! Memory contract for P-256 modular halving, permitting in-place operation. -/

@[expose] public section

namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.X25519.X86_64

private theorem regsVal_four (s : State) :
    regsVal s [.r8,.r9,.r10,.r11]=val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) := by
  simp only [regsVal,val4]
  omega_using []

/-- A canonical input yields its canonical modular half, preserving all memory
outside the output. No separation between input and output is needed. -/
theorem half_ok {s : State} {base : Addr} {size a o : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ho : o+32≤size)
    (hx : wordsVal s.mem base a 4 < Spec.P256.p) :
    WP isa (.block (half o a)) s fun t =>
      wordsVal t.mem base o 4 = halfValue (wordsVal s.mem base a 4) ∧
      wordsVal t.mem base o 4 < Spec.P256.p ∧
      (2*wordsVal t.mem base o 4)%Spec.P256.p=wordsVal s.mem base a 4 ∧
      KeepRegs [.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12] s t ∧
      Outside base o 32 s.mem t.mem := by
  rw [half,show (loads [.r8,.r9,.r10,.r11] a ++ Half.mask ++ Half.add ++ Half.shift ++
      stores [.r8,.r9,.r10,.r11] o) = loads [.r8,.r9,.r10,.r11] a ++
        ((Half.mask ++ Half.add ++ Half.shift) ++ stores [.r8,.r9,.r10,.r11] o) by
          simp only [List.append_assoc],WP.block_append_iff]
  refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs ha (by constructor <;> decide)) fun u ⟨hu,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (half_core_ok u) fun v ⟨hv,kv⟩ => ?_
  have hs₁ := hs.of_keeps ku (by decide)
  have hs₂ := hs₁.of_keeps kv (by decide)
  refine WP.mono (stores_ok [.r8,.r9,.r10,.r11] hs₂ ho (by decide)) fun t ⟨ht,kt,ot⟩ => ?_
  change regsVal u [.r8,.r9,.r10,.r11]=wordsVal s.mem base a 4 at hu
  change wordsVal t.mem base o 4=regsVal v [.r8,.r9,.r10,.r11] at ht
  have he : wordsVal t.mem base o 4=halfValue (wordsVal s.mem base a 4) := by
    rw [ht,regsVal_four,hv,←regsVal_four,hu]
  refine ⟨he,he ▸ halfValue_lt hx,?_,?_,?_⟩
  · rw [he]; exact halfValue_twice hx
  · exact ((VG.Proof.Mont.X86_64.Keeps.regs ku).mono (by regions_sub)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kv).trans (kt.mono (by regions_sub)))
  · rw [←ku.2.1,←kv.2.1]
    exact ot

end VG.Proof.P256.X86_64

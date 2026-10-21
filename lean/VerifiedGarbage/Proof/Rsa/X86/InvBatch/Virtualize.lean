module
public import VerifiedGarbage.Proof.Mont.Words32

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.VirtualWords
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The branchless replacement of modulus one by three -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

 theorem scan_eq_one (m : Mem) (base : Addr) (M n : Nat) (hn : 0<n) :
    seededOr (m.readW (off base M) 32 ^^^ 1)
      (fun j => m.readW (off base (M+4*(j+1))) 32) (n-1)=0 ↔ val32 m base M n=1 := by
  rw [seededOr_zero]
  have low : (m.readW (off base M) 32 ^^^ 1)=0 ↔ w32 m base M=1 := by
    constructor
    · intro h
      have e : m.readW (off base M) 32=1 := BitVec.xor_eq_zero_iff.mp h
      rw [w32,e]; rfl
    · intro h
      have e : m.readW (off base M) 32=1 := BitVec.eq_of_toNat_eq h
      rw [e]; decide
  rw [low]
  have tail : (∀ i<n-1,m.readW (off base (M+4*(i+1))) 32=0) ↔ val32 m base (M+4) (n-1)=0 := by
    rw [VG.Proof.Weierstrass.val32_eq_zero_iff]
    apply forall_congr'; intro i
    apply forall_congr'; intro _
    rw [show M+4*(i+1)=M+4+4*i by omega]
    constructor
    · intro h; rw [w32,h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  have expanded : val32 m base M n=w32 m base M+2^32*val32 m base (M+4) (n-1) := by
    exact (congrArg (val32 m base M) (show n=(n-1)+1 by omega)).trans rfl
  rw [tail,expanded]
  constructor
  · rintro ⟨h,t⟩; rw [h,t]
  · intro h; omega

 theorem virtualize_ok {s : State} {base : Addr} {size M n : Nat}
    (hs : Scr s base size) (hn : 0<n) (fits : M+4*n≤size) :
    WP isa (.block (VG.Impl.Rsa.X86.InvBatch.virtualize n M)) s fun t =>
      val32 t.mem base M n=(if val32 s.mem base M n=1 then 3 else val32 s.mem base M n) ∧
      Keeps [.eax,.ecx] s t ∧ Outside base M 4 s.mem t.mem := by
  have nw := hs.nowrap
  unfold VG.Impl.Rsa.X86.InvBatch.virtualize
  refine WP.block_append (WP.block_append ?_) 
  refine wp_movS (readSrc_sc hs (by omega)) fun s1 U1 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s2 U2 => WP.block_nil ?_
  have k2 : Keeps [.eax] s s2 := U1.keeps.trans U2.keeps
  have m2 : s2.mem=s.mem := U2.mem.trans U1.mem
  refine WP.mono (scanOne_ok (n-1) s2 (hs.of_keeps k2 (by decide)) (by omega)) fun s3 ⟨v3,k3,m3⟩ => ?_
  have val3 : s3.gpr .eax=seededOr (s.mem.readW (off base M) 32 ^^^ 1)
      (fun j => s.mem.readW (off base (M+4*(j+1))) 32) (n-1) := by
    rw [v3,U2.gpr,ite_eq_right (by decide),U1.gpr,m2]
  have eq3 : s3.gpr .eax=0 ↔ val32 s.mem base M n=1 := by rw [val3]; exact scan_eq_one _ _ _ _ hn
  refine wp_subS rfl fun s4 U4 cf4 => ?_
  refine wp_sbbS rfl cf4 fun s5 U5 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s6 U6 => ?_
  have mask : s6.gpr .eax=if val32 s.mem base M n=1 then 2 else 0 := by
    rw [U6.gpr,ite_eq_left rfl,U5.gpr,BitVec.sub_self]
    by_cases h : s3.gpr .eax=0
    · rw [h]; have e := eq3.mp h; rw [ite_eq_left e]; rfl
    · have nz : ¬(s3.gpr .eax).toNat<1 := by
        intro lt; have z : (s3.gpr .eax).toNat=0 := by omega
        exact h (BitVec.eq_of_toNat_eq z)
      change 0#32-(BitVec.ofBool (decide ((s3.gpr .eax).toNat<1))).setWidth 32 &&& 2 = _
      rw [decide_eq_false nz]
      rw [ite_eq_right (fun e => h (eq3.mpr e))]; rfl
  have k6 : Keeps [.eax] s s6 := ((((k2.trans k3).trans U4.keeps).trans U5.keeps).trans U6.keeps)
  have mem6 : s6.mem=s.mem := by rw [U6.mem,U5.mem,U4.mem,m3,m2]
  refine wp_movS (readSrc_sc (hs.of_keeps k6 (by decide)) (by omega)) fun s7 U7 _ => ?_
  refine wp_orS rfl fun s8 U8 => ?_
  have k8 : Keeps [.eax,.ecx] s s8 := ((k6.mono (by decide)).trans (U7.keeps.mono (by decide))).trans (U8.keeps.mono (by decide))
  have hs8 := hs.of_keeps k8 (by decide)
  refine wp_storeS (hs8.ea (by omega)) (hs8.write (by omega)) fun t T => WP.block_nil ?_
  have mem8 : s8.mem=s.mem := by rw [U8.mem,U7.mem,mem6]
  have frame : Outside base M 4 s.mem t.mem := by
    rw [T.mem,mem8]; exact writeW32_outside _ _ _ (by omega)
  refine ⟨?_,k8.trans (T.keeps _),frame⟩
  have stored : w32 t.mem base M=(s8.gpr .ecx).toNat := by rw [T.mem,w32_write_self]
  have expanded : val32 t.mem base M n=w32 t.mem base M+2^32*val32 t.mem base (M+4) (n-1) := by
    exact (congrArg (val32 t.mem base M) (show n=(n-1)+1 by omega)).trans rfl
  rw [expanded,stored,frame.val32 (by omega) (by omega)]
  rw [U8.gpr,U7.gpr,U7.other .eax (by decide),mask,mem6]
  have expanded0 : val32 s.mem base M n=w32 s.mem base M+2^32*val32 s.mem base (M+4) (n-1) := by
    exact (congrArg (val32 s.mem base M) (show n=(n-1)+1 by omega)).trans rfl
  by_cases e : val32 s.mem base M n=1
  · have low : w32 s.mem base M=1 := by rw [expanded0] at e; omega
    have high : val32 s.mem base (M+4) (n-1)=0 := by rw [expanded0] at e; omega
    have lo : s.mem.readW (off base M) 32=1 := BitVec.eq_of_toNat_eq low
    rw [ite_eq_left e,ite_eq_left e,lo,high]; rfl
  · have or0 : ∀ x : BitVec 32, x ||| 0=x := fun _ => BitVec.or_zero
    rw [ite_eq_right e,ite_eq_right e,or0,expanded0]

end VG.Proof.Rsa.X86.InvBatch

module

import VerifiedGarbage.Proof.Rsa.X86.Chain.Words
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.Chain.Word

/-! The fixed carry chain followed by public pointer and count updates. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (wp_carry)

theorem chunk_ok {s : State} {base : Addr} {size a b d n k : Nat} {op : AluOp} {cin : Bool}
    (hw : Ws s base size) (hop : op=.adc ∨ op=.sbb)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (ha : a+4*k≤size) (hb : b+4*k≤size) (hd : d+4*k≤size)
    (da : d≤a ∨ a+4*k≤d) (db : d≤b ∨ b+4*k≤d)
    (count : (s.gpr .edx).toNat=4*n) (kn : k≤n)
    (mask : s.gpr .ecx=cmask cin) :
    WP isa (.block (VG.Impl.Rsa.X86.Chain.chunk op k)) s fun t =>
      Outside base d (4*k) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t ∧
      PtrAt t base .ebp (a+4*k) ∧ PtrAt t base .ebx (b+4*k) ∧ PtrAt t base .edi (d+4*k) ∧
      (t.gpr .edx).toNat=4*(n-k) ∧ ∃ cout : Bool,t.gpr .ecx=cmask cout ∧
        Rel op (val32 t.mem base d k) (val32 s.mem base a k)
          (val32 s.mem base b k) (2^(32*k)) cin.toNat cout.toNat := by
  unfold VG.Impl.Rsa.X86.Chain.chunk
  simp only [List.cons_append,List.nil_append]
  refine wp_carry mask fun u U C => ?_
  have hu := hw.of_keeps U.keeps
  have pu (r : Reg) (h : r≠.ecx) : u.gpr r=s.gpr r := U.other r h
  have pa' : PtrAt u base .ebp a := by rw [PtrAt,pu _ (by decide)];exact pa
  have pb' : PtrAt u base .ebx b := by rw [PtrAt,pu _ (by decide)];exact pb
  have pd' : PtrAt u base .edi d := by rw [PtrAt,pu _ (by decide)];exact pd
  refine WP.block_append (WP.mono (words_ok hu hop pa' pb' pd' ha hb hd da db C) fun v ⟨O,K,c,Cv,V⟩ => ?_)
  refine wp_sbb_self Cv fun v₁ S => ?_
  refine wp_addS rfl fun v₂ A _ => wp_addS rfl fun v₃ B _ => wp_addS rfl fun v₄ D _ => ?_
  refine wp_subS rfl fun t E _ => WP.block_nil ?_
  have Kr : Keeps [.eax,.ecx] s v₁ := ((U.keeps.mono (by decide)).trans (K.mono (by decide))).trans (S.keeps.mono (by decide))
  have keep : Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s v₄ :=
    (((Kr.mono (by decide)).trans (A.keeps.mono (by decide))).trans (B.keeps.mono (by decide))).trans (D.keeps.mono (by decide))
  have mem : t.mem=v.mem := by rw [E.mem,D.mem,B.mem,A.mem,S.mem]
  have reg (r : Reg) (h : r≠.eax ∧ r≠.ecx) : v₁.gpr r=s.gpr r := Kr.1 r (by simpa using h)
  refine ⟨by rw [mem];simpa only [U.mem] using O,keep.trans (E.keeps.mono (by decide)),?_,?_,?_,?_,c,?_,?_⟩
  · rw [PtrAt,E.other _ (by decide),D.other _ (by decide),B.other _ (by decide),A.gpr,reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*k<2^32)] using ptr_add pa (BitVec.ofNat 32 (4*k))
  · rw [PtrAt,E.other _ (by decide),D.other _ (by decide),B.gpr,A.other _ (by decide),reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*k<2^32)] using ptr_add pb (BitVec.ofNat 32 (4*k))
  · rw [PtrAt,E.other _ (by decide),D.gpr,B.other _ (by decide),A.other _ (by decide),reg _ (by decide)]
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*k<2^32)] using ptr_add pd (BitVec.ofNat 32 (4*k))
  · rw [E.gpr,D.other _ (by decide),B.other _ (by decide),A.other _ (by decide),reg _ (by decide),BitVec.toNat_sub,count,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 4*k<2^32)]
    omega
  · rw [E.other _ (by decide),D.other _ (by decide),B.other _ (by decide),A.other _ (by decide),S.gpr]
  · rw [mem]
    simpa only [U.mem] using V

end VG.Proof.Rsa.X86.Chain

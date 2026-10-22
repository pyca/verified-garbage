module

public import VerifiedGarbage.Proof.Rsa.X86.Chain.Loop

/-! Addition and subtraction interfaces matching the existing key-workspace loops. -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Chain
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem addLoop_ok {s : State} {base : Addr} {size a b d n : Nat}
    (hw : Ws s base size) (hn : 0<n)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (count : (s.gpr .edx).toNat=4*n) (mask : s.gpr .ecx=cmask false) :
    WP isa (VG.Impl.Rsa.X86.Chain.loop .adc) s fun t =>
      Outside base d (4*n) s.mem t.mem ∧ PtrAt t base .ebp (a+4*n) ∧ PtrAt t base .edi (d+4*n) ∧
      (∃ c : Bool,t.gpr .ecx=cmask c ∧ val32 t.mem base d n+2^(32*n)*c.toNat=
        val32 s.mem base a n+val32 s.mem base b n) ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t := by
  refine WP.mono (loop_ok hw (.inl rfl) hn ha hb hd da db pa pb pd count mask) fun t I => ?_
  obtain ⟨c,C,V⟩ := I.value
  exact ⟨I.frame,I.pa,I.pd,⟨c,C,by simpa only [Rel,ite_true,Nat.add_zero] using V⟩,I.keep⟩

theorem subLoop_ok {s : State} {base : Addr} {size a b d n : Nat}
    (hw : Ws s base size) (hn : 0<n)
    (ha : a+4*n≤size) (hb : b+4*n≤size) (hd : d+4*n≤size)
    (da : d≤a ∨ a+4*n≤d) (db : d≤b ∨ b+4*n≤d)
    (pa : PtrAt s base .ebp a) (pb : PtrAt s base .ebx b) (pd : PtrAt s base .edi d)
    (count : (s.gpr .edx).toNat=4*n) (mask : s.gpr .ecx=cmask false) :
    WP isa (VG.Impl.Rsa.X86.Chain.loop .sbb) s fun t =>
      Outside base d (4*n) s.mem t.mem ∧ PtrAt t base .ebp (a+4*n) ∧
      (∃ c : Bool,t.gpr .ecx=cmask c ∧ val32 t.mem base d n+val32 s.mem base b n=
        val32 s.mem base a n+2^(32*n)*c.toNat) ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp,.edi] s t := by
  refine WP.mono (loop_ok hw (.inr rfl) hn ha hb hd da db pa pb pd count mask) fun t I => ?_
  obtain ⟨c,C,V⟩ := I.value
  exact ⟨I.frame,I.pa,⟨c,C,by simpa [Rel] using V⟩,I.keep⟩

end VG.Proof.Rsa.X86.Chain

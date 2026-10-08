import VerifiedGarbage.Proof.Weierstrass.X86.NafPrepIO
import VerifiedGarbage.Proof.Weierstrass.X86.NafShift

/-! The public recoder's per-byte invariant, including its scratch residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont.X86 VG.Proof.Mont

def nafPrepClob : List Reg := [.eax,.ebx,.ecx,.edx,.esi]

def nafPrepWrites (bits work : Nat) : List (Nat × Nat) := [(bits,257),(work,36)]

structure NafPrepState (base : Addr) (size bits work k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : val32 s.mem base work 9=Naf5.residual k j
  count : s.gpr .esi=BitVec.ofNat 32 j
  digits : ∀ i<j,s.mem (off base (bits+i))=Naf5.byte k i

theorem nafWork_digit {m m' : Mem} {base : Addr} {bits work i : Nat}
    (h : Outside base work 36 m m') (hsep : bits+257≤work ∨ work+36≤bits)
    (hi : i<257) (hb : bits+257≤2^64) :
    m' (off base (bits+i))=m (off base (bits+i)) :=
  h _ (by rw [ofs_off0 base (by omega)]; omega)

theorem nafPrepStep_ok {s : State} {base : Addr} {size bits work k j : Nat}
    (hI : NafPrepState base size bits work k j s) (hb : bits+257≤size)
    (hw : work+36≤size) (hsep : bits+257≤work ∨ work+36≤bits) (hj : j<257)
    (hv : Naf5.residual k j≤2^256) :
    WP isa (Naf.step bits work) s fun t => NafPrepState base size bits work k (j+1) t ∧
      t.cf=some (decide (j+1<257)) ∧ Keeps nafPrepClob s t ∧
      Outs base (nafPrepWrites bits work) s.mem t.mem := by
  have hn := hI.scr.nowrap
  rw [Naf.step]
  refine WP.seq (WP.mono (nafAdjust_ok hI.scr hw hI.value hv) fun a ⟨da,va,ka,oa⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have ca : a.gpr .esi=BitVec.ofNat 32 j := (ka.1 _ (by decide)).trans hI.count
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nafStore_ok sa hb hj ca da) fun b ⟨mb,kb⟩ => ?_
  have sb := sa.of_keeps kb (by decide)
  have ob : Outside base (bits+j) 1 a.mem b.mem := by
    rw [mb]; exact writeW8_outside _ _ _ (by omega)
  have vb : val32 b.mem base work 9=2*Naf5.residual k (j+1) := by
    rw [ob.val32 (by omega) (by omega),va]
  rw [WP.block_append_iff]
  refine WP.mono (nafShift_ok sb hw) fun c ⟨vc,kc,oc⟩ => ?_
  have sc := sb.of_keeps kc (by decide)
  have cc : c.gpr .esi=BitVec.ofNat 32 j := by
    rw [kc.1 _ (by decide),kb.1 _ (by decide),ca]
  refine WP.mono (nafInc_ok c hj cc) fun t ⟨ct,cf,kt⟩ => ?_
  refine ⟨⟨sc.of_keeps kt.keeps (by decide),?_,ct,?_⟩,cf,?_,?_⟩
  · rw [kt.2.1,vc,vb]; omega
  · intro i hi
    rw [kt.2.1,nafWork_digit oc hsep (by omega) (by omega)]
    by_cases hij : i=j
    · subst i; rw [mb]; exact writeW8_self ..
    · rw [ob _ (by rw [ofs_off0 base (by omega)]; omega),
        nafWork_digit oa hsep (by omega) (by omega)]
      exact hI.digits i (by omega)
  · exact (((ka.mono (by decide)).trans (kb.mono (by decide))).trans
      (kc.mono (by decide))).trans (kt.keeps.mono (by decide))
  · rw [kt.2.1]
    exact ((Outs.of_outside oa (by simp [nafPrepWrites])).trans
      (Outs.of_outside (ob.mono (o' := bits) (n' := 257) (by omega) (by omega)) (by simp [nafPrepWrites]))).trans
      (Outs.of_outside oc (by simp [nafPrepWrites]))

end VG.Proof.Weierstrass.X86

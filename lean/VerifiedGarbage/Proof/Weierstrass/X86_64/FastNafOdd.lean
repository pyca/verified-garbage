import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafState

/-! An odd digit advances by the window width; all skipped digits are zero. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem fastOddStep_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hw : FastNaf.Width w) (hI : FastPrepState base size bits w k j s)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256)
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.seq (Impl.Weierstrass.X86_64.FastNaf.choose w)
      (.block (Naf.subtractDigit++([.store8 (tbl bits) .rcx] : List Instr)++
        Impl.Weierstrass.X86_64.FastNaf.shift w++Impl.Weierstrass.X86_64.FastNaf.advance w))) s fun t =>
      FastPrepState base size bits w k (j+w) t ∧ KeepRegs nafPrepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  have hsft : w=1 ∨ w=5 ∨ w=7 := Or.inr hw
  have hx : (s.gpr .r8).toNat%2^w=FastNaf.residual w k j%2^w := by
    have h := hI.value
    dsimp only [nafVal5] at h
    rcases hw with rfl|rfl <;> omega
  refine WP.seq (WP.mono (fastChoose_ok s hw) fun a ⟨da,ka⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have va : nafVal5 (a.gpr .r8) (a.gpr .r9) (a.gpr .r10) (a.gpr .r11) (a.gpr .r12)=FastNaf.residual w k j := by
    rw [ka.1 .r8 (by decide),ka.1 .r9 (by decide),ka.1 .r10 (by decide),ka.1 .r11 (by decide),ka.1 .r12 (by decide)]
    exact hI.value
  have da' := da.trans (fastOdd_eq hw hx ho)
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fastSubtract_ok a w k j da' va hv) fun b ⟨vb,kb⟩ => ?_
  have sb := sa.of_keeps kb (by decide)
  have cb : b.gpr .rbx=BitVec.ofNat 64 j := (kb.1 _ (by decide)).trans ((ka.1 _ (by decide)).trans hI.count)
  have db : b.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j) := (kb.1 _ (by decide)).trans da'
  rw [WP.block_append_iff]
  refine WP.mono (fastStore_ok sb hb hj cb db) fun c ⟨mc,kc⟩ => ?_
  have sc := sb.of_keepRegs kc (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (fastShift_ok c hsft) fun d ⟨vd,kd⟩ => ?_
  have sd := sc.of_keeps kd (by decide)
  have cd : d.gpr .rbx=BitVec.ofNat 64 j := (kd.1 _ (by decide)).trans ((kc.gpr _ (by simp)).trans cb)
  refine WP.mono (fastAdvance_ok d hsft cd) fun t ⟨ct,kt⟩ => ?_
  have mt : t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte w k j) := by
    rw [kt.2.1,kd.2.1,mc,kb.2.1,ka.2.1]
  have O := writeW8_outside s.mem base (FastNaf.byte w k j) (d:=bits+j)
    (by have := hI.scr.nowrap; omega)
  refine ⟨⟨sd.of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [kt.1 .r8 (by decide),kt.1 .r9 (by decide),kt.1 .r10 (by decide),kt.1 .r11 (by decide),kt.1 .r12 (by decide),vd,
      kc.gpr .r8 (by simp),kc.gpr .r9 (by simp),kc.gpr .r10 (by simp),kc.gpr .r11 (by simp),kc.gpr .r12 (by simp),vb]
    rw [FastNaf.residual_succ,FastNaf.next_odd hw _ ho,FastNaf.residual_skip hw k j ho]
    rcases hw with rfl|rfl <;> omega
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i
      rw [writeW8_self,ite_eq_left (show j<j+w by rcases hw with rfl|rfl <;> omega)]
    · rw [O _ (by rw [ofs_off0 base (d:=bits+i) (by have:=hI.scr.nowrap; omega)]; omega),hI.digits i hi]
      by_cases hij' : i<j
      · simp only [hij',show i<j+w from by omega,ite_true]
      · by_cases hil : i<j+w
        · simp only [hij',hil,ite_false,ite_true]
          exact (FastNaf.byte_skip_zero hw k j (i-j) ho (by omega) (by omega)).symm.trans (by rw [Nat.add_sub_of_le (by omega)])
        · simp only [hij',hil,ite_false]
  · exact (((((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (by decide)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kb).mono (by decide))).trans (kc.mono (by simp))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kd).mono (by decide))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by decide))
  · rw [mt]
    exact O.mono (by omega) (by omega)

end VG.Proof.Weierstrass.X86_64

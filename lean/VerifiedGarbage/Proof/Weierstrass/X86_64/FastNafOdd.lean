import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafState

/-! An odd digit advances by the window width; all skipped digits are zero. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem fastOddStep_ok {s : State} {base : Addr} {size n bits w k j : Nat} (hn : n=4 ∨ n=6)
    (hw : FastNaf.Width w) (hI : FastPrepState n base size bits w k j s)
    (hb : bits+64*n+8≤size) (hj : j<64*n+1) (hv : FastNaf.residual w k j≤2^(64*n))
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.seq (Impl.Weierstrass.X86_64.FastNaf.choose w)
      (.block (Naf.subtractDigitN n++([.store8 (tbl bits) .rcx] : List Instr)++
        Impl.Weierstrass.X86_64.FastNaf.shiftN n w++Impl.Weierstrass.X86_64.FastNaf.advance w))) s fun t =>
      FastPrepState n base size bits w k (j+w) t ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem := by
  have hsft : w=1 ∨ w=5 ∨ w=7 := Or.inr hw
  have hx : (s.gpr .r8).toNat%2^w=FastNaf.residual w k j%2^w := by
    have h := hI.value
    rw [nafValN_r8] at h
    rcases hw with rfl|rfl <;> omega
  refine WP.seq (WP.mono (fastChoose_ok s hw) fun a ⟨da,ka⟩ => ?_)
  have sa := hI.scr.of_keeps ka (by decide)
  have va : nafValN n a=FastNaf.residual w k j :=
    (nafValN_keep ka.1 (by decide)).trans hI.value
  have da' := da.trans (fastOdd_eq hw hx ho)
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fastSubtractN_ok a hn w k j da' va hv) fun b ⟨vb,kb⟩ => ?_
  have sb := sa.of_keeps kb (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)
  have cb : b.gpr .rbx=BitVec.ofNat 64 j := (kb.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans ((ka.1 _ (by decide)).trans hI.count)
  have db : b.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit w k j) := (kb.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans da'
  rw [WP.block_append_iff]
  refine WP.mono (fastStore_ok sb (by omega) cb db) fun c ⟨mc,kc⟩ => ?_
  have sc := sb.of_keepRegs kc (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (fastShiftN_ok c hn hsft) fun d ⟨vd,kd⟩ => ?_
  have sd := sc.of_keeps kd (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)
  have cd : d.gpr .rbx=BitVec.ofNat 64 j := (kd.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans ((kc.gpr _ (by simp)).trans cb)
  refine WP.mono (fastAdvance_ok d hsft cd) fun t ⟨ct,kt⟩ => ?_
  have mt : t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte w k j) := by
    rw [kt.2.1,kd.2.1,mc,kb.2.1,ka.2.1]
  have O := writeW8_outside s.mem base (FastNaf.byte w k j) (d:=bits+j)
    (by have := hI.scr.nowrap; omega)
  refine ⟨⟨sd.of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [nafValN_keep kt.1 (by decide),vd,nafValN_keep kc.gpr (by simp),vb]
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
  · exact (((((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rcx])
      (by decide) (List.mem_append_left _ hr))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kb).mono (fun r hr => mem_clobN (pre:=[.rax,.rdx])
        (by decide) hr))).trans (kc.mono (by simp))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kd).mono (fun r hr => mem_clobN (pre:=[.rax])
        (by decide) hr))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (fun r hr => mem_clobN (pre:=[.rbx])
        (by decide) (List.mem_append_left _ hr)))
  · rw [mt]
    exact O.mono (by omega) (by omega)

end VG.Proof.Weierstrass.X86_64

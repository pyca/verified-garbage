import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chain

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

private theorem mac_bound {R Q X U V : Nat} (hx : X<R) (hu : U<Q) (hv : V<Q) : V+X*U<R*Q := by
  have h : X*U ≤ (R-1)*(Q-1) := Nat.mul_le_mul (by omega) (by omega)
  have e : (Q-1)+(R-1)*(Q-1)+R=R*Q := by
    calc
      _ = ((R-1)+1)*(Q-1)+R := by rw [Nat.add_mul,Nat.one_mul]; omega
      _ = R*(Q-1)+R := by rw [Nat.sub_add_cancel (by omega : 1≤R)]
      _ = R*((Q-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = R*Q := by rw [Nat.sub_add_cancel (by omega : 1≤Q)]
  omega

private theorem no_carry {L Q C V : Nat} (h : L+Q*C=V) (hb : V<Q) : L=V := by
  have hc : C=0 := by
    by_contra ne
    have : Q ≤ Q*C := Nat.le_mul_of_pos_right _ (by omega)
    omega
  simpa only [hc,Nat.mul_zero,Nat.add_zero] using h

/-- The top accumulator word is reserved for the product carry. A zero top
word makes it impossible to lose a carry when the next triangular row starts. -/
theorem chain_closed (rs : List Reg) {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rbp=off B e) (hz : s.gpr .rcx=0)
    (hZ : e+8*(k+(rs.length-1)) ≤ Z) (hn : rs≠[]) (hd : rs.Nodup)
    (hrs : ∀ r ∈ rs, Safe r ∧ r≠.rax ∧ r≠.rbx ∧ r≠.rcx)
    (hc : s.cf=some false) (ho : s.of=some false)
    (hv : value s rs<2^(64*(rs.length-1))) :
    WP isa (.block (AdxTri8.chain k .rax .rbx .rcx rs)) s fun t =>
      value t rs=value s rs+(s.gpr .rdx).toNat*wv s.mem B (e+8*k) (rs.length-1) ∧
      Keeps (([.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  refine WP.mono (chain_ok rs hs hp hz hZ hn hd (by unfold Safe; decide) (by unfold Safe; decide) (by decide)
    (by decide) (by decide) hrs hc ho) fun t ⟨c,o,_,_,eq,kt⟩ => ?_
  rw [hz] at eq
  simp only [Bool.toNat_false,show (0 : BitVec 64).toNat=0 from rfl,Nat.add_zero] at eq
  have bound := mac_bound (s.gpr .rdx).isLt (wv_lt s.mem B (e+8*k) (rs.length-1)) hv
  rw [← Nat.pow_add,show 64+64*(rs.length-1)=64*rs.length by have := List.length_pos_iff.mpr hn; omega] at bound
  exact ⟨no_carry eq bound,kt⟩

end VG.Proof.Bignum.X86_64.AdxTri8

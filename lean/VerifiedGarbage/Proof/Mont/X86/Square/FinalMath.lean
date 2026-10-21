module

import VerifiedGarbage.Proof.Mont.X86.Square.MemStep
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.Proof.Mont

theorem pow32 (n : Nat) : (2^32)^n=2^(32*n) := by rw [Nat.pow_mul]

theorem value_val32 (mem : Mem) (W : Addr) (a n : Nat) :
    Column.value (2^32) (fun i => w32 mem W (a+4*i)) n = val32 mem W a n := by
  induction n with
  | zero => simp [Column.value, val32]
  | succ n ih =>
    calc Column.value (2^32) (fun i => w32 mem W (a+4*i)) (n+1) =
           Column.value (2^32) (fun i => w32 mem W (a+4*i)) n + w32 mem W (a+4*n)*(2^32)^n := by
             simp only [Column.value, NatSum.succ]
         _ = val32 mem W a (n+1) := by rw [ih, val32_succ, pow32]; grind

theorem val32_low (mem : Mem) (W : Addr) (m : Nat) {N : Nat} (hn : 0<N) :
    val32 mem W m N%2^32=w32 mem W m := by
  have one : val32 mem W m 1=w32 mem W m := by simp [val32]
  have e := val32_append mem W m 1 (N-1)
  rw [show 1+(N-1)=N by omega, one] at e
  simp only [Nat.mul_one] at e
  rw [e, Nat.add_mod, Nat.mul_mod]
  have word := (mem.readW (off W m) 32).isLt
  simp only [Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt word]

theorem low_inverse (mem : Mem) (W : Addr) (m inv : Nat) {N : Nat} (hn : 0<N)
    (hi : (val32 mem W m N*w32 mem W inv+1)%2^32=0) :
    (w32 mem W m*w32 mem W inv+1)%2^32=0 := by
  have low := val32_low mem W m hn
  rw [Nat.add_mod, Nat.mul_mod, low] at hi
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (mem.readW (off W m) 32).isLt]
  exact hi

theorem advance (r N k c cn residue out outn p pn q qn x y z : Nat)
    (old : r^k*c+r^N*out=p+q)
    (carry : residue+r*cn=c+x+y+z)
    (output : r^N*outn=r^N*out+r^k*residue)
    (input : pn=p+x*r^k) (quot : qn=q+(y+z)*r^k) :
    r^(k+1)*cn+r^N*outn=pn+qn := by
  calc r^(k+1)*cn+r^N*outn = r^k*(residue+r*cn)+r^N*out := by rw [Nat.pow_succ, output]; grind
       _ = r^k*(c+x+y+z)+r^N*out := by rw [carry]
       _ = (r^k*c+r^N*out)+(x+y+z)*r^k := by grind
       _ = pn+qn := by rw [old, input, quot]; grind

theorem final_bound {R A M Q O c : Nat} (rpos : 0<R) (alt : A<M) (mlt : M<R) (qlt : Q<R)
    (eq : R*(O+R*c)=A*A+Q*M) : O+R*c<2*M ∧ c<2 := by
  have apos : 0<M := by omega
  have a : A*A<R*M := Nat.mul_lt_mul'' (Nat.lt_trans alt mlt) alt
  have q : Q*M<R*M := Nat.mul_lt_mul_of_pos_right qlt apos
  have bound : R*(O+R*c)<R*(2*M) := by
    rw [eq, show R*(2*M)=2*(R*M) by grind]
    omega
  have tlt := (Nat.mul_lt_mul_left rpos).mp bound
  have c2 : c<2 := by
    have : R*c<R*2 := by have := Nat.mul_lt_mul_of_pos_right mlt (by decide : 0<2); omega
    exact (Nat.mul_lt_mul_left rpos).mp this
  exact ⟨tlt,c2⟩

end VG.Proof.Mont.X86.Square

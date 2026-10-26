module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.RowsStep
import VerifiedGarbage.Proof.Mont.X86.Square.RowsFinal
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import Mathlib.Util.CompileInductive

/-! # Iterating the statically scheduled columns to the final product -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Square (mDigits qDigits)

 theorem columnsRun_ok {s t : State} {W : Addr} {L S m inv a o N k count c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (nl : N≤128)
    (hinv : (w32 s.mem W m*w32 s.mem W (S+16)+1)%2^32=0)
    (start : ColsI s W L S m a N k c t) (bound : k+count≤2*N) :
    WP isa (VG.Impl.Mont.X86.Rt.StaticSquare.columns N k count) t fun u =>
      ∃ c', ColsI s W L S m a N (k+count) c' u := by
  induction count generalizing t k c with
  | zero => exact WP.block_nil ⟨c,by simpa only [Nat.add_zero] using start⟩
  | succ count ih =>
    refine WP.seq (WP.mono (iterate_ok ha V lay nl hinv start (by omega)) fun u hu => ?_)
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using ih hu (by omega)

 theorem ColsI.final_eq {s t : State} {W : Addr} {L S m a N c : Nat}
    (I : ColsI s W L S m a N (2*N) c t) :
    (2^32)^N*(val32 t.mem W (S+52+4*N) N+(2^32)^N*c)=
      val32 s.mem W a N*val32 s.mem W a N+val32 t.mem W (S+52) N*val32 s.mem W m N := by
  have e := I.equation
  rw [Column.partSum_done _ _ _ (by omega),Column.partSum_done _ _ _ (by omega),Square.q_value] at e
  change (2^32)^(2*N)*c+(2^32)^N*val32 t.mem W (S+52+4*N) (2*N-N)=
    Column.value (2^32) (fun i => w32 s.mem W (a+4*i)) N*Column.value (2^32) (fun i => w32 s.mem W (a+4*i)) N+
    val32 t.mem W (S+52) N*Column.value (2^32) (fun i => w32 s.mem W (m+4*i)) N at e
  rw [Square.value_val32,Square.value_val32,show 2*N-N=N by omega,
    show 2*N=N+N by omega,Nat.pow_add] at e
  calc (2^32)^N*(val32 t.mem W (S+52+4*N) N+(2^32)^N*c)=
      ((2^32)^N*(2^32)^N)*c+(2^32)^N*val32 t.mem W (S+52+4*N) N := by grind
    _ = _ := e

 theorem ColsI.final_bound {s t : State} {W : Addr} {L S m a N c : Nat}
    (I : ColsI s W L S m a N (2*N) c t)
    (hlt : val32 s.mem W a N<val32 s.mem W m N) :
    val32 t.mem W (S+52+4*N) N+(2^32)^N*c<2*val32 s.mem W m N ∧ c<2 := by
  apply Square.final_bound (Nat.pow_pos (by decide)) hlt
    (by rw [Square.pow32]; exact val32_lt _ _ _ _) (by rw [Square.pow32]; exact val32_lt _ _ _ _) I.final_eq

end VG.Proof.Mont.X86.StaticSquare

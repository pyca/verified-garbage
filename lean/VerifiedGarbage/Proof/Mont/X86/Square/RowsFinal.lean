module

public import VerifiedGarbage.Proof.Mont.X86.Square.RowsLoop

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

 theorem q_value (t : State) (W : Addr) (S N : Nat) :
    Column.value (2^32) (Column.prefixDigits (qDigits t W S) (2*N)) N = val32 t.mem W (S+52) N := by
  calc Column.value (2^32) (Column.prefixDigits (qDigits t W S) (2*N)) N =
        Column.value (2^32) (fun i => w32 t.mem W (S+52+4*i)) N := by
          unfold Column.value
          apply Finset.sum_congr rfl
          intro i hi
          have lt : i<2*N := by have := Finset.mem_range.mp hi; omega
          simp only [Column.prefixDigits, lt, ↓reduceIte, qDigits]
       _ = val32 t.mem W (S+52) N := value_val32 _ _ _ _

theorem ColsI.final_eq {s t : State} {W : Addr} {L S m a N c : Nat}
    (I : ColsI s W L S m a N (2*N) c t) :
    (2^32)^N*(val32 t.mem W (S+52+4*N) N+(2^32)^N*c) =
      val32 s.mem W a N*val32 s.mem W a N+val32 t.mem W (S+52) N*val32 s.mem W m N := by
  have e := I.equation
  rw [Column.partSum_done _ _ _ (by omega), Column.partSum_done _ _ _ (by omega), q_value] at e
  change (2^32)^(2*N)*c+(2^32)^N*val32 t.mem W (S+52+4*N) (2*N-N) =
    Column.value (2^32) (fun i => w32 s.mem W (a+4*i)) N * Column.value (2^32) (fun i => w32 s.mem W (a+4*i)) N +
    val32 t.mem W (S+52) N*Column.value (2^32) (fun i => w32 s.mem W (m+4*i)) N at e
  rw [value_val32, value_val32, show 2*N-N=N by omega,
    show 2*N=N+N by omega, Nat.pow_add] at e
  calc (2^32)^N*(val32 t.mem W (S+52+4*N) N+(2^32)^N*c) =
         ((2^32)^N*(2^32)^N)*c+(2^32)^N*val32 t.mem W (S+52+4*N) N := by ring
       _ = _ := e

theorem ColsI.final_bound {s t : State} {W : Addr} {L S m a N c : Nat}
    (I : ColsI s W L S m a N (2*N) c t)
    (hlt : val32 s.mem W a N<val32 s.mem W m N) :
    val32 t.mem W (S+52+4*N) N+(2^32)^N*c<2*val32 s.mem W m N ∧ c<2 := by
  apply VG.Proof.Mont.X86.Square.final_bound (Nat.pow_pos (by decide)) hlt
    (by rw [pow32]; exact val32_lt _ _ _ _) (by rw [pow32]; exact val32_lt _ _ _ _)
    I.final_eq

end VG.Proof.Mont.X86.Square

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackTailMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack

theorem byteOf_div (G k j : Nat) : byteOf (G/2^(8*k)) j=byteOf G (k+j) := by
  unfold byteOf
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add,←Nat.mul_add]

theorem stream_written (G d c : Nat) (hd : d≤20) (hc : c≤8)
    (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (hG : G<2^(d*c))
    (m : Mem) (out : Addr) (a : BitVec 64) :
    let f := fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ c
    Written m (tailResult (d*c/8) f.mem out f.acc).1 out (d*c/8) (byteOf G) := by
  dsimp only
  obtain ⟨hw,ha⟩ := fields_written G d hd m out a hc
  have hnz : d*c%64≠0 := by rcases ht with h|h|h|h|h <;> omega
  have hdiv : d*c/8/8=d*c/64 := by omega
  have hacc : acc64 G d c=G/2^(8*(d*c/8/8*8)) := by
    rw [acc64,Nat.mod_eq_of_lt hG,hdiv]
    congr 2
    omega
  rw [ha hnz,hacc]
  have htail := tail_written (d*c/8) (G/2^(8*(d*c/8/8*8))) ht
    (fieldsRun d out (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,a⟩ c).mem out
  have htail' := htail.congr fun j _=>byteOf_div G (d*c/8/8*8) j
  have hbase : d*c/8/8*8=8*(d*c/64) := by omega
  rw [hbase] at htail'
  have hlength : 8*(d*c/64)+d*c/8%8=d*c/8 := by omega
  have hh := written_append hw htail' (by have := Nat.mul_le_mul hd hc; omega)
  simpa only [hlength,hbase] using hh

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

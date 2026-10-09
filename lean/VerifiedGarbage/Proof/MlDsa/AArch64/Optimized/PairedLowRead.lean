import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowPair_read_other (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (a : Addr)
    (h0 : Mem.Sep a 16 out0 16) (h1 : Mem.Sep a 16 out1 16)
    (h2 : Mem.Sep a 16 aux0 16) (h3 : Mem.Sep a 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read a 16=d.mem.read a 16 := by
  simp only [lowPairStep]
  rw [Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide),Mem.read_write_sep h0 (by decide)]

theorem lowRun_read_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (a : Addr)
    (hs : ∀i∈is,Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i+128)) 16) :
    (lowRun g v out aux c d is).mem.read a 16=d.mem.read a 16 := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [lowRun,ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    have h := hs i (by simp)
    exact lowPair_read_other _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem lowRun_count (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) : (lowRun g v out aux c d is).count=d.count := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih => exact ih _

theorem lowPass_count (g : Nat) (work out aux : Addr) (c : LowConstants) (d : CheckData) (n : Nat) :
    (lowPassData g work out aux c d n).count=d.count := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lowPassData,lowRun_count,ih]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailModel

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted StreamOutput)

def coreRegs : List Reg := [.x5,.x6,.x7,.x10,.x16]
def bufferBase (work : Addr) : Addr := work+256
def bufferRegion (work : Addr) : Region := ⟨bufferBase work,680⟩

structure CoreConfig (σ : State) (wlen : Nat) (w1 work : Addr) : Prop where
  length : wlen=768 ∨ wlen=1024
  workPtr : σ.gpr .x19=work
  readable : ∀d n,d+n≤wlen→InRegions (σ.rd++σ.wr) (w1+BitVec.ofNat 64 d) n
  writable : ∀d n,d+n≤2048→InRegions σ.wr (work+BitVec.ofNat 64 d) n
  separate : (Region.mk w1 wlen).Disjoint (bufferRegion work)

structure CoreEnv (σ : State) (wlen : Nat) (w1 work : Addr)
    (B : Spec.Sha3.State) (i emitted : Nat) (s : State) : Prop where
  keep : RegKeep coreRegs σ s
  frame : Frame [bufferRegion work] σ.mem s.mem
  ptr : s.gpr .x5=inputPtr wlen w1 i
  output : StreamOutput s.mem (bufferBase work) 8 (min emitted 5) B

structure CoreState (σ : State) (wlen : Nat) (w1 work : Addr)
    (A B : Spec.Sha3.State) (i : Nat) (s : State) : Prop
    extends CoreEnv σ wlen w1 work B i i s where
  pairs : Pairs s (lowRun wlen σ.mem w1 A i) (permuted B i)

structure RoundState (σ : State) (wlen : Nat) (w1 work : Addr)
    (A B : Spec.Sha3.State) (i emitted : Nat) (s : State) : Prop
    extends CoreEnv σ wlen w1 work B i emitted s where
  pairs : Pairs s (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) (permuted B (i+1))

theorem buffer_addr (work : Addr) (i : Nat) :
    work+BitVec.ofNat 64 (256+136*i)=bufferBase work+BitVec.ofNat 64 (136*i) := by
  rw [BitVec.ofNat_add,← BitVec.add_assoc]
  rfl

theorem CoreEnv.readable {σ s : State} {wlen : Nat} {w1 work : Addr}
    {B : Spec.Sha3.State} {i emitted d n : Nat} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hc : CoreConfig σ wlen w1 work) (hd : d+n≤wlen) :
    InRegions (s.rd++s.wr) (w1+BitVec.ofNat 64 d) n := by
  rw [h.keep.rd,h.keep.wr]
  exact hc.readable d n hd

theorem CoreEnv.word {σ s : State} {wlen : Nat} {w1 work : Addr}
    {B : Spec.Sha3.State} {i emitted d : Nat} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hc : CoreConfig σ wlen w1 work) (hd : d+8≤wlen) :
    s.mem.readW (w1+BitVec.ofNat 64 d) 64=σ.mem.readW (w1+BitVec.ofNat 64 d) 64 := by
  have hw : wlen≤1024 := by rcases hc.length with rfl|rfl <;> decide
  exact h.frame.readW (r:=⟨w1,wlen⟩) (Offset.contains_base w1 hd (by omega))
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hc.separate) (by decide)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

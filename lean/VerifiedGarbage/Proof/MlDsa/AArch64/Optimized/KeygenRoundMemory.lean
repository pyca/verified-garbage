import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundMem

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenRound

structure Ready (s : State) : Prop where
  q : ∀e<4,vword (s.v .v16) e=8380417#32
  bias : ∀e<4,vword (s.v .v17) e=4095#32

theorem Ready.frame {s t : State} (h : Ready s) (hk : StepKeep [.v0,.v1,.v2,.v7] s t) : Ready t :=
  ⟨by intro e he; rw [hk.vec .v16 (by decide)]; exact h.q e he,
   by intro e he; rw [hk.vec .v17 (by decide)]; exact h.bias e he⟩

def roundStep (input high low : Addr) (j : Nat) (m : Mem) : Mem :=
  let v := m.read (input+BitVec.ofNat 64 (16*j)) 16
  (m.write (high+BitVec.ofNat 64 (16*j)) 16 (highVector v)).write
    (low+BitVec.ofNat 64 (16*j)) 16 (lowVector v)
def roundRun (m : Mem) (input high low : Addr) : Nat → Mem
  | 0 => m
  | j+1 => roundStep input high low j (roundRun m input high low j)

theorem roundRun_next (m : Mem) (input high low : Addr) (j : Nat) :
    roundRun m input high low (j+1)=roundStep input high low j (roundRun m input high low j) := rfl

theorem body_step {s : State} {input high low : Addr} {u i : Nat}
    (hi : i<4) (hr : Ready s)
    (h0 : s.gpr .x0=input+BitVec.ofNat 64 (64*u))
    (h1 : s.gpr .x1=high+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=low+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hh : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (body (16*i))) s fun t =>
      StepKeep [.v0,.v1,.v2,.v7] s t ∧ Ready t ∧ t.mem=roundStep input high low (4*u+i) s.mem := by
  rw [←List.append_nil (body (16*i))]
  refine body_ok (by omega) ha hh hl hr.q hr.bias fun t hk hm => WP.block_nil_iff.mpr ⟨hk,hr.frame hk,?_⟩
  simpa only [roundStep,h0,h1,h2,BitVec.add_assoc,←BitVec.ofNat_add,
    show 64*u+16*i=16*(4*u+i) by omega] using hm

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound

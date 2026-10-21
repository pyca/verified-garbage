module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Mont.X86.Square.RowsStep
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

def initCode : List Instr := [.mov .esi (.imm 0), .xop (.bin .pxor .xmm3 .xmm3),
  .mov .eax (.imm (-1)), .xop (.movd .xmm7 .eax)]
def initState (s : State) : State :=
  let t1 := s.setReg .esi 0
  let t2 := t1.setXmm .xmm3 0
  let t3 := t2.setReg .eax (-1)
  (XOp.movd .xmm7 .eax).exec t3

theorem run_init (s : State) : runBlock isa initCode s=some (initState s) := by
  simp only [initCode, runBlock_cons, exec, readSrc, Option.map_some, XOp.exec, XBinOp.eval,
    BitVec.xor_self, runStep_some, runBlock_nil]
  rfl

theorem init_values (s : State) : (initState s).gpr .esi=BitVec.ofNat 32 0 ∧
    (initState s).xmm .xmm3=packed (BitVec.ofNat 64 0) ∧
    (initState s).xmm .xmm7=packed (BitVec.ofNat 64 (2^32-1)) ∧
    (initState s).mem=s.mem ∧ Keeps [.eax, .esi] s (initState s) := by
  refine ⟨?_, ?_, ?_, rfl, ⟨?_, rfl, rfl⟩⟩
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> simp_all [initState, XOp.exec, State.setReg, State.setXmm]

theorem columnsLoop_ok {s t : State} {W : Addr} {L S m inv a o N c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (np : 0<N)
    (hinv : (w32 s.mem W m*w32 s.mem W inv+1)%2^32=0)
    (start : ColsI s W L S m a N 0 c t) :
    WP isa (.loop VG.Impl.Mont.X86.Rt.Square.column .ne) t fun u => ∃ c', ColsI s W L S m a N (2*N) c' u := by
  refine WP.loop (M := isa) (fun n u => ∃ k c, k+n=2*N ∧ 0<n ∧ ColsI s W L S m a N k c u) ?_
    (2*N) t ⟨0,c,by omega,by omega,start⟩
  intro n t ⟨k,c,kn,pos,I⟩
  refine WP.mono (iterate_ok ha V lay hinv I (by omega)) fun u ⟨Iu,zf⟩ => ?_
  by_cases endAt : k+1=2*N
  · left
    refine ⟨?_, nextCarry t W a S m inv N k c, ?_⟩
    · change u.zf.map not=some false
      simp [zf,endAt]
    · simpa only [endAt] using Iu
  · right
    refine ⟨?_,n-1,by omega,k+1,_,by omega,by omega,Iu⟩
    change u.zf.map not=some true
    simp [zf,endAt]

theorem start_ok {s : State} {W : Addr} {L S m inv a o N : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (np : 0<N)
    (edi : PtrAt s W .edi S)
    (hinv : (w32 s.mem W m*w32 s.mem W inv+1)%2^32=0) :
    WP isa (.seq (.block initCode) (.loop VG.Impl.Mont.X86.Rt.Square.column .ne)) s fun u =>
      ∃ c, ColsI s W L S m a N (2*N) c u := by
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨initState s,run_init s,?_⟩
  have v := init_values s
  have start : ColsI s W L S m a N 0 0 (initState s) := by
    refine ⟨hw.of_keeps v.2.2.2.2, ?_, ?_, v.2.2.2.2.mono (by decide), ?_, v.1, v.2.1, v.2.2.1, by omega, ?_⟩
    · rw [v.2.2.2.1]; exact Outside.refl _ _ _ _
    · rw [v.2.2.2.1]; exact Outs.refl _ _ _
    · rw [PtrAt,v.2.2.2.2.1 _ (by decide)]; exact edi
    · simp only [Column.partSum_zero, Nat.zero_sub, val32, Nat.mul_zero, Nat.add_zero]
  exact columnsLoop_ok ha V lay np hinv start

end VG.Proof.Mont.X86.Square

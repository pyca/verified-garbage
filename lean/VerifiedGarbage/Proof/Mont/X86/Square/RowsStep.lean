module

public import VerifiedGarbage.Proof.Mont.X86.Square.RedMath
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.RowsMath
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Square.ColumnMath
import VerifiedGarbage.Proof.Mont.X86.Square.ColumnStep
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import Init.Prelude
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem
import Mathlib.Util.CompileInductive

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

structure ColsI (s : State) (W : Addr) (L S m a N k c : Nat) (t : State) : Prop where
  ws : Ws t W L
  out : Outside W S (12*N+56) s.mem t.mem
  frame : Outs W [(S+20,8),(S+52,8*N+8)] s.mem t.mem
  keep : Keeps [.eax, .edx, .ecx, .ebp, .ebx, .esi] s t
  edi : PtrAt t W .edi S
  count : t.gpr .esi = BitVec.ofNat 32 (4*k)
  carry : t.xmm .xmm3 = packed (BitVec.ofNat 64 c)
  mask : t.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1))
  bound : c≤4*N*2^32
  equation : (2^32)^k*c+(2^32)^N*val32 t.mem W (S+52+4*N) (k-N) =
    Column.partSum (2^32) (mDigits s W a) (mDigits s W a) N k +
    Column.partSum (2^32) (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k

theorem iterate_ok {s t : State} {W : Addr} {L S m inv a o N k c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a)
    (hinv : (w32 s.mem W m*w32 s.mem W inv+1)%2^32=0)
    (I : ColsI s W L S m a N k c t) (hk : k<2*N) :
    WP isa VG.Impl.Mont.X86.Rt.Square.column t fun u => ColsI s W L S m a N (k+1) (nextCarry t W a S m inv N k c) u ∧
      u.zf = some (decide (k+1=2*N)) := by
  have nw := I.ws.nowrap
  have h8 : 8*N<2^32 := by have := lay.scr; omega
  have np : 0<N := by omega
  have ki : S+52+4*k+4≤L := by have := lay.scr; omega
  have haT := ha.of_keeps I.keep (by decide)
    (Outs.of_outside (I.out.mono (Nat.zero_le _) (by have := lay.scr; omega)) (List.mem_singleton_self _))
  have af := digits_frame nw lay.a_le lay.sa I.out
  have mf := digits_frame nw lay.mo_le lay.smo I.out
  have m0 : w32 t.mem W m=w32 s.mem W m := by simpa only [Nat.mul_zero, Nat.add_zero] using mf 0 np
  have iv : w32 t.mem W inv=w32 s.mem W inv := I.out.w32 (by have := lay.sinv; omega) (by have := lay.inv_le; omega)
  have ac : Column.coeff (fun i => w32 t.mem W (a+4*i)) (fun i => w32 t.mem W (a+4*i)) N k =
      Column.coeff (mDigits s W a) (mDigits s W a) N k := coeff_congr af af
  have mc : Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits t W m) N k =
      Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k := coeff_congr (fun _ _ => rfl) mf
  let q := nextQ t W a S m inv N k c
  let lo := preLow t W a S m N k c
  let residue := sumLow t W a S m inv N k c%2^32
  have qlt : q<2^32 := nextQ_lt t W a S m inv N k c
  have qzero : N≤k → q=0 := by
    intro large
    simp only [q, nextQ, Nat.not_lt.mpr large, ↓reduceIte]
  have residueSmall : k<N → residue=0 := by
    intro small
    exact sumLow_zero t W a S m inv N k c small (by rw [m0, iv]; exact hinv)
  have residueLarge : N≤k → residue=lo%2^32 := by
    intro large
    have zero := qzero large
    simp only [residue, sumLow, show nextQ t W a S m inv N k c=0 from zero,
      Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
    rfl
  refine WP.mono (column_ok haT I.ws V lay hk I.bound I.edi I.count I.carry I.mask)
    fun u ⟨memU, carryU, maskU, countU, zfU, keepU⟩ => ?_
  have mem : u.mem=stepMem t.mem W S k lo (if k<N then q else lo) := by
    simpa only [stepMem] using memU
  have qStep := qPart_memstep nw lay.scr hk qlt qzero mem (mDigits s W m)
  have outStep := output_memstep nw lay.scr hk residueSmall residueLarge mem
  have carries : residue+2^32*nextCarry t W a S m inv N k c =
      c+Column.coeff (mDigits s W a) (mDigits s W a) N k +
        Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k + q*mDigits s W m 0 := by
    calc residue+2^32*nextCarry t W a S m inv N k c =
          Column.coeff (mDigits s W a) (mDigits s W a) N k +
            Column.coeff (Column.prefixDigits (qDigits t W S) k) (mDigits s W m) N k +
            q*w32 s.mem W m+c := by
              rw [nextCarry_value, column_value t W a S m inv hk, ac, mc, m0]
         _ = _ := by simp only [mDigits, Nat.mul_zero, Nat.add_zero]; ac_rfl
  have newEq := advance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I.equation carries outStep
    (Column.partSum_succ (2^32) (mDigits s W a) (mDigits s W a) N k) qStep
  have Ostep : Outside W S (12*N+56) t.mem u.mem := by
    rw [mem]
    exact stepMem_outside _ _ nw lay.scr hk _ _
  have Fstep : Outs W [(S+20,8),(S+52,8*N+8)] t.mem u.mem := by
    rw [mem]
    exact stepMem_frame _ _ nw lay.scr hk _ _
  refine ⟨⟨I.ws.of_keeps keepU, I.out.trans Ostep, I.frame.trans Fstep, I.keep.trans keepU,
    ?_, countU, carryU, maskU, (column_bounds t W a S m inv hk h8 I.bound).2.2.1, newEq⟩, zfU⟩
  rw [PtrAt, keepU.1 _ (by decide)]
  exact I.edi

end VG.Proof.Mont.X86.Square

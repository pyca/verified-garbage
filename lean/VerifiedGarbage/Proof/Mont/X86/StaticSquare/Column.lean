module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.MemStep
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.ColumnSquare

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Input
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Digit
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Double
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.ReductionProducts
import VerifiedGarbage.Proof.Mont.X86.Square.ColumnMath
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.CarryMath
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Words
/-! # One statically scheduled Montgomery square column -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/StaticSquare/ColumnMath.lean`, which only this module imported.
section

/-! # Bounds and cancellation for a complete scalar column -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont

def inputCoeff (mem : Mem) (W : Addr) (a N k : Nat) :=
 Column.coeff (fun i => w32 mem W (a+4*i)) (fun i => w32 mem W (a+4*i)) N k

def redCoeff (mem : Mem) (W : Addr) (S m N k : Nat) :=
 Column.coeff (Column.prefixDigits (fun i => w32 mem W (S+52+4*i)) k)
   (fun i => w32 mem W (m+4*i)) N k

def pre (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 c+inputCoeff mem W a N k+redCoeff mem W S m N k

def quot (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 if k<N then (pre mem W a S m N k c%2^32*w32 mem W (S+16))%2^32 else 0

def total (mem : Mem) (W : Addr) (a S m N k c : Nat) :=
 pre mem W a S m N k c+quot mem W a S m N k c*w32 mem W m

 theorem quot_lt (mem : Mem) (W : Addr) (a S m N k c : Nat) : quot mem W a S m N k c<2^32 := by
  unfold quot
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

 theorem column_bounds (mem : Mem) (W : Addr) (a S m : Nat) {N k c : Nat}
    (np : 0<N) (nl : N≤128) (cb : c≤4*N*2^32) :
    total mem W a S m N k c<2^96 ∧ total mem W a S m N k c/2^32≤4*N*2^32 := by
  have word (x : Nat) : w32 mem W x≤2^32-1 := by have := (mem.readW (off W x) 32).isLt; dsimp only [w32]; omega
  have ib : inputCoeff mem W a N k≤N*(2^32-1)*(2^32-1) :=
    Column.coeff_bound (fun i _ => word _) (fun i _ => word _)
  have rb : redCoeff mem W S m N k≤N*(2^32-1)*(2^32-1) := by
    apply Column.coeff_bound _ (fun i _ => word _)
    intro i hi
    unfold Column.prefixDigits
    split
    · exact word _
    · omega
  have qb : quot mem W a S m N k c≤2^32-1 := by have := quot_lt mem W a S m N k c; omega
  have mul := Nat.mul_le_mul qb (word m)
  unfold total pre
  constructor <;> omega

 theorem total_cancel (mem : Mem) (W : Addr) (a S m N k c : Nat) (small : k<N)
    (inverse : (w32 mem W m*w32 mem W (S+16)+1)%2^32=0) :
    total mem W a S m N k c%2^32=0 := by
  unfold total quot
  rw [ite_eq_left small]
  exact Square.cancel_digit _ _ _ _ inverse

 theorem pre_bounds (mem : Mem) (W : Addr) (a S m N k c : Nat)
    (bound : total mem W a S m N k c<2^96) :
    pre mem W a S m N k c<2^96 ∧ inputCoeff mem W a N k<2^96 := by
  unfold total pre at bound
  unfold pre
  omega

end VG.Proof.Mont.X86.StaticSquare
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/X86/StaticSquare/CarryIn.lean`, which only this module imported.
section

/-! # The preceding column carry enters the accumulator -/

section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem carryIn_ok {s : State} {W : Addr} {L S : Nat}
    (hw : Rt.Ws s W L) (ptr : Rt.PtrAt s W .edi S) (fits : S+16≤L)
    (bound : value s+w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12)<2^96) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.carryIn) s fun z =>
      value z=value s+w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12) ∧
      Keeps [.esi,.ebx,.ecx] s z ∧ z.mem=s.mem := by
  let c := decide (2^32≤(s.gpr .esi).toNat+w32 s.mem W (S+8))
  let d := decide (2^32≤(s.gpr .ebx).toNat+w32 s.mem W (S+12)+c.toNat)
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.carryIn
  refine wp_addS (Rt.readSrc_ptr hw ptr (by omega)) fun s₁ U₁ C₁ => ?_
  have C : s₁.cf=some c := C₁
  have h₁ := hw.of_keeps U₁.keeps
  have p₁ : Rt.PtrAt s₁ W .edi S := by rw [Rt.PtrAt,U₁.other .edi (by decide)]; exact ptr
  refine wp_adcS (Rt.readSrc_ptr h₁ p₁ (by omega)) C fun s₂ U₂ C₂ => ?_
  have D : s₂.cf=some d := by
    simpa only [U₁.other .ebx (by decide),U₁.mem] using C₂
  refine wp_adcS rfl D fun z U₃ _ => WP.block_nil ?_
  have L : (z.gpr .esi).toNat=((s.gpr .esi).toNat+w32 s.mem W (S+8))%2^32 := by
    rw [U₃.other .esi (by decide),U₂.other .esi (by decide),U₁.gpr,BitVec.toNat_add]
  have M : (z.gpr .ebx).toNat=((s.gpr .ebx).toNat+w32 s.mem W (S+12)+c.toNat)%2^32 := by
    rw [U₃.other .ebx (by decide),U₂.gpr,add3_toNat,U₁.other .ebx (by decide),U₁.mem]
  have H : (z.gpr .ecx).toNat=((s.gpr .ecx).toNat+d.toNat)%2^32 := by
    rw [U₃.gpr,add3_toNat,U₂.other .ecx (by decide),U₁.other .ecx (by decide)]
    rfl
  refine ⟨?_,?_,U₃.mem.trans (U₂.mem.trans U₁.mem)⟩
  · rw [value,L,M,H]
    exact accum96 (s.gpr .esi).isLt (s.gpr .ebx).isLt (s.gpr .ecx).isLt
      (s.mem.readW (off W (S+8)) 32).isLt (s.mem.readW (off W (S+12)) 32).isLt bound
  · have K : Keeps [.esi,.ebx,.ecx] s s₁ := U₁.keeps.mono (by decide)
    exact (K.trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))

end VG.Proof.Mont.X86.StaticSquare
end

end

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

abbrev columnClob : List Reg := [.eax,.edx,.edi,.ebp,.esi,.ebx,.ecx]

 theorem value_of_keeps {s t : State} {rs : List Reg} (K : Keeps rs s t)
    (hl : .esi∉rs) (hm : .ebx∉rs) (hh : .ecx∉rs) : value t=value s := by
  rw [value,K.1 .esi hl,K.1 .ebx hm,K.1 .ecx hh]
  rfl

 theorem column_ok {s : State} {W : Addr} {L a S m inv o N k c : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (hk : k<2*N) (nl : N≤128)
    (cb : c≤4*N*2^32) (carry : w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12)=c) :
    WP isa (VG.Impl.Mont.X86.Rt.StaticSquare.column N k) s fun t =>
      let q := quot s.mem W a S m N k c
      let word := if k<N then q else pre s.mem W a S m N k c%2^32
      let cn := total s.mem W a S m N k c/2^32
      t.mem=stepMem s.mem W S k word cn ∧ Keeps columnClob s t ∧
      PtrAt t W .edi S ∧ w32 t.mem W (S+8)+2^32*w32 t.mem W (S+12)=cn := by
  have np : 0<N := by omega_arith
  have b := column_bounds (k:=k) s.mem W a S m np nl cb
  have pb := pre_bounds s.mem W a S m N k c b.1
  have scr := lay.scr
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.column VG.Impl.Mont.X86.Rt.StaticSquare.seqs
  simp only [VG.Impl.Mont.X86.Rt.Square.seqs]
  refine WP.seq (WP.mono (clear_ok s) fun u ⟨vu,ku,mu⟩ => ?_)
  have hu := hw.of_keeps ku
  have hau := ha.of_keeps ku (by decide) (by rw [mu]; exact Outs.refl _ _ _)
  refine WP.seq (WP.mono (input_ok hu hau V.ws V.a lay.a_le hk vu
    (by rw [mu]; exact pb.2)) fun v ⟨vv,kv,mv⟩ => ?_)
  have K₁ : Keeps columnClob s v := (ku.mono (by decide)).trans (kv.mono (by decide))
  have M₁ : v.mem=s.mem := mv.trans mu
  have hv := hw.of_keeps K₁
  have hav := ha.of_keeps K₁ (by decide) (by rw [M₁]; exact Outs.refl _ _ _)
  have valueV : value v=inputCoeff s.mem W a N k := by rw [vv,mu]; rfl
  refine WP.seq (WP.block_append (WP.mono (ptr_ok hav (r:=.edi) (t:=.eax) (i:=5)
    (by decide) (by decide) (by decide)) fun x ⟨px,_,mx,kx⟩ => ?_))
  have hx := hv.of_keeps kx
  have hax := hav.of_keeps kx (by decide) (by rw [mx]; exact Outs.refl _ _ _)
  refine WP.mono (ptr_ok hax (r:=.ebp) (t:=.eax) (i:=3) (by decide) (by decide) (by decide))
    fun y ⟨py,_,my,ky⟩ => ?_
  have K₂ : Keeps [.edi,.eax,.ebp] v y :=
    (kx.mono (by decide)).trans (ky.mono (by decide))
  have K₃ : Keeps columnClob s y := K₁.trans (K₂.mono (by decide))
  have M₃ : y.mem=s.mem := my.trans (mx.trans M₁)
  have ps : PtrAt y W .edi S := by
    rw [PtrAt,ky.1 .edi (by decide),px,BitVec.toNat_add,V.ws,V.s]
  have pm : PtrAt y W .ebp m := by rw [PtrAt,py,BitVec.toNat_add,V.ws,V.mo]
  have valueY : value y=inputCoeff s.mem W a N k := (value_of_keeps K₂ (by decide) (by decide) (by decide)).trans valueV
  have byCarry : value y+w32 y.mem W (S+8)+2^32*w32 y.mem W (S+12)<2^96 := by
    rw [valueY,M₃]
    unfold pre at pb
    omega_arith
  refine WP.seq (WP.mono (carryIn_ok (hw.of_keeps K₃) ps (by omega_arith) byCarry) fun z ⟨vz,kz,mz⟩ => ?_)
  have K₄ : Keeps columnClob s z := K₃.trans (kz.mono (by decide))
  have M₄ : z.mem=s.mem := mz.trans M₃
  have pz : PtrAt z W .edi S := by rw [PtrAt,kz.1 .edi (by decide)]; exact ps
  have pzm : PtrAt z W .ebp m := by rw [PtrAt,kz.1 .ebp (by decide)]; exact pm
  have valueZ : value z=inputCoeff s.mem W a N k+c := by rw [vz,valueY,M₃,Nat.add_assoc,carry]
  have redBound : value z+reductionSum z.mem W S m N k N<2^96 := by
    rw [valueZ,M₄,reductionSum_full]
    unfold pre redCoeff at pb
    omega_arith
  refine WP.seq (WP.mono (reductionProducts_ok z (hw.of_keeps K₄) pz pzm (by omega_arith)
    lay.mo_le (Nat.le_refl _) redBound) fun r ⟨vr,kr,mr⟩ => ?_)
  have K₅ : Keeps columnClob s r := K₄.trans (kr.mono (by decide))
  have M₅ : r.mem=s.mem := mr.trans M₄
  have pr : PtrAt r W .edi S := by rw [PtrAt,kr.1 .edi (by decide)]; exact pz
  have prm : PtrAt r W .ebp m := by rw [PtrAt,kr.1 .ebp (by decide)]; exact pzm
  have valueR : value r=pre s.mem W a S m N k c := by
    rw [vr,valueZ,M₄,reductionSum_full]
    unfold pre redCoeff
    omega_arith
  have lowR : (r.gpr .esi).toNat=pre s.mem W a S m N k c%2^32 := by rw [←value_low,valueR]
  have qr : (if k<N then ((r.gpr .esi).toNat*w32 r.mem W (S+16))%2^32 else 0)=
      quot s.mem W a S m N k c := by rw [lowR,M₅]; rfl
  have digitBound : value r+(if k<N then ((r.gpr .esi).toNat*w32 r.mem W (S+16))%2^32 else 0)*w32 r.mem W m<2^96 := by
    rw [valueR,qr,M₅]
    exact b.1
  refine WP.seq (WP.mono (digit_ok (hw.of_keeps K₅) pr prm (by omega_arith)
    (by have := lay.mo_le; omega_arith) (by have := lay.smo; omega_arith) digitBound) fun d ⟨vd,kd,md⟩ => ?_)
  rw [qr] at vd md
  have valueD : value d=total s.mem W a S m N k c := by rw [vd,valueR,M₅]; rfl
  have K₆ : Keeps columnClob s d := K₅.trans (kd.mono (by decide))
  have pd : PtrAt d W .edi S := by rw [PtrAt,kd.1 .edi (by decide)]; exact pr
  refine WP.mono (carryOut_ok (hw.of_keeps K₆) pd (by omega_arith)) fun t ⟨kt,mt⟩ => ?_
  refine ⟨?_,K₆.trans (kt.mono (by decide)),?_,?_⟩
  · rw [mt,valueD,md,M₅,lowR]
    simp only [stepMem,Nat.add_assoc]
  · rw [PtrAt,kt.1 .edi (by decide)]
    exact pd
  · rw [mt,valueD]
    exact carryMem_value _ W hw.nowrap (by omega_arith) (by omega_arith)

end VG.Proof.Mont.X86.StaticSquare

module

public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized

/-! # Optimized composition with independently verified fixed hash helpers -/
@[expose] public section
namespace VG.Impl.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
open VG.Impl.MlKem.AArch64.Dot VG.Impl.MlKem.AArch64.Noise

def prfCbdUsing (hash : Prog isa) (N off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0,.strb .x9 .x28 (RB+32)])
  (.seq hash (.seq (.block (ptrTo .x0 .x28 PB ++ ptrTo .x1 .x28 off)) (cbdCall w16)))

def vRestUsing (prf : Nat→Nat→Prog isa) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
 seqs (((List.range L.k).map fun j=>dec12At ek (eo+384*j) (aOff L 0 j)) ++
 [dot (TP L) ((List.range L.k).map fun j=>(aOff L 0 j,yOff L j)),
 Ntt16.Readonly.nttInvAt (TP L),prf (2*L.k) (EP L),addAt (TP L) (EP L),
 ddAt m mo 1 (EP L),addAt (TP L) (EP L),L.ceLAt (TP L) L.dv ct (co+32*L.du*L.k)])

def encryptRestUsing (prf : Nat→Nat→Prog isa) (L : KemLay) (ek : Reg) (eo : Nat) (m : Reg) (mo : Nat) (ct : Reg) (co : Nat) : Prog isa :=
 .seq (noiseAllWith Ntt16.Readonly.nttAtWith L false) (seqs (((List.range L.k).map (uRow L ct co)) ++
  [vRestUsing prf L ek eo m mo ct co]))

def enRestUsing (prf : Nat→Nat→Prog isa) (L : KemLay) : Prog isa :=
 .seq (encryptRestUsing prf L .x25 0 .x28 MB .x27 0) (.block L.kemEpilogue)

def encapsUsing (startCode : Prog isa) (prf : Nat→Nat→Prog isa) (L : KemLay) : Prog isa :=
 .seq startCode (.seq (Paired.matrix L false) (enRestUsing prf L))

end VG.Impl.MlKem.AArch64.Optimized

module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Digit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum

/-! # Saving the two-word carry for the following column -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def carryMem (mem : Mem) (W : Addr) (S c : Nat) : Mem :=
 (mem.writeW (off W (S+8)) (BitVec.ofNat 32 c)).writeW
   (off W (S+12)) (BitVec.ofNat 32 (c/2^32))

 theorem carryOut_ok {s : State} {W : Addr} {L S : Nat}
    (hw : Ws s W L) (ps : PtrAt s W .edi S) (fits : S+16≤L) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.carryOut) s fun t =>
      Keeps [] s t ∧ t.mem=carryMem s.mem W S (value s/2^32) := by
  have low : s.gpr .ebx=BitVec.ofNat 32 (value s/2^32) := by
    apply BitVec.eq_of_toNat_eq
    rw [value_high,BitVec.toNat_ofNat]
    have := (s.gpr .ebx).isLt
    omega
  have high : s.gpr .ecx=BitVec.ofNat 32 (value s/2^32/2^32) := by
    apply BitVec.eq_of_toNat_eq
    rw [value_high,BitVec.toNat_ofNat]
    have := (s.gpr .ebx).isLt
    have := (s.gpr .ecx).isLt
    omega
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.carryOut
  refine wp_storeS (ea_ptr hw ps (by omega)) (ws_write hw (by omega)) fun u U => ?_
  have hu := hw.of_keeps (U.keeps [])
  have pu : PtrAt u W .edi S := by rw [PtrAt,U.gpr]; exact ps
  refine wp_storeS (ea_ptr hu pu (by omega)) (ws_write hu (by omega)) fun t T => WP.block_nil ?_
  refine ⟨(U.keeps []).trans (T.keeps []),?_⟩
  rw [T.mem,U.mem,U.gpr,low,high]
  rfl

 theorem carryMem_frame (mem : Mem) (W : Addr) {L S : Nat} (nw : W.toNat+L≤2^32)
    (fits : S+16≤L) (c : Nat) : Outside W (S+8) 8 mem (carryMem mem W S c) := by
  unfold carryMem
  exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))

 theorem carryMem_value (mem : Mem) (W : Addr) {L S : Nat} (nw : W.toNat+L≤2^32)
    (fits : S+16≤L) {c : Nat} (hc : c<2^64) :
    w32 (carryMem mem W S c) W (S+8)+2^32*w32 (carryMem mem W S c) W (S+12)=c := by
  have O := writeW32_outside (mem.writeW (off W (S+8)) (BitVec.ofNat 32 c)) W
    (d:=S+12) (BitVec.ofNat 32 (c/2^32)) (by omega : S+12+4≤2^64)
  unfold carryMem
  rw [O.w32 (by omega) (by omega),w32_write_self,w32_write_self,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  have hdiv : c/2^32<2^32 := by omega
  rw [Nat.mod_eq_of_lt hdiv]
  exact Nat.mod_add_div c (2^32)

end VG.Proof.Mont.X86.StaticSquare

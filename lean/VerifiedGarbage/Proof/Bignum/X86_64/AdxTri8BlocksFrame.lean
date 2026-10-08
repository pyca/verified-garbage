import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8FullBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

def diagonalRanges (w k : Nat) : List (Nat × Nat) := [(rawBase w,128*k),(8*sFn 12,8)]

def blockCross (m : Mem) (B : Addr) (e : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => blockCross m B e n+2^(1024*n)*AdxSquare.crossValue m B (e+64*n) 8

structure BlocksInv (s₀ : State) (B : Addr) (Z w a k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi=B
  indexI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 (8*k)
  keep : Keep mmRegs s₀ s
  frame : Frm B (diagonalRanges w k) s₀.mem s.mem
  val : wv s.mem B (rawBase w) (16*k)=blockCross s₀.mem B (slot w a) k

theorem diagonal_hdr {m m' : Mem} {B : Addr} {w k : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (hf : Frm B (diagonalRanges w k) m m') : Hdr m' B w mi := by
  have low (j : Nat) (hj : j<16) : word m' B (8*j)=word m B (8*j) := by
    apply hf.word_eq
    · intro r hr
      simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega
    · omega
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun j hj => (low (sArr j) (by unfold sArr; omega)).trans (hh.harr j hj)⟩

theorem diagonal_ops {m m' : Mem} {B : Addr} {w k : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (hf : Frm B (diagonalRanges w k) m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega

theorem diagonal_input {m m' : Mem} {B : Addr} {w a k I : Nat}
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hk : 8*k≤w) (hi : I+8≤w)
    (hZ : slot w 8≤2^64) (hf : Frm B (diagonalRanges w k) m m') :
    AdxSquare.crossValue m' B (slot w a+8*I) 8=AdxSquare.crossValue m B (slot w a+8*I) 8 := by
  have ar := AdxRect8.tile_ranges hi hi ha ha1 ha2
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  apply AdxSquare.crossValue_congr
  intro j hj
  apply hf.word_eq
  · intro r hr
    simp only [diagonalRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;>
      simp only [rawBase,slot,hdrBytes,sFn,aAcc,aTmp] at * <;> omega
  · omega

end VG.Proof.Bignum.X86_64.AdxTri8

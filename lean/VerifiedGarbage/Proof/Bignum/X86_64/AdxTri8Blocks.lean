import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8BlocksStep

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)

theorem blocks_ok {s : State} {B : Addr} {Z w a n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hw : w<2^31) (hwN : w=8*n) (hn : 0<n)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    (hz : ∀ j<2*w, word s.mem B (rawBase w+8*j)=0) :
    WP isa (AdxTri8.blocks a) s (BlocksInv s B Z w a n mi) := by
  have nowrap := hs.nowrap
  have iZ : 8*sFn 12+8≤Z := by
    have := hdr_lt_slot w 8 (show sFn 12<32 by decide); omega
  have init : WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s fun t =>
      t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off B (8*sFn 12)) (0 : BitVec 64)) _ rfl
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ]; rfl
  unfold AdxTri8.blocks
  refine WP.seq (WP.mono init fun u ⟨mu,ku⟩ => ?_)
  have ou : Outside B (8*sFn 12) 8 s.mem u.mem := by rw [mu]; exact writeW_outside _ _ _ (by decide)
  have fu : Frm B (diagonalRanges w 0) s.mem u.mem := Frm.of_outside ou (by simp [diagonalRanges])
  have h0 : BlocksInv s B Z w a 0 mi u :=
    ⟨hs.congr ku.2.2,diagonal_hdr hh fu,(ku.gpr (by decide)).trans hd,by rw [mu,word_writeW_self]; rfl,
      ku.mono (by decide),fu,rfl⟩
  exact wp_upto (a := 0) (N := n) hn (BlocksInv s B Z w a · mi)
    (fun _ _ hk _ h => blockStep_ok hZ hw hwN hk ha ha1 ha2 hz h) (fun _ h => h) h0

end VG.Proof.Bignum.X86_64.AdxTri8

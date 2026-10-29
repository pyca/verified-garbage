module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSquareLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
/-! Complete precomputation of the next comb tooth using the shared squaring kernel. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/CounterInit.lean`, which only this module imported.
section

/-! Initialize the public squaring counter from the cached row-count header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem counterInit_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (rows : word s.mem B (8*sRows)=BitVec.ofNat 64 n) :
 WP isa (.block [ldh .x3 sRows,sth .x3 sI]) s fun t =>
 Good t B Z w mi ∧ Counter B n t ∧ Outside B (8*sI) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 change WP isa (.block ([ldh .x3 sRows]++[sth .x3 sI])) s _
 rw [WP.block_append_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 n ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sRows<32 by decide),header_read good room (show sRows<32 by decide),rows]
 · rintro u ⟨⟨value,memU⟩,restU⟩
   have goodU : Good u B Z w mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (store_control_ok goodU room (by decide : 16≤sI) (by decide : sI<32) .x3) ?_
   rintro t ⟨goodT,memT,frame,restT⟩
   refine ⟨goodT,?_,?_,(restU.trans restT).mono (by simp)⟩
   · unfold Counter
     rw [memT,word_writeW_self,value]
   · rw [←memU];exact frame

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def basisSquareRanges (w : Nat) : List (Nat × Nat) := squareRanges w++[(slot w 5,8*(w+2))]

theorem precomputeSquares_ok (M : Mont) {s : State} {p : Parameters} {E n : Nat}
 (basis : Basis p E s) (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 n) (positive : 0<n) (size : n<2^64) :
 WP isa (Precompute.squares M.mm) s fun t =>
 Basis p (E*2^n) t ∧ Power p (E*2^n) t ∧
 Frm p.B (basisSquareRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.squares
 rw [WP.seq_iff]
 refine WP.mono (basis_to_power basis) ?_
 rintro a ⟨powerA,_,frameA,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (counterInit_ok powerA.good p.room ((arrays_header frameA (by decide)).trans rows)) ?_
 rintro b ⟨goodB,counterB,frameB,restB⟩
 have powerB := powerA.after_header goodB frameB (by decide : sI<32)
 rw [WP.seq_iff]
 refine WP.mono (precomputeSquareLoop_ok M powerB counterB positive size) ?_
 rintro c ⟨powerC,_,frameC,restC⟩
 refine WP.mono (power_to_basis powerC) ?_
 rintro t ⟨basisT,powerT,frameT,restT⟩
 have first : Frm p.B (basisSquareRanges p.w) s.mem a.mem :=
  Frm.of_arrays frameA (by simp [basisSquareRanges,squareRanges])
 have second : Frm p.B (basisSquareRanges p.w) a.mem b.mem :=
  Frm.of_outside frameB (by simp [basisSquareRanges,squareRanges])
 have third : Frm p.B (basisSquareRanges p.w) b.mem c.mem :=
  frameC.mono (fun r hr => List.mem_append_left _ hr)
 have fourth : Frm p.B (basisSquareRanges p.w) c.mem t.mem :=
  Frm.of_arrays frameT (by simp [basisSquareRanges])
 exact ⟨basisT,powerT,((first.trans second).trans third).trans fourth,
  (((restA.trans restB).trans restC).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

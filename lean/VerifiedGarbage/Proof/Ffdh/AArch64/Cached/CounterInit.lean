module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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

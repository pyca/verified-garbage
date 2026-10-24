module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Control stores affect only the upper header, leaving the Montgomery layout intact. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem header_read {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (hi : i<32) :
 InRegions (s.rd++s.wr) (off B (8*i)) 8 :=
 good.scr.ld (by have := hdr_lt_slot w 8 hi;omega)

theorem good_after_header {s t : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64} {rs : List Reg}
 (good : Good s B Z w mi) (lower : 16≤i) (upper : i<32)
 (frame : Outside B (8*i) 8 s.mem t.mem) (rest : Keep rs s t) (base : t.gpr .x0=B) :
 Good t B Z w mi := by
 refine ⟨good.scr.congr rest.wr,base,?_,?_,?_⟩
 · exact (frame.word (Or.inl (by unfold sW;omega)) (by unfold sW;decide)).trans good.hdr.hw
 · exact (frame.word (Or.inl (by unfold sMinv;omega)) (by unfold sMinv;decide)).trans good.hdr.hminv
 · intro j hj
   exact (frame.word (Or.inl (by unfold sArr;omega)) (by unfold sArr;omega)).trans (good.hdr.harr j hj)

theorem header_other {B : Addr} {i j : Nat} {m m' : Mem}
 (frame : Outside B (8*i) 8 m m') (_hi : i<32) (hj : j<32) (different : j≠i) :
 word m' B (8*j)=word m B (8*j) :=
 frame.word (by omega) (by omega)

theorem store_control_ok {s : State} {B : Addr} {Z w i : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32) (r : Reg) :
 WP isa (.block [sth r i]) s fun t =>
 Good t B Z w mi ∧ t.mem=s.mem.writeW (off B (8*i)) (s.gpr r) ∧
 Outside B (8*i) 8 s.mem t.mem ∧ Keep [] s t := by
 refine WP.mono (WP.keep [] (Q:=fun t =>t.mem=s.mem.writeW (off B (8*i)) (s.gpr r))
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,good.scr.st (d:=8*i) (by have := hdr_lt_slot w 8 upper;omega)]
 · rintro t ⟨mem,rest⟩
   have frame : Outside B (8*i) 8 s.mem t.mem := by
    rw [mem]
    exact writeW_outside _ _ _ (by omega)
   exact ⟨good_after_header good lower upper frame rest ((rest.gpr .x0 (by simp)).trans good.x0),mem,frame,rest⟩


theorem decrement_control_ok {s : State} {B : Addr} {Z w i n : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (lower : 16≤i) (upper : i<32)
 (positive : 0<n) (value : word s.mem B (8*i)=BitVec.ofNat 64 n) :
 WP isa (.block [ldh .x3 i,.subImm .x .x3 .x3 1,sth .x3 i]) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*i)=BitVec.ofNat 64 (n-1) ∧
 t.gpr .x3=BitVec.ofNat 64 (n-1) ∧ Outside B (8*i) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 change WP isa (.block ([ldh .x3 i,.subImm .x .x3 .x3 1]++[sth .x3 i])) s _
 rw [WP.block_append_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 (n-1) ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc upper,header_read good room upper,value,
   BitVec.ofNat_sub_ofNat_of_le (w:=64) n 1 (by decide) positive]
 · rintro u ⟨⟨count,memU⟩,restU⟩
   have goodU : Good u B Z w mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (store_control_ok goodU room lower upper .x3) ?_
   rintro t ⟨goodT,memT,frame,restT⟩
   refine ⟨goodT,?_,(restT.gpr .x3 (by simp)).trans count,?_,(restU.trans restT).mono (by simp)⟩
   · rw [memT,word_writeW_self,count]
   · rw [←memU];exact frame


theorem ofNat_nonzero {n : Nat} (fit : n<2^64) :
 (BitVec.ofNat 64 n != 0#64)=decide (0<n) := by
 by_cases zero : n=0
 · subst n;decide
 · have ne : BitVec.ofNat 64 n≠0#64 := by
    intro eq
    have h := congrArg BitVec.toNat eq
    change n%2^64=0 at h
    rw [Nat.mod_eq_of_lt fit] at h
    exact zero h
   simp [ne,Nat.pos_of_ne_zero zero]

end VG.Proof.Ffdh.AArch64.Cached

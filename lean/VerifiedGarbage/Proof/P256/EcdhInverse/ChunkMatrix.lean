import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.P256.EcdhInverse.Chunk
import VerifiedGarbage.Proof.P256.EcdhInverse.MachineExtract
import VerifiedGarbage.Proof.P256.EcdhInverse.LowUpdate

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def lowMatrix (s : State) (d : Int) : MSt :=
  msteps 20 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)

theorem neg_row_div {m : MSt} {f g : Int} (h : m.rel 20 f g) :
    (-m.u*f+-m.v*g)/2^20 = -m.f ∧ (-m.q*f+-m.r*g)/2^20 = -m.g := by
  obtain ⟨hf,hg⟩ := h
  have hf' : -m.u*f+-m.v*g=-(2^20*m.f) := by nlinarith only [hf]
  have hg' : -m.q*f+-m.r*g=-(2^20*m.g) := by nlinarith only [hg]
  rw [hf',hg']
  norm_num
  omega

def chunk20A : List Instr := chunkCode 19++extract20a++lowUpdateA

theorem chunk20A_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+40<2^62) :
    WP isa (.block chunk20A) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix s d).d ∧
      t.gpr .x8=BitVec.ofInt 64 (-(lowMatrix s d).u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-(lowMatrix s d).v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-(lowMatrix s d).q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-(lowMatrix s d).r) ∧
      ((t.gpr .x2).toNat:Int)%2^44=(-(lowMatrix s d).f)%2^44 ∧
      ((t.gpr .x3).toNat:Int)%2^44=(-(lowMatrix s d).g)%2^44 ∧
      Keeps [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x26,.x28] s t := by
  rw [chunk20A,WP.block_append_iff,WP.block_append_iff]
  have hodd := encoded_odd s d hf
  have hcon := msteps_cong hodd (encoded_cong s d) 20 (by omega)
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hcon
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 20
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 20
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 20
  refine WP.mono (chunkCode_ok s d 19 hd hz (by exact hbound)) fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  refine WP.mono (extract20a_ok t _ _ (msteps 20 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl tf tg tz) fun a ⟨au,av,aq,ar,ka⟩ => ?_
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact tz
  refine WP.mono (lowUpdateA_run a az) fun b ⟨bf,bg,kb⟩ => ?_
  have a2 : a.gpr .x2=s.gpr .x2 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have a3 : a.gpr .x3=s.gpr .x3 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have hrel := msteps_mat (d:=d) (g:=(s.gpr .x3).toNat) (show ((s.gpr .x2).toNat:Int)%2=1 by omega) 20
  obtain ⟨nf,ng⟩ := neg_row_div hrel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,
    ((kt.mono (by decide)).trans (ka.mono (by decide))).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide),td,cd]; rfl
  · rw [kb.gpr _ (by decide),au,cu]; rfl
  · rw [kb.gpr _ (by decide),av,cv]; rfl
  · rw [kb.gpr _ (by decide),aq,cq]; rfl
  · rw [kb.gpr _ (by decide),ar,cr]; rfl
  · rw [bf,au,av,a2,a3,cu,cv,shifted_lincomb,nf]; rfl
  · rw [bg,aq,ar,a2,a3,cq,cr,shifted_lincomb,ng]; rfl

def chunk20B : List Instr := chunkCode 19++extract20b++lowUpdateB

theorem chunk20B_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+40<2^62) :
    WP isa (.block chunk20B) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix s d).d ∧
      t.gpr .x12=BitVec.ofInt 64 (-(lowMatrix s d).u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-(lowMatrix s d).v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-(lowMatrix s d).q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-(lowMatrix s d).r) ∧
      ((t.gpr .x2).toNat:Int)%2^44=(-(lowMatrix s d).f)%2^44 ∧
      ((t.gpr .x3).toNat:Int)%2^44=(-(lowMatrix s d).g)%2^44 ∧
      Keeps [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x12,.x13,.x14,.x15,.x26,.x28] s t := by
  rw [chunk20B,WP.block_append_iff,WP.block_append_iff]
  have hodd := encoded_odd s d hf
  have hcon := msteps_cong hodd (encoded_cong s d) 20 (by omega)
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hcon
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 20
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 20
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 20
  refine WP.mono (chunkCode_ok s d 19 hd hz (by exact hbound)) fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  refine WP.mono (extract20b_ok t _ _ (msteps 20 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl tf tg tz) fun a ⟨au,av,aq,ar,ka⟩ => ?_
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact tz
  refine WP.mono (lowUpdateB_run a az) fun b ⟨bf,bg,kb⟩ => ?_
  have a2 : a.gpr .x2=s.gpr .x2 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have a3 : a.gpr .x3=s.gpr .x3 := by rw [ka.gpr _ (by decide),kt.gpr _ (by decide)]
  have hrel := msteps_mat (d:=d) (g:=(s.gpr .x3).toNat) (show ((s.gpr .x2).toNat:Int)%2=1 by omega) 20
  obtain ⟨nf,ng⟩ := neg_row_div hrel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,
    ((kt.mono (by decide)).trans (ka.mono (by decide))).trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide),td,cd]; rfl
  · rw [kb.gpr _ (by decide),au,cu]; rfl
  · rw [kb.gpr _ (by decide),av,cv]; rfl
  · rw [kb.gpr _ (by decide),aq,cq]; rfl
  · rw [kb.gpr _ (by decide),ar,cr]; rfl
  · rw [bf,au,av,a2,a3,cu,cv,shifted_lincomb,nf]; rfl
  · rw [bg,aq,ar,a2,a3,cq,cr,shifted_lincomb,ng]; rfl

end VG.Proof.P256.EcdhInverse

import VerifiedGarbage.Proof.P256.EcdhInverse.ChunkMatrix
import VerifiedGarbage.Proof.P256.EcdhInverse.Matrix
import VerifiedGarbage.Proof.Divstep.Packed

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def matA (s : State) := s.gpr .x12*s.gpr .x8+s.gpr .x13*s.gpr .x10
def matB (s : State) := s.gpr .x12*s.gpr .x9+s.gpr .x13*s.gpr .x11
def matC (s : State) := s.gpr .x14*s.gpr .x8+s.gpr .x15*s.gpr .x10
def matD (s : State) := s.gpr .x14*s.gpr .x9+s.gpr .x15*s.gpr .x11

structure MatState (s t : State) : Prop where
  a : t.gpr .x8=matA s
  b : t.gpr .x9=matB s
  c : t.gpr .x16=matC s
  d : t.gpr .x17=matD s

theorem MatState.keep {s t u : State} {rs : List Reg} (h : MatState s t)
    (hk : Keeps rs t u) (hr : ∀r∈[Reg.x8,.x9,.x16,.x17],r∉rs) : MatState s u :=
  ⟨(hk.gpr _ (hr _ (by simp))).trans h.a,(hk.gpr _ (hr _ (by simp))).trans h.b,
   (hk.gpr _ (hr _ (by simp))).trans h.c,(hk.gpr _ (hr _ (by simp))).trans h.d⟩

def chunk19Rows : List Instr := (encodeCode++parityCode)++rounds 10++Matrix.first++
  rounds 8++(updateStep++halfStep)

def chunk19Regs : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x16,.x17,.x26,.x28]

theorem chunk19Rows_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hbound : |d|+38<2^62) :
    WP isa (.block chunk19Rows) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (msteps 19 (encoded s d)).d ∧
      t.gpr .x4=BitVec.ofInt 64 (msteps 19 (encoded s d)).f ∧
      t.gpr .x5=BitVec.ofInt 64 (msteps 19 (encoded s d)).g ∧
      t.gpr .x27=0 ∧ MatState s t ∧ Keeps chunk19Regs s t := by
  have cut : chunk19Rows=(encodeCode++parityCode)++(rounds 10++(Matrix.first++
    (rounds 8++(updateStep++halfStep)))) := by simp only [chunk19Rows,List.append_assoc]
  rw [cut]
  apply WP.block_append
  refine WP.mono (encode_parity_ok s d hd hz) fun a ⟨ha,ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (rounds_ok ha (encoded_bounds s d) 10 (by change |d|+20<2^62; omega))
    fun b ⟨hb,kb⟩ => ?_
  apply WP.block_append
  refine WP.mono (Matrix.first_ok b) fun c ⟨ca,cb,cc,cd,_,cz,_,_,kc⟩ => ?_
  have hc : RowState (msteps 10 (encoded s d)) c := ⟨
    (kc.gpr _ (by decide)).trans hb.d,(kc.gpr _ (by decide)).trans hb.f,
    (kc.gpr _ (by decide)).trans hb.g,(kc.gpr _ (by decide)).trans hb.zero,cz.trans hb.parity⟩
  have hmat : MatState s c := by
    have keep (r : Reg) (hr : r∈[Reg.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]) : b.gpr r=s.gpr r :=
      ((ka.mono (by decide)).trans kb).gpr r ((show ∀r∈[Reg.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15],
        r∉[Reg.x1,.x4,.x5,.x6,.x26,.x28] by decide) r hr)
    refine ⟨?_,?_,?_,?_⟩
    all_goals simp only [matA,matB,matC,matD,ca,cb,cc,cd,keep .x8 (by simp),keep .x9 (by simp),
      keep .x10 (by simp),keep .x11 (by simp),keep .x12 (by simp),keep .x13 (by simp),
      keep .x14 (by simp),keep .x15 (by simp)]
  have h10 := msteps_d (encoded s d) 10
  have hd8 : |(msteps 10 (encoded s d)).d|+2*(8:Nat)<2^62 := by
    change |(msteps 10 (encoded s d)).d|≤|d|+2*10 at h10
    norm_num at h10 ⊢
    omega
  apply WP.block_append
  refine WP.mono (rounds_ok hc (rowBounds_steps (encoded_bounds s d) 10) 8 hd8)
    fun e ⟨he,ke⟩ => ?_
  have he' : RowState (msteps 18 (encoded s d)) e := by
    rw [show (18:Nat)=10+8 by decide,msteps_add]
    exact he
  have hd18 : -(2^63)≤(msteps 18 (encoded s d)).d ∧ (msteps 18 (encoded s d)).d<2^63 := by
    have h18 := msteps_d (encoded s d) 18
    change |(msteps 18 (encoded s d)).d|≤|d|+2*18 at h18
    have := neg_abs_le (msteps 18 (encoded s d)).d
    have := le_abs_self (msteps 18 (encoded s d)).d
    norm_num at h18 ⊢
    omega
  refine WP.mono (lastStep_ok he' hd18 (rowBounds_steps (encoded_bounds s d) 18))
    fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  have em : mstep (msteps 18 (encoded s d))=msteps 19 (encoded s d) := (msteps_succ ..).symm
  refine ⟨em ▸ td,em ▸ tf,em ▸ tg,tz,(hmat.keep ke (by decide)).keep kt (by decide),?_⟩
  exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
    (ke.mono (by decide))).trans (kt.mono (by decide))

def lowMatrix19 (s : State) (d : Int) : MSt :=
  msteps 19 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)

def chunk19 : List Instr := chunk19Rows++extract19++Matrix.final++Matrix.moves

def chunk19AllRegs : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x26,.x28]

theorem chunk19_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+38<2^62) :
    WP isa (.block chunk19) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (lowMatrix19 s d).d ∧
      t.gpr .x4= -(BitVec.ofInt 64 (-(lowMatrix19 s d).u)*matA s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).v)*matC s ∧
      t.gpr .x5= -(BitVec.ofInt 64 (-(lowMatrix19 s d).u)*matB s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).v)*matD s ∧
      t.gpr .x6= -(BitVec.ofInt 64 (-(lowMatrix19 s d).q)*matA s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).r)*matC s ∧
      t.gpr .x7= -(BitVec.ofInt 64 (-(lowMatrix19 s d).q)*matB s)-
        BitVec.ofInt 64 (-(lowMatrix19 s d).r)*matD s ∧
      Keeps chunk19AllRegs s t := by
  rw [chunk19]
  simp only [List.append_assoc]
  apply WP.block_append
  have hodd := encoded_odd s d hf
  have hc := msteps_cong hodd (encoded_cong s d) 19 (by omega)
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hc
  have hm := msteps_mat (d:=d) (g:=(encoded s d).g) hodd 19
  have hb := msteps_bnd d (encoded s d).f (encoded s d).g 19
  have hl := msteps_lo d (encoded s d).f (encoded s d).g 19
  refine WP.mono (chunk19Rows_ok s d hd hz hbound) fun a ⟨ad,af,ag,az,am,ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (extract19_ok a _ _ (msteps 19 (encoded s d)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) hm hb hl af ag az) fun b ⟨bu,bv,bq,br,kb⟩ => ?_
  have bm := am.keep kb (by decide)
  have bz : b.gpr .x27=0 := (kb.gpr _ (by decide)).trans az
  apply WP.block_append
  refine WP.mono (Matrix.final_ok b bz) fun c ⟨c10,c11,c12,c13,kc⟩ => ?_
  refine WP.mono (Matrix.moves_ok c) fun t ⟨t4,t5,t6,t7,kt⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,(((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ (by decide),ad,cd]
    rfl
  · rw [t4,c10,bu,bv,bm.a,bm.c,cu,cv]; rfl
  · rw [t5,c11,bu,bv,bm.b,bm.d,cu,cv]; rfl
  · rw [t6,c12,bq,br,bm.a,bm.c,cq,cr]; rfl
  · rw [t7,c13,bq,br,bm.b,bm.d,cq,cr]; rfl

end VG.Proof.P256.EcdhInverse

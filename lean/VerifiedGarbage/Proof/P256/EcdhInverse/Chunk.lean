import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.P256.EcdhInverse.Encode

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x Keeps.trans Keeps.mono)

def parityCode : List Instr := [.movz .x .x28 1 0,.tst .x .x5 .x28]

theorem parityCode_ok (s : State) :
    WP isa (.block parityCode) s fun t =>
      t.zf=decide (s.gpr .x5 &&& 1=0) ∧ Keeps [.x28] s t := by
  apply WP.of_runBlock
  simp only [parityCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',show (16*0:Nat)<Size.x.bits by decide]
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [RegUpd.gpr_write,hr,↓reduceIte]

def encoded (s : State) (d : Int) : MSt :=
  MSt.init d (((s.gpr .x2).toNat%2^20:Nat)-(2^41:Int))
    (((s.gpr .x3).toNat%2^20:Nat)-(2^62:Int))

theorem encode_parity_ok (s : State) (d : Int) (hd : s.gpr .x1=BitVec.ofInt 64 d)
    (hz : s.gpr .x27=0) :
    WP isa (.block (encodeCode++parityCode)) s fun t =>
      RowState (encoded s d) t ∧ Keeps [.x4,.x5,.x28] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (encodeCode_ok s) fun a ⟨af,ag,ka⟩ => ?_
  refine WP.mono (parityCode_ok a) fun b ⟨bz,kb⟩ => ?_
  refine ⟨⟨?_,?_,?_,?_,?_⟩,ka.trans (kb.mono (by decide))⟩
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hd
  · rw [kb.gpr _ (by decide)]; exact af
  · rw [kb.gpr _ (by decide)]; exact ag
  · rw [kb.gpr _ (by decide),ka.gpr _ (by decide)]; exact hz
  · rw [bz,ag]; simp only [ofInt_parity]; rfl

theorem encoded_bounds (s : State) (d : Int) : rowBounds (encoded s d) :=
  packed_initial_bounds d (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

def chunkCode (n : Nat) : List Instr :=
  encodeCode++parityCode++rounds n++updateStep++halfStep

theorem chunkCode_ok (s : State) (d : Int) (n : Nat)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hbound : |d|+2*(n+1)<2^62) :
    WP isa (.block (chunkCode n)) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).d ∧
      t.gpr .x4=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).f ∧
      t.gpr .x5=BitVec.ofInt 64 (msteps (n+1) (encoded s d)).g ∧
      t.gpr .x27=0 ∧ Keeps [.x1,.x4,.x5,.x6,.x26,.x28] s t := by
  rw [chunkCode,show encodeCode++parityCode++rounds n++updateStep++halfStep=
    (encodeCode++parityCode)++rounds n++(updateStep++halfStep) by simp only [List.append_assoc],
    WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (encode_parity_ok s d hd hz) fun a ⟨ha,ka⟩ => ?_
  have hn : |(encoded s d).d|+2*n<2^62 := by
    change |d|+2*n<2^62
    norm_num only [Nat.cast_add,Nat.cast_one] at hbound
    omega
  refine WP.mono (rounds_ok ha (encoded_bounds s d) n hn) fun b ⟨hb,kb⟩ => ?_
  have hd' : -(2^63)≤(msteps n (encoded s d)).d ∧
      (msteps n (encoded s d)).d<2^63 := by
    have hm := msteps_d (encoded s d) n
    have hl := neg_abs_le (msteps n (encoded s d)).d
    have hh := le_abs_self (msteps n (encoded s d)).d
    omega
  refine WP.mono (lastStep_ok hb hd' (rowBounds_steps (encoded_bounds s d) n))
    fun t ⟨td,tf,tg,tz,kt⟩ => ?_
  rw [msteps_succ]
  exact ⟨td,tf,tg,tz,((ka.mono (by decide)).trans kb).trans kt⟩

theorem encoded_cong (s : State) (d : Int) :
    (encoded s d).cong (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  all_goals
    dsimp only [encoded,MSt.init]
    norm_num
    omega

theorem encoded_odd (s : State) (d : Int) (hf : (s.gpr .x2).toNat%2=1) :
    (encoded s d).f%2=1 := by
  dsimp only [encoded,MSt.init]
  norm_num
  omega

end VG.Proof.P256.EcdhInverse

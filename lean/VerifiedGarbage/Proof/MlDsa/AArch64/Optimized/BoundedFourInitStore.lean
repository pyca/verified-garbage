import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitCode

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def storeConstant (v : BitVec 64) (off : Nat) : List Instr :=
 VG.Impl.Tbl.AArch64.const64 .x6 v ++ [.str .x .x6 .x19 off]

/-- A table word is emitted through x6 and preserves every SIMD register. -/
theorem storeConstant_ok {v : BitVec 64} {off : Nat}
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%8=0 ∧ off<32768)
    (hw : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 off) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      t.mem=s.mem.writeW (s.gpr .x19+BitVec.ofNat 64 off) v → WP isa (.block rest) t Q) :
    WP isa (.block (storeConstant v off++rest)) s Q := by
  unfold storeConstant
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 v) fun a ⟨hav,hag,has⟩ => ?_
  have ha : Only [.x6] s a := by
    refine ⟨fun r hr => hag r (by simpa using hr),?_,?_,?_,?_,?_⟩
    all_goals rw [has]
    all_goals first | rfl | exact fun _ _ => rfl
  have hs : WP isa (.block [.str .x .x6 .x19 off]) a fun t =>
      MemTo a t (a.mem.writeW (a.gpr .x19+BitVec.ofNat 64 off) (a.gpr .x6)) :=
    wp_strx ho rfl (by rw [ha.wr,ha.get .x19]; exact hw) fun _ ht => wp_nil ht
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by rfl) hs) fun t ⟨ht,hvec⟩ =>
    k t ((ha.keep.trans ht.keep).mono (by simp)) ?_ ?_
  · have hvec' : a.v=s.v := by rw [has]
    exact hvec.trans hvec' 
  · rw [ht.mem,ha.mem,ha.get .x19,hav]
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

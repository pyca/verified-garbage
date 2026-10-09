import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackLoop
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-- Parse one complete stream using the persistent width-specific constants.
The source and destination pointers are public and all 256 fields are decoded. -/
theorem parse_ok (s : State) {d off : Nat} {p : Reg} (hd : d=18 ∨ d=20)
    (hoff : off<4096) (hp : p≠.x0) (hr : ParseReady d s)
    (hsep : (Region.mk (s.gpr .x19+BitVec.ofNat 64 off) (32*d)).Disjoint ⟨s.gpr p,1024⟩)
    (h0 : ∀ j<16, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)) 16)
    (h1 : ∀ j<16, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 16) 16)
    (h2 : ∀ j<16, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 (2*d-16)) 16)
    (hw : ∀ j<16, ∀ g<4, InRegions s.wr (s.gpr p+BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (parse d p off) s (ParserState s (s.gpr .x19+BitVec.ofNat 64 off) (s.gpr p) d 16) := by
  unfold parse
  apply WP.seq
  let a := s.write .x .x0 (s.gpr .x19+BitVec.ofNat 64 off)
  let b := a.write .x .x4 (a.gpr p)
  let t := b.write .x .x11 16
  refine WP.block_cons_iff.mpr ⟨a,by simp [isa,exec,hoff,State.read,a],?_⟩
  refine WP.block_cons_iff.mpr ⟨b,by simp [isa,exec,Impl.MlKem.AArch64.mov,State.read,b],?_⟩
  refine WP.block_cons_iff.mpr ⟨t,rfl,WP.block_nil_iff.mpr ?_⟩
  refine parser_loop_ok hd (by decide) (s := t) (start := 0) ?_ hsep h0 h1 h2 hw
  refine ⟨by decide,hr.keep (fun _ _ => rfl),?_,Frame.refl _ _,?_,?_,rfl,?_,
    (fun _ _ => rfl),rfl,rfl,rfl⟩
  · intro i hi; omega
  · simp only [t,b,a,RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,Nat.mul_zero,BitVec.add_zero]
    rfl
  · simp only [t,b,a,RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,Nat.mul_zero,BitVec.add_zero,hp,ite_false]
    rfl
  · intro r h0 h4 _ h11
    simp only [t,b,a,RegUpd.gpr_write,h0,h4,h11,ite_false]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

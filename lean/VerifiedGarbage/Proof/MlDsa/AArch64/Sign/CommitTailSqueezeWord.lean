import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBlock
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInitial

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep trn2_dwords stateReg_ne)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Proof.Sha3.AArch64 (WP.cons wp_str Upd)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Serialize a pair of high lanes without spilling the resident state. -/
theorem highPair_ok {s : State} {p : Addr} {i : Nat}
    (hi : i<8) (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block [.vop (.perm .trn2 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
      .strq .v26 .x10 (16*i)]) s fun t => SqueezeKeep s t ∧
      t.mem=s.mem.write (p+BitVec.ofNat 64 (16*i)) 16
        (ofVDwords (vdword (s.v (vreg (2*i))) 1) (vdword (s.v (vreg (2*i+1))) 1)) := by
  refine wp_vop (d:=.v26) rfl fun a ha =>
    wp_strq ⟨by omega,by omega⟩ (by rw [ha.gpr,hp]) (by rw [ha.wr]; exact hout)
      fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ _ => by rw [ht.gpr,ha.gpr],fun r h26 _ => by rw [ht.v,ha.get r h26],
    ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp⟩,?_⟩
  rw [ht.mem,ha.v,ha.mem,trn2_dwords]

/-- The final high rate word is stored without touching any resident lane. -/
theorem highLast_ok {s : State} {p : Addr} (hp : s.gpr .x10=p)
    (hout : InRegions s.wr (p+128) 8) :
    WP isa (.block [.umov .x .x7 .v16 1,.str .x .x7 .x10 128]) s fun t =>
      SqueezeKeep s t ∧ t.mem=s.mem.writeW (p+128) (vdword (s.v .v16) 1) := by
  refine WP.cons (s':=s.write .x .x7 (vdword (s.v .v16) 1)) rfl ?_
  have h := Upd.write64 s .x7 (vdword (s.v .v16) 1)
  refine wp_str (by decide) (by rw [h.other .x10 (by decide),hp])
    (by rw [h.wr]; exact hout) fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨⟨fun r _ hr => (congrFun ht.gpr r).trans (h.other r hr),
    fun r _ _ => by rw [ht.vec,h.vec],ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩,?_⟩
  rw [ht.mem,h.gpr,h.mem]
  rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

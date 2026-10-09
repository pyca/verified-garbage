import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCadd2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowLoadTwo (r q : VReg) (off : Nat) : List Instr :=
 [.ldrq .v27 .x15 off,.ldrq .v29 .x15 (off+128),
  .vop (.sub .s4 .v24 .v27 r),.vop (.sub .s4 r .v29 q)]

/-- Consume the first raw register before the second lane reuses it. -/
theorem lowLoadTwo_ok {r q : VReg} {off : Nat}
    (hr24 : r≠.v24) (hr27 : r≠.v27) (hr29 : r≠.v29)
    (hq24 : q≠.v24) (hq27 : q≠.v27) (hq29 : q≠.v29)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hread' : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (k : ∀v,VChg [.v27,.v29,.v24,r] s v →
      (∀e<4,vword (v.v .v24) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v r) e) →
      (∀e<4,vword (v.v r) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16) e-vword (s.v q) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowLoadTwo r q off++rest)) s Q := by
  refine wp_ldrq (by omega) rfl hread fun s1 h1 => ?_
  refine wp_ldrq (by omega) rfl (by rw [h1.rd,h1.wr,h1.gpr]; exact hread') fun s2 h2 => ?_
  refine wp_vop (d := .v24) rfl fun s3 h3 => wp_vop (d := r) rfl fun s4 h4 => ?_
  refine k s4 ((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by simp)) ?_ ?_
  · intro e he
    rw [h4.get .v24 (Ne.symm hr24),h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v27 (by decide),h1.v,h2.get r hr29,h1.get r hr27]
  · intro e he
    rw [h4.v,VG.AArch64.vword_map2 _ _ _ he,h3.get .v29 (by decide),h2.v,
      h1.mem,h1.gpr,h3.get q hq24,h2.get q hq29,h1.get q hq27]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

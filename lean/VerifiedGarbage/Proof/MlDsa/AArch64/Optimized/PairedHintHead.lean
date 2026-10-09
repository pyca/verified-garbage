import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawNorm
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintVec

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask hintWord)

def hintOutput (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
  hintWord (vword (s.v .v11) e)
    (reduceWord (vword (s.v raw) e)+vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e)
    (vword (s.mem.read (s.gpr .x16+BitVec.ofNat 64 off) 16) e)

def hintHead (raw : VReg) (off : Nat) : List Instr := rawNorm raw ++
  ([.ldrq .v27 .x15 off,.ldrq .v26 .x16 off,.vop (.add .s4 .v24 .v24 .v27)] : List Instr) ++ hintVector

theorem hintHead_ok (raw : VReg) {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v24,.v25,.v26,.v27,.v28,.v30] s t →
      (∀e<4,vword (t.v .v25) e=hintOutput s raw off e) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintHead raw off++rest)) s Q := by
  unfold hintHead
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine rawNorm_ok raw hq hc fun a ha hv hnorm => ?_
  refine wp_ldrq ho rfl (by simpa only [ha.rd,ha.wr,ha.gpr] using hl) fun b hb => ?_
  have hbb : VChg [.v24,.v25,.v27,.v30] s b := (ha.trans hb.chg).mono (by decide)
  refine wp_ldrq ho rfl (by simpa only [hbb.rd,hbb.wr,hbb.gpr] using hh) fun c hcc => ?_
  refine wp_vop (d:=.v24) rfl fun d hd => ?_
  have hdd : VChg [.v24,.v25,.v26,.v27,.v30] s d := ((hbb.trans hcc.chg).trans hd.chg).mono (by decide)
  refine hintVector_ok
    (by intro e he; rw [hdd.get .v12 (by decide),hdd.get .v11 (by decide)]; exact hn e he)
    (by intro e he; rw [hdd.get .v13 (by decide)]; exact hz e he) fun t ht hout => ?_
  refine k t ((hdd.trans ht).mono (by decide)) ?_ ?_
  · intro e he
    rw [hout e he,hdd.get .v11 (by decide),hd.v,VG.AArch64.vword_map2 _ _ _ he,
      hcc.get .v24 (by decide),hb.get .v24 (by decide),hv e he,hcc.get .v27 (by decide),hb.v,
      ha.mem,ha.gpr,hd.get .v26 (by decide),hcc.v,hbb.mem,hbb.gpr]
    rfl
  · intro e he
    rw [ht.get .v30 (by decide),hd.get .v30 (by decide),hcc.get .v30 (by decide),
      hb.get .v30 (by decide),hnorm e he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

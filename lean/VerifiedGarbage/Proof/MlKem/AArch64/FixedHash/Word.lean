module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- One exact word absorb from the measured fixed-length generator. -/
theorem absorbWord_ok {s : State} {sc base : Reg} {off dst : Nat}
    (hb : base≠.x2) (hc2 : sc≠.x2) (hc9 : sc≠.x9) (hc10 : sc≠.x10)
    (ho : off<65536) (hd : dst%8=0 ∧ dst<32768)
    (hr : InRegions (s.rd++s.wr) (s.gpr base+BitVec.ofNat 64 off) 8)
    (hw : InRegions s.wr (s.gpr sc+BitVec.ofNat 64 dst) 8) :
    WP isa (.block (ptrTo .x2 base off ++
      ([.ldr .x .x9 .x2 0,.ldr .x .x10 sc dst,.logic .eor .x .x9 .x9 .x10,.str .x .x9 sc dst] : List Instr))) s
      fun t=>Keep [.x2,.x9,.x10] s t ∧
        t.mem=s.mem.writeW (s.gpr sc+BitVec.ofNat 64 dst)
          (s.mem.readW (s.gpr base+BitVec.ofNat 64 off) 64 ^^^
           s.mem.readW (s.gpr sc+BitVec.ofNat 64 dst) 64) := by
  refine wp_ptrTo hb.symm ho fun a ha ea=> ?_
  refine wp_ldrx (by decide) (by rw [ea,ptr_zero]) (by rw [ha.rd,ha.wr]; exact hr) fun b hb eb=> ?_
  refine wp_ldrx hd (by rw [hb.get sc (by simp [hc9]),ha.get sc (by simp [hc2])])
    (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; obtain ⟨r,hr,hc⟩:=hw; exact ⟨r,List.mem_append_right _ hr,hc⟩) fun c hc ec=> ?_
  refine wp_eor fun d hd' ed=> ?_
  have hh := ((ha.trans hb).trans hc).trans hd'
  refine wp_strx hd (by rw [hh.get sc (by simp [hc2,hc9,hc10])])
    (by rw [hh.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨(hh.keep.trans ht.keep).mono (by simp),?_⟩
  rw [ht.mem,ed,hc.get .x9,eb,ec,hd'.mem,hc.mem,hb.mem,ha.mem]

/-- One exact byte absorb from the measured fixed-length generator. -/
theorem absorbByte_ok {s : State} {sc base : Reg} {off dst : Nat}
    (hb : base≠.x2) (hc2 : sc≠.x2) (hc9 : sc≠.x9) (hc10 : sc≠.x10)
    (ho : off<65536) (hd : dst<4096)
    (hr : InRegions (s.rd++s.wr) (s.gpr base+BitVec.ofNat 64 off) 1)
    (hw : InRegions s.wr (s.gpr sc+BitVec.ofNat 64 dst) 1) :
    WP isa (.block (ptrTo .x2 base off ++
      ([.ldrb .x9 .x2 0,.ldrb .x10 sc dst,.logic .eor .x .x9 .x9 .x10,.strb .x9 sc dst] : List Instr))) s
      fun t=>Keep [.x2,.x9,.x10] s t ∧
        t.mem=s.mem.writeW (s.gpr sc+BitVec.ofNat 64 dst)
          (s.mem (s.gpr base+BitVec.ofNat 64 off) ^^^
           s.mem (s.gpr sc+BitVec.ofNat 64 dst)) := by
  refine wp_ptrTo hb.symm ho fun a ha ea=> ?_
  refine wp_ldrb (by decide) (by rw [ea,ptr_zero]) (by rw [ha.rd,ha.wr]; exact hr) fun b hb eb=> ?_
  refine wp_ldrb hd (by rw [hb.get sc (by simp [hc9]),ha.get sc (by simp [hc2])])
    (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; obtain ⟨r,hr,hc⟩:=hw; exact ⟨r,List.mem_append_right _ hr,hc⟩) fun c hc ec=> ?_
  refine wp_eor fun d hd' ed=> ?_
  have hh := ((ha.trans hb).trans hc).trans hd'
  refine wp_strb hd (by rw [hh.get sc (by simp [hc2,hc9,hc10])])
    (by rw [hh.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨(hh.keep.trans ht.keep).mono (by simp),?_⟩
  rw [ht.mem,ed,hc.get .x9,eb,ec,hd'.mem,hc.mem,hb.mem,ha.mem]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- A word squeeze leaves the state unchanged when the output is disjoint. -/
theorem squeezeWord_ok {s : State} {sc base : Reg} {src off : Nat}
    (hb : base≠.x2) (hb9 : base≠.x9)
    (ho : off<65536) (hs : src%8=0 ∧ src<32768)
    (hr : InRegions (s.rd++s.wr) (s.gpr sc+BitVec.ofNat 64 src) 8)
    (hw : InRegions s.wr (s.gpr base+BitVec.ofNat 64 off) 8) :
    WP isa (.block (([.ldr .x .x9 sc src] : List Instr) ++ ptrTo .x2 base off ++ ([.str .x .x9 .x2 0] : List Instr))) s
      fun t=>Keep [.x2,.x9] s t ∧
        t.mem=s.mem.writeW (s.gpr base+BitVec.ofNat 64 off)
          (s.mem.readW (s.gpr sc+BitVec.ofNat 64 src) 64) := by
  refine wp_ldrx hs rfl hr fun a ha ea=> ?_
  refine wp_ptrTo hb.symm ho fun b hb eb=> ?_
  refine wp_strx (by decide) (by rw [eb,ha.get base (by simp [hb9]),ptr_zero])
    (by rw [hb.wr,ha.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨((ha.keep.trans hb.keep).trans ht.keep).mono (by simp),?_⟩
  rw [ht.mem,hb.get .x9,ea,hb.mem,ha.mem]
end VG.Proof.MlKem.AArch64.FixedHash

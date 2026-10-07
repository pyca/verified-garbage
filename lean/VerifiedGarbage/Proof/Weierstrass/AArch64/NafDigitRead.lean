import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def nafMagnitude (b : BitVec 8) : Nat := if b.toNat<128 then b.toNat else 256-b.toNat

def nafNegative (b : BitVec 8) : Bool := decide (128≤b.toNat)

/-- A public counter selects one signed byte. -/
theorem nafRead_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hb : K.bits<4096) (hj : K.bits+j<size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (hm : s.mem (off base (K.bits+j))=b) (r : Reg) :
    WP isa (.block [.add .x .x16 .x0 .x19,.ldrb r .x16 K.bits]) s fun t =>
      t.gpr r=b.setWidth 64 ∧ Keeps [r,.x16] s t := by
  have hr : InRegions (s.rd++s.wr) (off base (K.bits+j)) 1 :=
    ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega) (by decide)⟩
  have he : base+BitVec.ofNat 64 j+BitVec.ofNat 64 K.bits=off base (K.bits+j) := by
    simp only [off,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [Nat.add_comm j]
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,State.load,addr,
    RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,BitVec.setWidth_eq,
    hs.x0,h19,Size.bits,Nat.mod_one,hb,and_self,he,hr,
    ite_true,read1_zext,hm,Option.map_some,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,?_,rfl,rfl,rfl,rfl⟩
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp only [RegUpd.gpr_write,hq.1,hq.2,ite_false]

private theorem nafIndex_fact : ∀ b : BitVec 8,
    let x : BitVec 64 := b.setWidth 64
    let sign := x >>> 7
    let y := x-(sign <<< 8)
    let mask := (0:BitVec 64)-sign
    (((y ^^^ mask)-mask)+1) >>> 1 = BitVec.ofNat 64 ((nafMagnitude b+1)/2) := by
  decide +kernel

/-- Decode the signed byte into the odd-table index without data-dependent shifts. -/
theorem nafIndex_ok {s : State} {b : BitVec 8} (h2 : s.gpr .x2=b.setWidth 64) :
    WP isa (.block Naf.digitIndex) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 ((nafMagnitude b+1)/2) ∧ Keeps [.x2,.x3,.x4] s t := by
  apply WP.of_runBlock
  simp only [Naf.digitIndex,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,h2,
    show 7<64 by decide,show 8<64 by decide,show 1<64 by decide,
    show 16*0<64 by decide,show 1<4096 by decide,ite_true,ite_false,reduceCtorEq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · exact nafIndex_fact b
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

private theorem nafSign_fact : ∀ b : BitVec 8,
    b.setWidth 64 >>> 7=BitVec.ofNat 64 (nafNegative b).toNat := by decide +kernel

theorem nafSignRead_ok {K : WinCfg} {s : State} {base : Addr} {size j : Nat} {b : BitVec 8}
    (hs : Scr s base size) (hb : K.bits<4096) (hj : K.bits+j<size)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) (hm : s.mem (off base (K.bits+j))=b) :
    WP isa (.block (Naf.signRead K)) s fun t =>
      t.gpr .x3=BitVec.ofNat 64 (nafNegative b).toNat ∧ Keeps [.x3,.x16] s t := by
  change WP isa (.block ([.add .x .x16 .x0 .x19,.ldrb .x3 .x16 K.bits] ++ [.lsr .x .x3 .x3 7])) s _
  rw [WP.block_append_iff]
  refine WP.mono (nafRead_ok hs hb hj h19 hm .x3) fun a ⟨ha,ka⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,ha,
    Size.bits,show 7<64 by decide,ite_true,Option.some.injEq,exists_eq_left']
  refine ⟨nafSign_fact b,?_,ka.mem,ka.rd,ka.wr,ka.sp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,ite_false]
  exact ka.gpr r (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact hr)

end VG.Proof.Weierstrass.AArch64

module

public import VerifiedGarbage.Impl.P256.VerifyTable
import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! The stores of a co-Z table entry: the point `E` into entry `x19`, the powers
of its `Z` into the entry's cache. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.P256.VerifyTable (entryAddr cacheAddr storeEntry)

theorem entryAddr_ok {base : Addr} {s : State} {m : Nat}
    (hs : s.gpr .x0=base) (hm : 1≤m) (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block entryAddr) s fun t =>
      t.gpr .x16=off base (2848+96*(m-1)) ∧ Keeps [.x1,.x2,.x16] s t := by
  apply WP.of_runBlock
  simp only [entryAddr,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1:Nat)<4096 by decide,show VG.Impl.P256.VerifyTable.K.tbl=2848 from rfl,
    show (2848:Nat)<4096 by decide,show 16*0<64 by decide,ite_true,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,hs,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le m 1 (by decide) hm]
    change base+BitVec.ofNat 64 2848+BitVec.ofNat 64 (m-1)*BitVec.ofNat 64 96=off base (2848+96*(m-1))
    rw [←BitVec.ofNat_mul]
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc,Nat.mul_comm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem cacheAddr_ok {base : Addr} {s : State} {m : Nat}
    (hs : s.gpr .x0=base) (hm : 1≤m) (hm9 : m≤9) (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block cacheAddr) s fun t =>
      t.gpr .x16=off base (6000+64*(m-1)) ∧ Keeps [.x1,.x2,.x16] s t := by
  apply WP.of_runBlock
  simp only [cacheAddr,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1:Nat)<4096 by decide,show 16*0<64 by decide,show 6<64 by decide,ite_true,
    RegUpd.gpr_write,BitVec.setWidth_eq,Size.bits,reduceCtorEq,ite_false,h19,hs,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le m 1 (by decide) hm]
    have hl : BitVec.ofNat 64 (m-1) <<< 6=BitVec.ofNat 64 (64*(m-1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : m-1<2^64)]
      omega
    simp only [hl]
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

/-- Entry `m`'s stores: `E` into its point, the powers of `Z` into its cache. -/
theorem storeEntry_ok {base : Addr} {s : State} {m : Nat}
    (hs : Scr s base 8192) (hm : 1≤m) (hm9 : m≤9)
    (h19 : s.gpr .x19=BitVec.ofNat 64 m) :
    WP isa (.block storeEntry) s fun t =>
      (∀ i<12,word t.mem base (2848+96*(m-1)+8*i)=word s.mem base (704+8*i)) ∧
      (∀ i<8,word t.mem base (6000+64*(m-1)+8*i)=word s.mem base (5400+8*i)) ∧
      KeepRegs [.x1,.x2,.x16] s t ∧
      Unch base [(2848+96*(m-1),96),(6000+64*(m-1),64)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [storeEntry,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryAddr_ok hs.x0 hm h19) fun a ⟨pa,ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Proof.P256.EcdhJac.tableStoreWords_ok (n:=12) (src:=fun i => 704+8*i) ha pa (by omega)
    (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega) 12 (by omega))
    fun b ⟨vb,kb,ob⟩ => ?_
  have hb := ha.of_keepRegs kb (by decide)
  have a19 : a.gpr .x19=BitVec.ofNat 64 m := by rw [ka.gpr _ (by decide),h19]
  have b19 : b.gpr .x19=BitVec.ofNat 64 m := by rw [kb.gpr _ (by decide),a19]
  rw [WP.block_append_iff]
  refine WP.mono (cacheAddr_ok hb.x0 hm hm9 b19) fun d ⟨pd,kd⟩ => ?_
  have hd := hb.of_keeps kd (by decide)
  refine WP.mono (Proof.P256.EcdhJac.tableStoreWords_ok (n:=8) (src:=fun i => 5400+8*i) hd pd (by omega)
    (by intro i hi; omega) (by intro i hi; omega) (by intro i hi; omega) 8 (by omega))
    fun t ⟨vt,kt,ot⟩ => ?_
  have od : Outside base (6000+64*(m-1)) 64 b.mem t.mem := by simpa only [kd.mem] using ot
  refine ⟨fun i hi => ?_,fun i hi => ?_,?_,fun x hx => ?_⟩
  · rw [od.word (by omega) (by omega),vb i hi,ka.mem]
  · rw [vt i hi,kd.mem,ob.word (by omega) (by omega),ka.mem]
  · exact ((Keeps.regs ka).trans (kb.mono (by decide))).trans
      ((Keeps.regs kd).trans (kt.mono (by decide)))
  · rw [od x (hx (6000+64*(m-1),64) (by simp)),ob x (hx (2848+96*(m-1),96) (by simp)),ka.mem]

end VG.Proof.P256.VerifyTable

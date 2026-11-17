module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorScan
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.AArch64.CrtWindowVectorClear`, which this module and modules that import it used -/

section

/-! Clear the four selection accumulators without disturbing scalar state. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem zeroVector_ok (s : State) (r : VReg) :
    WP isa (.block [.vop (.movi0 r)]) s fun t =>
      t.v r = 0 ∧ VKeep [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, VOp.eval, Option.map_some, runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.v_setV_self _ _ _, VKeep.setV _ _ _⟩

theorem clearVectors_ok (rs : List VReg) (s : State) :
    WP isa (.block (rs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ r ∈ rs, t.v r = 0) ∧ VKeep rs s t := by
  induction rs generalizing s with
  | nil => exact WP.block_nil ⟨by simp, ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩⟩
  | cons r rs ih =>
    rw [List.map_cons, show .vop (.movi0 r) :: rs.map (fun r => Instr.vop (.movi0 r)) =
      [.vop (.movi0 r)] ++ rs.map (fun r => Instr.vop (.movi0 r)) from rfl,
      WP.block_append_iff]
    refine WP.mono (zeroVector_ok s r) fun u ⟨hu, ku⟩ => ?_
    refine WP.mono (ih u) fun t ⟨ht, kt⟩ => ⟨?_, ku.trans kt⟩
    intro q hq
    by_cases h : q ∈ rs
    · exact ht q h
    · have he : q = r := (List.mem_cons.mp hq).resolve_right h
      subst q
      exact (kt.v r h).trans hu

theorem clearAccs_ok (s : State) :
    WP isa (.block (accs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ i < 4, t.v (acc i) = 0) ∧ VKeep accs s t := by
  refine WP.mono (clearVectors_ok accs s) fun t ⟨ht, kt⟩ => ⟨?_, kt⟩
  intro i hi
  exact ht (acc i) ((by decide : ∀ i < 4, acc i ∈ accs) i hi)

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! ### `Bignum.AArch64.CrtWindowVectorHead`, which this module and modules that import it used -/

section

/-! Start each SIMD block at the same public offset in every table entry. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

def blockHead (n : Nat) : List Instr :=
  [ldh .x16 (sArr Crt.aT), .sub .x .x16 .x17 .x16,
   ldh .x3 Crt.sTab, .add .x .x16 .x16 .x3,
   .vop (.movi0 .v23), movi .x14 n]

theorem exec_zeroVector (s : State) (r : VReg) :
    exec (.vop (.movi0 r)) s = some (s.setV r 0) := rfl

theorem blockHead_ok {s : State} {P : Addr} {w b n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b)) :
    WP isa (.block (blockHead n)) s fun t =>
      (t.gpr .x16 = off P (slot w 8 + 64 * b) ∧ t.gpr .x14 = BitVec.ofNat 64 n ∧
       t.v = (s.setV .v23 0).v ∧ t.mem = s.mem) ∧ Keep [.x16,.x3,.x14] s t := by
  have hp' : off P (slot w Crt.aT + 64 * b) - off P (slot w Crt.aT) =
      BitVec.ofNat 64 (64 * b) := by
    rw [off, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.add_sub_cancel_left _ _
  rcases hN with rfl | rfl <;>
  · refine WP.keep _ ?_ rfl rfl rfl
    brun [blockHead, hc.good.x0, hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
      hdr_enc (show Crt.sTab < 32 by decide), hc.ld (i := sArr Crt.aT) (by decide),
      hc.ld (i := Crt.sTab) (by decide), hc.good.hdr.harr Crt.aT (by decide), ht, hp, hp',
      exec_zeroVector, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV]
    refine ⟨BitVec.add_comm _ _ |>.trans (off_add P (slot w 8) (64 * b)), ?_⟩
    simp only [State.setV, RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector

end

end

/-! Initialize the complete invariant for a vector scan of 16 or 32 rows. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem startScan_ok {s : State} {P : Addr} {w b v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1) :
    WP isa (.block (blockHead n ++ accs.map fun r => .vop (.movi0 r))) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧
      ScanInv t (off P (slot w 8 + 64 * b)) (8 * (w + 2)) v 0 t ∧
      t.mem = s.mem ∧ Keep [.x16,.x3,.x14] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (blockHead_ok hN hc ht hp) fun u ⟨⟨h16,h14,hv,hm⟩, ku⟩ => ?_
  refine WP.mono (clearAccs_ok u) fun t ⟨hz, kt⟩ => ?_
  have keep : Keep [] u t := ⟨fun r _ => congrFun kt.gpr r, kt.rd, kt.wr, kt.sp,
    fun r hr => congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (kt.v r ((by decide : ∀ r ∈ preservedV, r ∉ accs) r hr))⟩
  refine ⟨by rw [kt.gpr, h14], ⟨rfl, Keep.refl _ _, ?_, ?_, ?_, ?_, ?_⟩,
    kt.mem.trans hm, (ku.trans keep).mono (by decide)⟩
  · simpa only [Nat.mul_zero, BitVec.add_zero, kt.gpr] using h16
  · rw [kt.v .v23 (by decide), hv, RegUpd.v_setV_self]
    rfl
  · rw [kt.v .v22 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h22
  · rw [kt.v .v24 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h24
  · intro i hi
    simpa only [Nat.not_lt_zero, ite_false] using hz i hi

end VG.Proof.Bignum.AArch64.WindowVector

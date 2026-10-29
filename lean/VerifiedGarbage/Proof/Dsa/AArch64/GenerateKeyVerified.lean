module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyGenerateCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyPublic
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBlockCT
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
/-! # Complete verification of DSA key generation for every AArch64 backend -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/GenerateKeyConstantTime.lean`, which only this module imported.
section

/-! # Key generation's leak: the domain, its status, its draws used and its trace -/

section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_finish_public_pre {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    {status : BitVec 64} (hr : KeygenState h used t)
    (hz : word t.mem (randomBase s) Random.oStatus = status) :
    RandomFinishPre (randomFinishPublic s status) t := by
  refine ⟨hr.scr, hr.sp,
    hr.saved (40, s.gpr .x0) (by simp [keygenSavedValues]), ?_,
    hr.saved (56, s.gpr .x2) (by simp [keygenSavedValues]), hz, ?_, (s.gpr .x1).isLt, ?_, ?_⟩
  · change word t.mem (randomBase s) Random.oOutLen = BitVec.ofNat 64 (s.gpr .x1).toNat
    simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [keygenSavedValues])
  · change 0 < (s.gpr .x1).toNat
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · intro j hj
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro d hd
    exact ((h.stackOut.sub_left (keygen_frame_sub h)).sub_left (Offset.sub_base _ hd)).sep
      (Region.contains_self _ _) (Region.contains_self _ _)

theorem keygen_finish_agreement {extra : Nat} {s t a b : State} {hs : GenerateKeyABI extra s}
    {ht : GenerateKeyABI extra t} {useda usedb : Nat} {status : BitVec 64}
    (ha : KeygenState hs useda a) (hb : KeygenState ht usedb b) (hpub : KeygenPublicAgree s t)
    (hsa : word a.mem (randomBase s) Random.oStatus = status)
    (hsb : word b.mem (randomBase t) Random.oStatus = status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa RandomSign.finish a tsa u) (eb : Exec isa RandomSign.finish b tsb w) : tsa = tsb := by
  have hpa := keygen_finish_public_pre ha hsa
  have hpb := keygen_finish_public_pre hb hsb
  have he : randomFinishPublic s status = randomFinishPublic t status := by
    unfold randomFinishPublic
    rw [hpub.base, hpub.regs .x0 (by decide), hpub.regs .x1 (by decide), hpub.regs .x2 (by decide)]
  rw [← he] at hpb
  exact (random_finish_ct _ _ _ _ _ _ ⟨_, hpa, hpb, ha.sp.trans (hpub.base.trans hb.sp.symm)⟩ ea eb).1

theorem keygen_alloc_sp (s : State) : (allocated Random.frameBytes s).sp = randomBase s := rfl

theorem keygen_body_ct (v : Backend) {s t : State}
    (hs : GenerateKeyABI v.stack s) (ht : GenerateKeyABI v.stack t) (hp : KeygenPublicAgree s t)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (htrace : (keygenResult s).trace = (keygenResult t).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveKey v.mul)) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveKey v.mul)) (allocated Random.frameBytes t) tsb w) :
    tsa = tsb := by
  unfold GenerateKey.body at ea eb
  cases ea with | seq eaA eaR => cases eaR with | seq eaCall eaR2 =>
  cases eaR2 with | seq eaT eaR3 => cases eaR3 with | seq eaI eaF =>
  cases eb with | seq ebA ebR => cases ebR with | seq ebCall ebR2 =>
  cases ebR2 with | seq ebT ebR3 => cases ebR3 with | seq ebI ebF =>
  have hA := (keygen_head_ct _ _ _ _ _ _ (by
    dsimp only
    rw [keygen_alloc_sp, keygen_alloc_sp]
    exact hp.base) eaA ebA).1
  obtain ⟨ha, hsta, hQa, a1, a2, a3, a4, a5, a6⟩ := random_post_of_exec (keygen_head hs) eaA
  obtain ⟨hb, hstb, hQb, b1, b2, b3, b4, b5, b6⟩ := random_post_of_exec (keygen_head ht) ebA
  have hCall := (keygen_check_ct v _ _ _ _ _ _
    ⟨s, t, hs, ht, ha, hb, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, hp⟩ eaCall ebCall).1
  obtain ⟨hua, hwa, haxa⟩ := random_post_of_exec (keygen_check_step v ha a1 a2 a3 a4 a5 a6) (.seq eaCall eaT)
  obtain ⟨hub, hwb, haxb⟩ := random_post_of_exec (keygen_check_step v hb b1 b2 b3 b4 b5 b6) (.seq ebCall ebT)
  obtain ⟨-, -, hspa, -⟩ := random_post_of_exec
    (keygen_check_call v hs ha.sp a1 a2 a3 a4 a5 a6 ha.rd ha.wr) eaCall
  obtain ⟨-, -, hspb, -⟩ := random_post_of_exec
    (keygen_check_call v ht hb.sp b1 b2 b3 b4 b5 b6 hb.rd hb.wr) ebCall
  have hT := (keygen_testCheck_ct _ _ _ _ _ _ (by
    dsimp only
    rw [hspa, hspb, ha.sp, hb.sp]
    exact hp.base) eaT ebT).1
  have hct := hp.checked
  cases hcs : keygenChecked s with
  | false =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteF hc' _ => simp only [eval, State.read, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ eaN =>
    cases ebI with
    | iteF hc' _ => simp only [eval, State.read, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ ebN =>
    obtain ⟨hna, rfl⟩ := keygen_block_nil eaN
    obtain ⟨hnb, rfl⟩ := keygen_block_nil ebN
    have hF := keygen_finish_agreement hua hub hp
      (by rw [hwa _ (by decide), hsta]) (by rw [hwb _ (by decide), hstb]) eaF ebF
    rw [hA, hCall, hT, hna, hnb, hF]
  | true =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteT hc' _ => simp only [eval, State.read, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ eaG =>
    cases ebI with
    | iteT hc' _ => simp only [eval, State.read, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ ebG =>
    have hQa' := (hwa _ (by decide)).trans hQa
    have hQb' := (hwb _ (by decide)).trans hQb
    have hG := keygen_generate_ct v hua hub hQa' hQb' hcs hp hstatus htrace eaG ebG
    obtain ⟨hga, hgsa, -⟩ := random_post_of_exec (keygen_generate v hua hQa' hcs) eaG
    obtain ⟨hgb, hgsb, -⟩ := random_post_of_exec (keygen_generate v hub hQb' hct.symm) ebG
    rw [hstatus] at hgsa
    have hF := keygen_finish_agreement hga hgb hp hgsa hgsb eaF ebF
    rw [hA, hCall, hT, hG, hF]

theorem keygen_alloc {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩

theorem keygen_constantTime (v : Backend) :
    ConstantTime isa (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pub
      (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
        (Generate.deriveKey v.mul)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have hsa := generateKeyABI_of hs
  have hta := generateKeyABI_of ht
  obtain ⟨hp, hstatus, _, htrace⟩ := keygen_public_related hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [keygen_alloc hsa, Option.some.injEq] at hap
      rw [keygen_alloc hta, Option.some.injEq] at hbp
      subst hap
      subst hbp
      have hh := keygen_body_ct v hsa hta hp hstatus htrace hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def keygenSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 424 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 276 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if a = 0x1000000000009 then 0x80 else if a = 0x1000000000011 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x1000000000000, 24⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

private theorem sat_arg_0 : stackArg keygenSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg keygenSatState 1 = 32768 := by decide +kernel
private theorem sat_arg_2 : stackArg keygenSatState 2 = 9216 := by decide +kernel

theorem keygen_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨keygenSatState, ?_⟩
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, keygenSatState] at h₁ h₂; bv_omega)

theorem keygen_verified (v : Backend) :
    Verified target (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
        (Generate.deriveKey v.mul))
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) :=
  ⟨keygen_correct v, keygen_constantTime v, keygen_satisfiable v⟩

end VG.Proof.Dsa.AArch64

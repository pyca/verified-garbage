module

import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyGenerateCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyPublic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyBlockCT
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyBody
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Key generation's leak: the domain, its status, its draws used and its trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_finish_public_pre {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    {status : BitVec 64} (hr : KeygenState h used t)
    (hz : word t.mem (randomBase s) Random.oStatus = status) :
    RandomFinishPre (randomFinishPublic s status) t := by
  refine ⟨hr.scr, hr.sp,
    hr.saved (40, s.gpr .rdi) (by simp [keygenSavedValues]), ?_,
    hr.saved (56, s.gpr .rdx) (by simp [keygenSavedValues]), hz, ?_, (s.gpr .rsi).isLt, ?_, ?_⟩
  · change word t.mem (randomBase s) Random.oOutLen = BitVec.ofNat 64 (s.gpr .rsi).toNat
    simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .rsi) (by simp [keygenSavedValues])
  · change 0 < (s.gpr .rsi).toNat
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · intro j hj
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .rsi).isLt)⟩
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
    rw [hpub.base, hpub.regs .rdi (by decide), hpub.regs .rsi (by decide), hpub.regs .rdx (by decide)]
  rw [← he] at hpb
  exact (random_finish_ct _ _ _ _ _ _ ⟨_, hpa, hpb⟩ ea eb).1

theorem keygen_alloc_sp (s : State) : (allocState Random.frameBytes s).gpr .rsp = randomBase s := by
  simp only [allocState, State.setReg, ite_true]; rfl

theorem keygen_testCheck_mx {t : State} :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) t fun u =>
      ((u.mem = t.mem ∧ u.zf = some (((t.gpr .rax).setWidth 32).toNat == 0)) ∧ Keep [.rax] t u) ∧
        u.mxcsr = t.mxcsr :=
  WP.mono_mx (by decide) keygen_test_check (fun _ h hm => ⟨h, hm⟩)

theorem keygen_body_ct (v : Backend) {s t : State}
    (hs : GenerateKeyABI v.stack s) (ht : GenerateKeyABI v.stack t) (hp : KeygenPublicAgree s t)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (htrace : (keygenResult s).trace = (keygenResult t).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveKey v.sq v.mul)) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveKey v.sq v.mul)) (allocState Random.frameBytes t) tsb w) :
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
  obtain ⟨hua, hwa, haxa⟩ := random_post_of_exec (keygen_check_step v ha a1 a2 a3 a4 a5 a6) eaCall
  obtain ⟨hub, hwb, haxb⟩ := random_post_of_exec (keygen_check_step v hb b1 b2 b3 b4 b5 b6) ebCall
  have hT := (keygen_testCheck_ct _ _ _ _ _ _ (by
    dsimp only
    rw [hua.sp, hub.sp]
    exact hp.base) eaT ebT).1
  obtain ⟨⟨⟨hma, hza⟩, hka⟩, hmxa⟩ := random_post_of_exec keygen_testCheck_mx eaT
  obtain ⟨⟨⟨hmb, hzb⟩, hkb⟩, hmxb⟩ := random_post_of_exec keygen_testCheck_mx ebT
  have hsa := hua.of_frame (by rw [hma]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hma])
    (hka.mono (by decide)) (by rw [hmxa])
  have hsb := hub.of_frame (by rw [hmb]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hmb])
    (hkb.mono (by decide)) (by rw [hmxb])
  have hct := hp.checked
  cases hcs : keygenChecked s with
  | false =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteF hc' _ => simp only [eval, hza, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ eaN =>
    cases ebI with
    | iteF hc' _ => simp only [eval, hzb, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ ebN =>
    obtain ⟨hna, rfl⟩ := keygen_block_nil eaN
    obtain ⟨hnb, rfl⟩ := keygen_block_nil ebN
    have hF := keygen_finish_agreement hsa hsb hp
      (by rw [hma, hwa _ (by decide), hsta]) (by rw [hmb, hwb _ (by decide), hstb]) eaF ebF
    rw [hA, hCall, hT, hna, hnb, hF]
  | true =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteT hc' _ => simp only [eval, hza, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ eaG =>
    cases ebI with
    | iteT hc' _ => simp only [eval, hzb, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ ebG =>
    have hQa' := (hwa _ (by decide)).trans hQa
    have hQb' := (hwb _ (by decide)).trans hQb
    rw [← hma] at hQa'
    rw [← hmb] at hQb'
    have hG := keygen_generate_ct v hsa hsb hQa' hQb' hcs hp hstatus htrace eaG ebG
    obtain ⟨hga, hgsa, -⟩ := random_post_of_exec (keygen_generate v hsa hQa' hcs) eaG
    obtain ⟨hgb, hgsb, -⟩ := random_post_of_exec (keygen_generate v hsb hQb' hct.symm) ebG
    rw [hstatus] at hgsa
    have hF := keygen_finish_agreement hga hgb hp hgsa hgsb eaF ebF
    rw [hA, hCall, hT, hG, hF]

theorem keygen_alloc {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocState Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocState]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩

theorem keygen_constantTime (v : Backend) :
    ConstantTime isa (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pub
      (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.sq v.mul)
        (Generate.deriveKey v.sq v.mul)) := by
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

end VG.Proof.Dsa.X86_64

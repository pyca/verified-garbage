module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInitCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishAgreement
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Compose initialization, retries, and publication for valid subgroup moduli. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init_agreement {extra : Nat} {s t : State}
    (hs : RandomSignABI extra s) (ht : RandomSignABI extra t) (hp : RandomSignPublicAgree s t)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
  have he : (⟨randomBase s, s.gpr .rcx + s.gpr .r9, randomQBytes s⟩ : RandomPreparePublic) =
      ⟨randomBase t, t.gpr .rcx + t.gpr .r9, randomQBytes t⟩ := by
    rw [hp.base, hp.regs .rcx (by decide), hp.regs .r9 (by decide), hp.qbytes]
  exact (random_sign_init_ct _ _ _ _ _ _
    ⟨_, ⟨s, extra, hs, rfl, rfl⟩, t, extra, ht, rfl, he⟩ ea eb).1

theorem random_sign_cmp_zero_ct : RelCT isa (fun _ _ => True) (.block [.alu .cmp .rax (.imm 0)]) (fun _ _ => True) := by
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)).mono
    (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)

private theorem test_zero_mx {s : State} :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) s fun t =>
      ((t.mem = s.mem ∧ t.zf = some (s.gpr .rax == 0)) ∧ Keep [.rax] s t) ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide) random_sign_test_zero (fun _ h hm => ⟨h, hm⟩)

def randomSignTail (v : Backend) : Prog isa :=
  .seq (.block [.alu .cmp .rax (.imm 0)])
    (.seq (.ite .e (.block [.store (Random.sp Random.oStatus) .rax])
      (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.sq v.mul)) randomSignStatusTest) .e)) RandomSign.finish)

private theorem valid_tail (v : Backend) {s t a b : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (ha : RandomSignRunning hs hqs 0 8 a) (hb : RandomSignRunning ht hqt 0 8 b)
    (hra : a.gpr .rax = 1) (hrb : b.gpr .rax = 1) (hp : RandomSignPublicAgree s t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State} (ea : Exec isa (randomSignTail v) a tsa u)
    (eb : Exec isa (randomSignTail v) b tsb w) : tsa = tsb := by
  cases ea with
  | seq eac ear => cases ear with
    | seq eai eaf =>
      cases eb with
      | seq ebc ebr => cases ebr with
        | seq ebi ebf =>
          have hcmp := (random_sign_cmp_zero_ct _ _ _ _ _ _ trivial eac ebc).1
          obtain ⟨⟨⟨ham, haz⟩, hka⟩, hmxa⟩ := random_post_of_exec test_zero_mx eac
          obtain ⟨⟨⟨hbm, hbz⟩, hkb⟩, hmxb⟩ := random_post_of_exec test_zero_mx ebc
          have har := ha.congr ham hka hmxa
          have hbr := hb.congr hbm hkb hmxb
          rw [hra] at haz
          rw [hrb] at hbz
          cases eai with
          | iteT hc _ => simp only [eval, haz] at hc; contradiction
          | iteF _ eal =>
            cases ebi with
            | iteT hc _ => simp only [eval, hbz] at hc; contradiction
            | iteF _ ebl =>
              have hloop := (random_sign_loop_ct v hp 8 _ _ _ _ _ _
                ⟨by decide, by decide, 0, har, hbr, htrace⟩ eal ebl).1
              obtain ⟨⟨_, hrunA⟩, hsta, _⟩ := random_post_of_exec (random_sign_loop_correct v har (by decide) (by decide)) eal
              obtain ⟨⟨_, hrunB⟩, hstb, _⟩ := random_post_of_exec (random_sign_loop_correct v hbr (by decide) (by decide)) ebl
              rw [← hstatus] at hstb
              have hfinish := random_finish_agreement hs ht hrunA.finishPre hrunB.finishPre hp hsta hstb eaf ebf
              rw [hcmp, hloop, hfinish]

theorem random_sign_body_valid_ct (v : Backend) {s t : State}
    (hs : RandomSignABI v.stack s) (ht : RandomSignABI v.stack t) (hp : RandomSignPublicAgree s t)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s))
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul)) (allocState Random.frameBytes t) tsb w) : tsa = tsb := by
  have hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t) := by rw [← hp.qbytes]; exact hq
  cases ea with
  | seq eae ear => cases ear with
    | seq eap eat =>
      cases eb with
      | seq ebe ebr => cases ebr with
        | seq ebp ebt =>
          have hinit := random_sign_init_agreement hs ht hp (.seq eae eap) (.seq ebe ebp)
          obtain ⟨hra, har⟩ := random_post_of_exec (random_sign_init_running hs hq) (.seq eae eap)
          obtain ⟨hrb, hbr⟩ := random_post_of_exec (random_sign_init_running ht hqt) (.seq ebe ebp)
          have htail := valid_tail v har hbr hra hrb hp htrace hstatus eat ebt
          rw [← List.append_assoc, ← List.append_assoc, hinit, htail]

end VG.Proof.Dsa.X86_64

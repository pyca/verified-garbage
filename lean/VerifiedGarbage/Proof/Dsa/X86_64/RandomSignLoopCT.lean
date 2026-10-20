module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttemptCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignStep
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSampleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttemptCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSampleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The outer retry loop reveals the sampling and signing decisions specified by its trace. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSignStatusTest : Prog isa :=
  .block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 4)]

private theorem status_test {s : State} {B : Addr} {status : BitVec 64}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hv : word s.mem B Random.oStatus = status) :
    WP isa randomSignStatusTest s fun t =>
      (t.zf = some (status == 4) ∧ t.mem = s.mem ∧ Keep [.rax] s t) ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx (by decide) (random_statusTest_ok hs hsp hv) (fun _ h hm => ⟨h, hm⟩)

private theorem status_ct : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    randomSignStatusTest (fun _ _ => True) := by
  refine (two_taint (Φ := fun (B : Addr) s => s.gpr .rsp = B) [.rsp] ?_ (by taint_decide)).mono
    (fun s _ h => ⟨s.gpr .rsp, rfl, h.symm⟩) (fun _ _ _ => trivial)
  intro B s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.trans ht.symm

def RandomSignLoopAgree {extra : Nat} {s t : State} (hs : RandomSignABI extra s) (ht : RandomSignABI extra t)
    (hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t))
    (fuel : Nat) (a b : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning hs hqs used fuel a ∧ RandomSignRunning ht hqt used fuel b ∧
    (randomSignRemaining (randomInput s) used fuel).trace = (randomSignRemaining (randomInput t) used fuel).trace

theorem random_sign_loop_ct (v : Backend) {s t : State}
    {hs : RandomSignABI v.stack s} {ht : RandomSignABI v.stack t}
    {hqs : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {hqt : 1 < Spec.Dsa.decodeBE (randomQBytes t)}
    (hpub : RandomSignPublicAgree s t) (fuel : Nat) :
    RelCT isa (RandomSignLoopAgree hs ht hqs hqt fuel)
      (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.sq v.mul)) randomSignStatusTest) .e)
      (fun _ _ => True) := by
  refine RelCT.loop (M := isa) (RandomSignLoopAgree hs ht hqs hqt) ?_ fuel
  intro n a b tsa tsb u w ⟨hf, hn, used, ha, hb, htrace⟩ ea eb
  cases n with
  | zero => omega
  | succ n =>
    have hdraw := congrArg randomSamplingTrace htrace
    rw [random_sign_trace_draw, random_sign_trace_draw] at hdraw
    obtain ⟨hused, hscalar, hsampleStatus⟩ := random_sign_draw_agree hpub hdraw
    have hstatus := random_sign_attempt_status_agree htrace hscalar hsampleStatus
    cases ea with
    | seq eaa eat =>
      cases eb with
      | seq eba ebt =>
        have hattempt := random_sign_attempt_agreement v ha hb hpub (by omega) htrace eaa eba
        have hpa := random_post_of_exec (random_sign_step v ha (by omega) (by omega)) eaa
        have hpb := random_post_of_exec (random_sign_step v hb (by omega) (by omega)) eba
        obtain ⟨_, hrunA⟩ := hpa.1
        obtain ⟨_, hrunB⟩ := hpb.1
        obtain ⟨_, _, hra⟩ := hrunA.ready
        obtain ⟨_, _, hrb⟩ := hrunB.ready
        have htest := (status_ct _ _ _ _ _ _ (hra.sp.trans (hpub.base.trans hrb.sp.symm)) eat ebt).1
        obtain ⟨⟨hza, hma, hka⟩, hmxa⟩ := random_post_of_exec (status_test hra.scr hra.sp hpa.2.1) eat
        obtain ⟨⟨hzb, hmb, hkb⟩, hmxb⟩ := random_post_of_exec (status_test hrb.scr hrb.sp hpb.2.1) ebt
        have hpa' := hpa.congr hma hka hmxa
        have hpb' := hpb.congr hmb hkb hmxb
        refine ⟨by rw [hattempt, htest], ?_, fun _ => trivial, ?_⟩
        · simp only [eval, hza, hzb, hstatus]
        · intro hc
          have hfour : randomSignAttemptStatus (randomInput s) used (n + 1) = 4 := by
            simp only [eval, hza, Option.some.injEq, beq_iff_eq] at hc
            have hv := congrArg BitVec.toNat hc
            have hh := random_sign_attempt_status_bound (randomInput s) used (n + 1)
            change randomSignAttemptStatus (randomInput s) used (n + 1) % 2 ^ 64 = 4 at hv
            omega
          have hfourB : randomSignAttemptStatus (randomInput t) used (n + 1) = 4 := hstatus.symm.trans hfour
          have hnext := random_sign_attempt_next_trace htrace hfour hfourB
          obtain ⟨hf', _⟩ := random_sign_attempt_continue (by omega) hfour
          have ha' := hpa'.2.2 hfour
          have hb' := hpb'.2.2 hfourB
          simp only [Nat.add_sub_cancel] at ha' hb'
          rw [← hused] at hb' hnext
          exact ⟨n, by omega, by omega, by omega, used + (randomSignDraw (randomInput s) used).used,
            ha', hb', hnext⟩

end VG.Proof.Dsa.X86_64

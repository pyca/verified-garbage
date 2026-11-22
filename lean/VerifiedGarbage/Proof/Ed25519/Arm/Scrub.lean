module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Impl.Ed25519.Arm.KeyPair
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
meta import VerifiedGarbage.Proof.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
meta import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ed25519.KeyPair
meta import VerifiedGarbage.Impl.Ed25519.Arm.KeyPair
meta import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign

/-! ### `Ed25519.Arm.SignCached.Expanded`, which only this module used -/

section

/-! # Complete Ed25519 signing with the seed's cached SHA-512 digest (Arm)

`codeExpanded` is `bodyFrom PublicKey.copyExpanded`: the digest at the second argument is
copied to `frame 184`, where the rest, proven by `bodyFrom_ok` and `bodyFrom_ct`, reads it. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed25519.Arm.PublicKey (copyArgs copyWords copyExpanded)
open VG.Proof.Ed25519 (sign_of_sha512_eq sha512_length)

variable {umaal : Bool}

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

/-- The digest at `seed`, read only and outside what signing writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) :
    Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨State.addr L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  have hi : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  refine ⟨by rw [hs]; exact hi, fun r hr => ?_, by have := hL.ns; rw [h64] at this; exact this,
    by have := hL.top; omega_using [this]⟩
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.os _ hi).symm
  · exact hL.sc _ hi
  · exact (hL.ks _ hi).symm

/-- The copy's arguments: the digest in `r1`, `frame 184` in `r2`. -/
theorem copy_args {t : State} (ho : OutArgs L copyArgs t) :
    t.gpr .r1 = L.seed ∧ t.gpr .r2 = L.E + BitVec.ofNat 32 184 := by
  have a1 := ho (.r1, .caller 1 0) (by simp [copyArgs])
  change t.gpr .r1 = L.seed + 0#32 at a1
  rw [BitVec.add_zero] at a1
  exact ⟨a1, ho (.r2, .frame 184) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded s fun t =>
      Ctx L g m₀ t ∧ DigestReady L (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 64) t := by
  refine WP.seq (WP.mono (args_ok hc hL ha (args := copyArgs) (stack := []) (by decide)
    (by simp [copyArgs, Whole.valid]) (by decide) (by simp) (by simp [copyArgs, preserved]))
    fun t ⟨ht, _, ho, _⟩ => ?_)
  have ⟨a1, a2⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨ht, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L copyArgs [])) (.block copyWords) fun _ _ => True :=
  ctRegs [.r1, .r2] (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact args_eq h (p := (.r1, .caller 1 0)) (by simp [copyArgs])
      · exact args_eq h (p := (.r2, .frame 184)) (by simp [copyArgs]))
    (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs [] (by decide) (by simp [copyArgs, Whole.valid]) (by decide)
    (by simp) (by simp [copyArgs, preserved])).seq (two_wp copyWords_ct ?_ ?_)
  · intro t hc ho
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩
  · intro t hc ho
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩

/-! ## The expanded-key entry point -/

/-- Signing with the seed's digest at `r1` and its public key at `r2`. -/
def signLocalE : Contract isa := signLocalWith 64
  (fun s => ∃ seed : List Byte, seed.length = 32 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 = Spec.Ed25519.publicKey seed)
  (fun s t => ∀ seed : List Byte, seed.length = 32 →
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed →
    Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign seed
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat))

theorem expanded_key {s : State} (h : signLocalE.pre s) :
    ∃ seed : List Byte, seed.length = 32 ∧
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 = Spec.Ed25519.publicKey seed := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ := h
  exact hk

theorem bodyE_noFrames : (bodyFrom umaal copyExpanded).noFrames = true := by
  simp only [bodyFrom, copyExpanded, nonceCode, challengeCode, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [reduce_noFrames, base_noFrames, mul_noFrames]
  rfl

/-- The digest and the public key at the body's entry, as on entry. -/
theorem entry_expanded {s p : State} (h : signLocalE.pre s) (hp : Whole.Saved (Whole.entered s) 6 p)
    {seed : List Byte} (hE : Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed)
    (hk : Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 = Spec.Ed25519.publicKey seed) :
    Spec.Ed25519.bytesAt p.mem (State.addr (lay 64 s).seed) 64 = Spec.Sha512.sha512 seed ∧
      Spec.Ed25519.bytesAt p.mem (State.addr (lay 64 s).pk) 32 = Spec.Ed25519.publicKey seed := by
  have hf := Whole.saved_frame (entry_below h) hp
  exact ⟨(entry_input h hf (r := ⟨State.addr (s.gpr .r1), 64⟩) (by rw [h.1]; simp)
      (by change 64 ≤ 2 ^ 64; decide)).trans hE,
    (entry_input h hf (r := ⟨State.addr (s.gpr .r2), 32⟩) (by rw [h.1]; simp)
      (by change 32 ≤ 2 ^ 64; decide)).trans hk⟩

theorem signE_ok {s : State} (h : signLocalE.pre s) :
    WP isa (codeExpanded umaal) s fun u => abiPreserved s u ∧ signLocalE.post s u := by
  obtain ⟨seed, -, hE, hk⟩ := expanded_key h
  have hw := Whole.wrap_ok (bodyE_noFrames (umaal := umaal)) (by decide : 6 ≤ 6) (entry_below h) (entry_top h)
    (entry_read h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign seed
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
    (fun p hp => by
      have ⟨hE', hk'⟩ := entry_expanded h hp hE hk
      have hc : Ctx (lay 64 s) s.gpr p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h
      have ha : Arguments (lay 64 s) p.mem := entry_args h hp
      exact WP.mono (bodyFrom_ok (copy_ok hc hL ha rfl) hL ha hE' hk' (entry_tbl h hp)
        (congrFun hp.step.syms _)) fun u ⟨hu, ho⟩ => ⟨by
          change Whole.Ctx (Whole.base s) s.gpr p.mem (lay 64 s).inputs (lay 64 s).outputs u at hu
          rw [(entry_regions h).1, (entry_regions h).2] at hu
          exact hu, ho⟩)
    (hP := fun _ m₁ m₂ _ hf hp => by
      have e : Spec.Ed25519.bytesAt m₂ (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.bytesAt m₁ (State.addr (s.gpr .r0)) 64 := by
        unfold Spec.Ed25519.bytesAt
        refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r0), 64⟩) ?_
          (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
        rintro r hr
        rw [List.mem_singleton.mp hr]
        exact (entry_writes h _ (by rw [h.2.1]; simp)).symm
      show Spec.Ed25519.bytesAt m₂ _ _ = _
      rw [e]; exact hp)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed' _ hs' => ?_⟩
  have hm := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega_using [])
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 64 = _
  rw [hp, hm]
  exact sign_of_sha512_eq (hE.symm.trans hs') _

theorem signE_ct : ConstantTime isa signLocalE.pre signLocalE.pub (codeExpanded umaal) := by
  refine Whole.wrap_ct (by decide) (fun _ _ hp => hp.1)
    (fun _ h => entry_below h) (fun _ h => entry_top h) (fun _ h => entry_read h) ?_ ?_
  · intro s hs p hp
    obtain ⟨seed, -, hE, hk⟩ := expanded_key hs
    have ⟨hE', hk'⟩ := entry_expanded hs hp hE hk
    have hL : (lay 64 s).Ok := lay_ok hs
    have ha : Arguments (lay 64 s) p.mem := entry_args hs hp
    exact WP.mono (bodyFrom_ok (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha hE' hk'
      (entry_tbl hs hp) (congrFun hp.step.syms _)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args ht hqb
    have hqw : Tbl (lay 64 s) q.mem := he ▸ entry_tbl ht hqb
    have hqy : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms VG.Impl.Ed25519.Arm.combSym =
        (lay 64 s).T := (congrFun hqb.step.syms _).trans hp.2.2.2.2.2.2.2.symm
    have hL : (lay 64 s).Ok := lay_ok hs
    have hpa' : Arguments (lay 64 s) p.mem := entry_args hs hpa
    exact ⟨(bodyFrom_ct (copy_ct hL rfl hpa' hqa) hL hpa' hqa (entry_tbl hs hpa) hqw _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, hq, trivial, trivial⟩, congrFun hpa.step.syms _, hqy⟩ ea eb).1, trivial⟩

/-! ## The shared contract -/

/-- The contract under the plain calling convention, without the tables. -/
def signExpandedAbi : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 8192⟩
    let args : Region := ⟨State.addr s.sp,8⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [seed, pk, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧ out.Disjoint scr ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ∃ seed : List Byte, seed.length = 32 ∧
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed ∧
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 = Spec.Ed25519.publicKey seed
  post _ _ := True
  pub _ _ := True

theorem signExpandedAbi_pre {s : State} (h : (Spec.Ed25519.signExpandedContract Arm.abi 280).pre s) :
    signExpandedAbi.pre s := by
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, signExpandedAbi, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
  sig_split h
  sig_reduce [signExpandedAbi, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sig_simp [] []
  simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  sig_close
  all_goals with_reducible assumption

abbrev signSpecE : Contract isa :=
  Spec.Ed25519.signExpandedContract (Arm.abi.withConsts VG.Impl.Ed25519.Arm.combConsts) 280

theorem signE_pre {s : State} (h : signSpecE.pre s) : signLocalE.pre s := by
  have hp : (Spec.Ed25519.signExpandedContract Arm.abi 280).pre (stripConsts VG.Impl.Ed25519.Arm.combConsts s) ∧
      ConstsOk VG.Impl.Ed25519.Arm.combConsts 280 s := pre_consts.mp h
  obtain ⟨rd, wr, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, ht, hk⟩ :=
    signExpandedAbi_pre hp.1
  have hk' := hp.2
  have mem : (VG.Impl.Ed25519.Arm.combSym, VG.Impl.Ed25519.Arm.combWords) ∈
      VG.Impl.Ed25519.Arm.combConsts := List.mem_singleton_self _
  have fit := hk'.fit mem
  rw [combWords_length] at fit
  have tr := hk'.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)
  refine ⟨?_, wr, os, op, om, oa, oc, sc, pc, mc, ac, ko, ks, kp, km, kc, no, ns, np, nm, nc, hb, ht, hk,
    fit, fun j hj => ?_, tr.2.1 _ (by rw [show s.wr = _ from wr]; exact List.mem_cons_self),
    tr.2.1 _ (by rw [show s.wr = _ from wr]; exact List.mem_cons_of_mem _ List.mem_cons_self),
    tr.2.2 _ (by simp [Arm.abi, stackBelow])⟩
  · have e1 := hk'.1
    rw [combConsts_regs] at e1
    have hl : VG.Impl.Ed25519.Arm.combConsts.length = 1 := rfl
    rw [hl] at e1
    change List.take (s.rd.length - VG.Impl.Ed25519.Arm.combConsts.length) s.rd = _ at rd
    rw [hl] at rd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd]
    rfl
  · have hw := hk'.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

/-! ## A witness -/

def satDigest : List Byte := Spec.Sha512.sha512 satSeed

theorem satSeed_length : satSeed.length = 32 := by
  simp only [satSeed, Spec.Ed25519.bytesAt, List.length_map, List.length_range]

/-- The seed's digest at `0x2000`, its public key at `0x3000`, the scratch pointer on the
stack, and the comb's tables from `0x100000`. -/
def satMemE : Mem := fun a =>
  if a.toNat < 0x2000 then 0
  else if a.toNat < 0x2040 then satDigest[a.toNat - 0x2000]?.getD 0
  else if a.toNat < 0x100000 then satMem a
  else baseSatMem a

theorem satE_digest : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigest := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigest, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega_using [], show 0x2000 + i < 0x2040 from by omega_using [hi'], ite_false,
      ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem satE_key : Spec.Ed25519.bytesAt satMemE 0x3000 32 = satKey := by
  rw [← sat_key]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
    change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
    omega_using [hi]
  simp only [satMemE, e, show ¬ 0x3000 + i < 0x2000 by omega_using [], show ¬ 0x3000 + i < 0x2040 by omega_using [],
    show 0x3000 + i < 0x100000 by omega_using [hi], ↓reduceIte]

theorem satMemE_frame : Frame [⟨0, 0x100000⟩] baseSatMem satMemE := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  rw [show (x - 0 : Addr) = x from by simp] at hn
  simp only [satMemE, show ¬ x.toNat < 0x2000 by omega_using [hn], show ¬ x.toNat < 0x2040 by omega_using [hn],
    show ¬ x.toNat < 0x100000 by omega_using [hn], ↓reduceIte]

def satStateE : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMemE
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]
  syms _ := 0x100000

theorem satE_held : ∀ i < 64 * 192,
    satStateE.mem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.Ed25519.Arm.combWords.getD i 0 := by
  intro i hi
  rw [← baseSatMem_held i (by rw [combWords_length]; exact hi)]
  refine satMemE_frame.readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  have e : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (0x100000 + 8 * i % 2 ^ 64) % 2 ^ 64 = _
    omega_using [hi]
  refine (Offset.disjoint_of_le (r₁ := ⟨0, 0x100000⟩) ?_ ?_).symm
  · change 0 + 0x100000 ≤ (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat
    omega_using [e]
  · change (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat + 8 ≤ 2 ^ 64
    omega_using [e]

theorem signE_sat : signSpecE.pre satStateE := by
  have held := satE_held
  generalize eqs : satStateE = s
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    Arm.stackArg, Arm.stackArgAddr, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  refine ⟨by decide, by decide, by decide, held, by decide, ?_, Region.disjoint_of_sep (by decide), by decide, ?_⟩
  · intro r hr
    change r ∈ [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · sig_and_intros
    rotate_right
    · exact ⟨satSeed, satSeed_length, satE_digest, satE_key⟩
    all_goals first | exact Region.disjoint_of_sep (by decide +kernel) | decide +kernel

theorem signE_implies : signLocalE.Implies signSpecE where
  pre _ h := signE_pre h
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, a0, a1⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, a0, a1, hsy⟩
  sat := ⟨satStateE, signE_sat⟩

theorem signExpanded_verified : Verified Arm.target (codeExpanded umaal) signSpecE :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signE_ok h) signE_ct (.refl signE_implies.sat_left))
    signE_implies

end VG.Proof.Ed25519.Arm.SignCached

end

end

/-! ### `Ed25519.Arm.KeyPair`, which only this module used -/

section

/-! ### `Ed25519.Arm.PublicKey.Expanded`, which only this module used -/

section

/-! ### `Ed25519.Arm.PublicKey.Verified`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Correct`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.Layout`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  scr : BitVec 32
  E : BitVec 32
  /-- The address of the comb's tables (`combSym`). -/
  T : BitVec 32
  /-- The bytes read at `seed`: the seed's cached SHA-512 digest (64). -/
  seedLen : Nat

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨State.addr L.out, 32⟩
abbrev SEED : Region := ⟨State.addr L.seed, L.seedLen⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
abbrev TB : Region := TBL L.T
def inputs : List Region := [L.SEED, L.TB, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 32
  ns : L.seed.toNat + L.seedLen ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
  tfit : L.T.toNat + 98304 ≤ 2 ^ 32
  tout : L.TB.Disjoint L.OUT
  tscr : L.TB.Disjoint L.SCR
  tstk : L.TB.Disjoint L.STK
end Lay

/-- The comb's tables at `L.T` in `m`. -/
def Tbl (L : Lay) (m : Mem) : Prop :=
  ∀ j < 64 * 192, m.readW (State.addr L.T + BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem Ctx.arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 248) (k := 24) (by omega_using []) (by omega_using [hj]) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem value_eq (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (v : Value) (hi : ∀ j d, v = .caller j d → j < 3) : Whole.value L.E t.mem v = argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, argValue]
    rw [hc.arg_word hL (hi j d rfl), ha j (hi j d rfl)]

theorem setup_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    WP isa (.block (setup args stk)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = argValue L (stk[j]'hj)) := by
  refine WP.mono (hc.setup hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun u ⟨hu, hm, hregs, hstk⟩ => ⟨hu, hm, ?_, ?_⟩
  · intro p hp
    rw [hregs p hp, value_eq hc hL ha _ (hi p hp)]
  · intro j hj
    rw [hstk j hj, value_eq hc hL ha _ (his _ (List.getElem_mem hj))]

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Base`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {umaal : Bool}

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem base_noFrames : (Impl.Ed25519.Arm.scalarBase umaal).noFrames = true := by cases umaal <;> lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + 24 ∧ t.gpr .r2 = L.scr

theorem scalar_addr (hL : L.Ok) : State.addr (L.E + 24) = State.addr L.E + 24 :=
  addr_add (k := 24) (by have := hL.top; omega_using [this])

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T)
    (hw : Tbl L t.mem) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩, L.TB] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have sy : (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩, L.TB] L.outputs).syms
      VG.Impl.Ed25519.Arm.combSym = L.T := hsy
  simp only [scalarBaseLocal, sy, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, scalar_addr hL]
  refine ⟨True.intro, rfl, (hL.ko.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280))).symm,
    hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280)), hL.no, ?_, hL.nc, hL.tfit, hw,
    hL.tout, hL.tscr⟩
  have h := hL.top
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega_using [h])]
  change L.E.toNat + 24 + 32 ≤ 2 ^ 32
  omega_using [h]

theorem base_covers (L : Lay) : Covers ([⟨State.addr L.E + 24, 32⟩, L.TB] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 32 ≤ 248; decide⟩
    · exact ⟨L.TB, by simp [Lay.inputs], 0, by simp⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

/-- The tables in a memory the body leaves them in. -/
theorem Ctx.tbl (hc : Ctx L g m₀ t) (hL : L.Ok) (hw : Tbl L m₀) : Tbl L t.mem := fun j hj => by
  rw [← hw j hj]
  refine hc.frame.readW (r := L.TB) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.tout
  · exact hL.tscr
  · exact hL.tstk.sub_right (frame_sub L)

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : BaseArgs L t)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) (hw : Tbl L t.mem) :
    WP isa (.call ("vg_ed25519_scalar_base" ++ Impl.Ed25519.Arm.suffix umaal)
      (Impl.Ed25519.Arm.scalarBase umaal)) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha hsy hw) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (State.addr (t.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, scalar_addr hL] at hp
  exact hp

theorem prune_step (hc : Ctx L g m₀ t) (hL : L.Ok) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨State.addr L.E, 248⟩ : Region) ∈ t.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (prune_ok hc.sp (by have := hL.top; omega_using [this]) hwrite hh) fun u ⟨hu, hf, hp⟩ => ⟨?_, hp⟩
  refine hc.of_frame hu.rd hu.wr hu.sp ?_ hf ?_
  · intro r hr _
    apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · rintro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem base_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (hw : Tbl L m₀)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) = n) :
    WP isa (callWith baseArgs ("vg_ed25519_scalar_base" ++ Impl.Ed25519.Arm.suffix umaal)
      (Impl.Ed25519.Arm.scalarBase umaal)) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms (setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ syu => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp)
  have h1 := hav (.r1, .frame 24) (by simp)
  have h2 := hav (.r2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 =
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨State.addr L.E + 24, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩ (by rw [syu]; exact hsy) (hu.tbl hL hw))
    fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, he, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 = Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega_using [this]) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm

/-- The public key from `n` bytes read at the seed pointer (its cached digest), with the
postcondition `post`. -/
def pkLocalWith (n : Nat) (post : State → State → Prop) : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), n⟩
    let scr : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    let tb : Region := TBL (s.syms VG.Impl.Ed25519.Arm.combSym)
    s.rd = [seed, tb] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + n ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧
      (s.syms VG.Impl.Ed25519.Arm.combSym).toNat + 98304 ≤ 2 ^ 32 ∧
      (∀ j < 64 * 192, s.mem.readW (State.addr (s.syms VG.Impl.Ed25519.Arm.combSym) +
        BitVec.ofNat 64 (8 * j)) 64 = VG.Impl.Ed25519.Arm.combWord j) ∧
      tb.Disjoint out ∧ tb.Disjoint scr ∧ tb.Disjoint stk
  post := post
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.syms VG.Impl.Ed25519.Arm.combSym = t.syms VG.Impl.Ed25519.Arm.combSym

def lay (n : Nat) (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, Whole.base s, s.syms VG.Impl.Ed25519.Arm.combSym, n⟩

variable {n : Nat} {post : State → State → Prop}

theorem lay_ok {s : State} (h : (pkLocalWith n post).pre s) : (lay n s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, hb, tf, _, tout, tscr, tstk⟩ := h
  have he := Whole.base_addr hb
  have top := Whole.base_top hb
  have hs := s.sp.isLt
  refine ⟨by change (Whole.base s).toNat + 272 ≤ 2 ^ 32; omega_using [top], os, oc, sc, ?_, ?_, ?_, no, ns, nc,
    tf, tout, tscr, ?_⟩
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ko
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact ks
  · change (⟨State.addr (Whole.base s), 280⟩ : Region).Disjoint _
    rw [he]; exact kc
  · change Region.Disjoint _ (⟨State.addr (Whole.base s), 280⟩ : Region)
    rw [he]; exact tstk

theorem entry_below {s : State} (h : (pkLocalWith n post).pre s) : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.1

/-- The tables at the body's entry. -/
theorem entry_tbl {s p : State} (h : (pkLocalWith n post).pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Tbl (lay n s) p.mem := fun j hj => by
  have hf := Whole.saved_frame (entry_below h) hp
  have hw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  rw [← hw]
  refine hf.readW (r := TBL (s.syms VG.Impl.Ed25519.Arm.combSym))
    (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  change Region.Disjoint _ (⟨State.addr (Whole.base s), 280⟩ : Region)
  rw [Whole.base_addr (entry_below h)]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : (pkLocalWith n post).pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (lay_ok h).ko
  · exact (lay_ok h).kc

theorem entry_ctx {s p : State} (h : (pkLocalWith n post).pre s) (hp : Whole.Saved (Whole.entered s) 3 p) :
    Ctx (lay n s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, Lay.TB, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hs : 280 ≤ s.sp.toNat) (hp : Whole.Saved (Whole.entered s) 3 p) : Arguments (lay n s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hs (by decide : 3 ≤ 6)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt) hp hj
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases he with rfl | rfl | rfl <;> exact hw

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {umaal : Bool}

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The public key after a first step `first` that leaves a digest `D` at `frame 184`: the
public key of every seed whose digest `D` is. -/
theorem bodyFrom_ok {first : Prog isa} {D : List Byte}
    (hfirst : WP isa first t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 = D)
    (hL : L.Ok) (ha : Arguments L m₀) (hw : Tbl L m₀)
    (hsy : t.syms VG.Impl.Ed25519.Arm.combSym = L.T) :
    WP isa (bodyFrom umaal first) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul (Spec.Ed25519.prune D) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono_syms hfirst fun u ⟨hu, hh⟩ syu => ?_)
  refine WP.seq (WP.mono_syms (prune_step hu hL hh) fun u' ⟨hu', hs⟩ syu' => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hw (by rw [syu', syu]; exact hsy) hs)
    fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

/-! Merged from `Proof.Ed25519.Arm.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev Two (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ m₁ a ∧ P a) ∧ (Ctx L g₂ m₂ b ∧ P b)

def Slots (L : Lay) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = argValue L p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = argValue L (stk[j]'hj)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stk))
      (Two L g₁ g₂ m₁ m₂ (Slots L args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hi hr hs hvs his) fun _ ⟨hc, _, hg, ht⟩ => ⟨hc, hg, ht⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]

variable {L : Lay} {t : State}

/-- What the call of `vg_ed25519_scalar_base` needs besides its arguments: the tables' address
and words. -/
def BaseReady (L : Lay) (t : State) : Prop :=
  Slots L baseValues [] t ∧ t.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ Tbl L t.mem

def base_ready (hL : L.Ok) (hs : BaseReady L t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1.1 (.r0, .caller 0 0) (by simp [baseValues])
  have h1 := hs.1.1 (.r1, .frame 24) (by simp [baseValues])
  have h2 := hs.1.1 (.r2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨State.addr L.E + 24, 32⟩, L.TB], L.outputs, base_pre hL ⟨h0, h1, h2⟩ hs.2.1 hs.2.2,
    base_covers L, base_writes L⟩

end VG.Proof.Ed25519.Arm.PublicKey
end

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {umaal : Bool}

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem base_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ (BaseReady L))
    (.call ("vg_ed25519_scalar_base" ++ Impl.Ed25519.Arm.suffix umaal) (Impl.Ed25519.Arm.scalarBase umaal))
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine Whole.callEx scalarBase_ok scalarBase_ct fun a b h => ?_
    let ra := base_ready hL h.1.2
    let rb := base_ready hL h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    have hg : ∀ p ∈ baseValues, a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := fun p hp => by
      have hl : p.1 ∉ linkRegs := by simp only [baseValues, List.mem_cons, List.not_mem_nil, or_false] at hp
                                     rcases hp with rfl | rfl | rfl <;> decide
      rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl, h.1.2.1.1 p hp, h.2.2.1.1 p hp]
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      ⟨h.1.1.sp.trans h.2.1.sp.symm, hg (.r0, .caller 0 0) (by simp [baseValues]),
        hg (.r1, .frame 24) (by simp [baseValues]), hg (.r2, .caller 2 0) (by simp [baseValues]),
        h.1.2.2.1.trans h.2.2.2.1.symm⟩, ca, wa, cb, wb⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((base_ready hL hs).wp hc scalarBase_ok base_noFrames) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((base_ready hL hs).wp hc scalarBase_ok base_noFrames) fun _ hu => ⟨hu, trivial⟩

theorem prune_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL (digest := Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 6 56).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- The public key after a first step related to itself, as the copy of a cached digest is. -/
theorem bodyFrom_ct {first : Prog isa}
    (hfirst : RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) first (Two L g₁ g₂ m₁ m₂ fun _ => True))
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (hw₁ : Tbl L m₁) (hw₂ : Tbl L m₂) :
    RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (fun _ => True) a b ∧
      a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T)
      (bodyFrom umaal first) (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb baseValues []
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by decide) (by simp [Whole.valid])
    (by simp)
  have bc : RelCT isa (fun a b => Two L g₁ g₂ m₁ m₂ (Slots L baseValues []) a b ∧
      a.syms VG.Impl.Ed25519.Arm.combSym = L.T ∧ b.syms VG.Impl.Ed25519.Arm.combSym = L.T)
      (.call ("vg_ed25519_scalar_base" ++ Impl.Ed25519.Arm.suffix umaal) (Impl.Ed25519.Arm.scalarBase umaal))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
    (base_ct hL).mono (fun a b ⟨⟨⟨hca, hsa⟩, ⟨hcb, hsb⟩⟩, sa, sb⟩ =>
      ⟨⟨hca, hsa, sa, hca.tbl hL hw₁⟩, ⟨hcb, hsb, sb, hcb.tbl hL hw₂⟩⟩) fun _ _ h => h
  exact (Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T hfirst).seq
    ((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T (prune_ct hL)).seq (((Whole.keepSym VG.Impl.Ed25519.Arm.combSym L.T b).seq bc).seq (wipe_ct hL)))

theorem lay_eq {n : Nat} {post : State → State → Prop} {s t : State}
    (hp : (pkLocalWith n post).pub s t) : lay n s = lay n t := by
  obtain ⟨sp, h0, h1, h2, hy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, hy]

end VG.Proof.Ed25519.Arm.PublicKey
end

end

end

/-! # Ed25519 public-key derivation from the seed's cached SHA-512 digest (Arm)

`codeExpanded` is `bodyFrom copyExpanded`: the digest at the second argument is copied to
`frame 184`, where the rest, proven by `bodyFrom_ok` and `bodyFrom_ct`, reads it. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519 (sha512_length)

variable {umaal : Bool}

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The digest at `seed`, read only and outside what the derivation writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) :
    Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨State.addr L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  refine ⟨by rw [hs]; simp [Lay.inputs], fun r hr => ?_, by have := hL.ns; rw [h64] at this; exact this,
    by have := hL.top; omega_using [this]⟩
  rw [hs]
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm

/-- The copy's arguments: the digest in `r1`, `frame 184` in `r2`. -/
theorem copy_args {u : State} (ho : ∀ p ∈ copyArgs, u.gpr p.1 = argValue L p.2) :
    u.gpr .r1 = L.seed ∧ u.gpr .r2 = L.E + BitVec.ofNat 32 184 := by
  have a1 := ho (.r1, .caller 1 0) (by simp [copyArgs])
  simp only [argValue, Lay.value, BitVec.add_zero] at a1
  exact ⟨a1, ho (.r2, .frame 184) (by simp [copyArgs])⟩

theorem copy_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) (h64 : L.seedLen = 64) :
    WP isa copyExpanded t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 64 := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := copyArgs) (stk := []) (by decide)
    (by simp [copyArgs, Whole.valid]) (by simp [copyArgs]) (by simp [copyArgs, preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, ho, _⟩ => ?_)
  have ⟨a1, a2⟩ := copy_args ho
  exact Whole.copy_digest (copy_src hL h64) ⟨hu, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩

variable {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWords_ct :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (Slots L copyArgs [])) (.block copyWords) fun _ _ => True :=
  ctRegs [.r1, .r2] (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.1.2.1 (.r1, .caller 1 0) (by simp [copyArgs])).trans
          (h.2.2.1 (.r1, .caller 1 0) (by simp [copyArgs])).symm
      · exact (h.1.2.1 (.r2, .frame 184) (by simp [copyArgs])).trans
          (h.2.2.1 (.r2, .frame 184) (by simp [copyArgs])).symm)
    (by taint_decide)

theorem copy_ct (hL : L.Ok) (h64 : L.seedLen = 64) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) copyExpanded
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine (setup_ct hL ha hb copyArgs [] (by decide) (by simp [copyArgs, Whole.valid])
    (by simp [copyArgs]) (by simp [copyArgs, preserved]) (by decide) (by simp) (by simp)).seq
    (Whole.rel_wp copyWords_ct ?_ ?_)
  · intro u ⟨hc, ho⟩
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩
  · intro u ⟨hc, ho⟩
    have ⟨a1, a2⟩ := copy_args ho.1
    exact WP.mono (Whole.copy_digest (copy_src hL h64)
      ⟨hc, a1, a2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ h => ⟨h.1, trivial⟩

/-! ## The expanded-key entry point -/

/-- The public key from the seed's digest at `r1`. -/
def pkLocalE : Contract isa := pkLocalWith 64 fun s t => ∀ seed : List Byte, seed.length = 32 →
  Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 = Spec.Sha512.sha512 seed →
  Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.publicKey seed

theorem bodyE_noFrames : (bodyFrom umaal copyExpanded).noFrames = true := by
  simp only [bodyFrom, copyExpanded, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames, Bool.and_self]
  rw [base_noFrames]
  rfl

theorem pkE_ok {s : State} (h : pkLocalE.pre s) :
    WP isa (codeExpanded umaal) s fun u => abiPreserved s u ∧ pkLocalE.post s u := by
  have hw := Whole.wrap_ok (bodyE_noFrames (umaal := umaal)) (by decide : 3 ≤ 6) (entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.encodePoint
      (Spec.Ed25519.pointMul (Spec.Ed25519.prune (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 64))
        Spec.Ed25519.basePoint))
    (fun p hp => by
      have hc : Ctx (lay 64 s) s.gpr p.mem _ := entry_ctx h hp
      have hL : (lay 64 s).Ok := lay_ok h
      have ha : Arguments (lay 64 s) p.mem := entry_args (entry_below h) hp
      exact WP.mono (bodyFrom_ok (copy_ok hc hL ha rfl) hL ha (entry_tbl h hp)
        (congrFun hp.step.syms _)) fun u huo => ⟨by
          simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
            Lay.SCR, Lay.ARGS, Lay.TB, lay, h.2.1, List.cons_append, List.nil_append] using huo.1,
          huo.2⟩)
    (hP := fun _ m₁ m₂ _ hf hp => by
      have e : Spec.Ed25519.bytesAt m₂ (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.bytesAt m₁ (State.addr (s.gpr .r0)) 32 := by
        unfold Spec.Ed25519.bytesAt
        refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r0), 32⟩) ?_
          (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
        rintro r hr
        rw [List.mem_singleton.mp hr]
        exact (entry_writes h _ (by rw [h.2.1]; simp)).symm
      show Spec.Ed25519.bytesAt m₂ _ _ = _
      rw [e]; exact hp)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed _ hs => ?_⟩
  have hd : Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 64 =
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 64⟩) ?_
      (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 32 = _
  rw [hp, hd, hs]
  rfl

theorem pkE_ct : ConstantTime isa pkLocalE.pre pkLocalE.pub (codeExpanded umaal) := by
  refine Whole.wrap_ct (by decide : 3 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) ?_ (by intro s hs j hj h4; omega) ?_ ?_
  · intro s _
    simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt s.sp.isLt
  · intro s hs p hp
    have hL : (lay 64 s).Ok := lay_ok hs
    have ha : Arguments (lay 64 s) p.mem := entry_args (entry_below hs) hp
    exact WP.mono (bodyFrom_ok (copy_ok (entry_ctx hs hp) hL ha rfl) hL ha (entry_tbl hs hp)
      (congrFun hp.step.syms _)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq (n := 64) hp
    have hq : Ctx (lay 64 s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay 64 s) q.mem := he ▸ entry_args (entry_below ht) hqb
    have hqw : Tbl (lay 64 s) q.mem := he ▸ entry_tbl ht hqb
    have hqy : (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)).syms VG.Impl.Ed25519.Arm.combSym =
        (lay 64 s).T := (congrFun hqb.step.syms _).trans hp.2.2.2.2.symm
    have hL : (lay 64 s).Ok := lay_ok hs
    have hpa' : Arguments (lay 64 s) p.mem := entry_args (entry_below hs) hpa
    exact ⟨(bodyFrom_ct (copy_ct hL rfl hpa' hqa) hL hpa' hqa (entry_tbl hs hpa) hqw _ _ _ _ _ _
      ⟨⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩, congrFun hpa.step.syms _, hqy⟩ ea eb).1, trivial⟩

/-! ## A witness, and the shared contract -/

abbrev pkSpecE : Contract isa :=
  Proof.Ed25519.publicKeyExpandedContract (Arm.abi.withConsts VG.Impl.Ed25519.Arm.combConsts) 280

theorem pkE_pre {s : State} (h : pkSpecE.pre s) : pkLocalE.pre s := by
  have hp : (Proof.Ed25519.publicKeyExpandedContract Arm.abi 280).pre
      (stripConsts VG.Impl.Ed25519.Arm.combConsts s) ∧
      ConstsOk VG.Impl.Ed25519.Arm.combConsts 280 s := pre_consts.mp h
  have h1 := hp.1
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    stackBelow] at h1
  obtain ⟨hb, _, rd, wr, os, oc, sc, ko, ks, kc, no, ns, nc, -⟩ := h1
  have hk := hp.2
  have mem : (VG.Impl.Ed25519.Arm.combSym, VG.Impl.Ed25519.Arm.combWords) ∈
      VG.Impl.Ed25519.Arm.combConsts := List.mem_singleton_self _
  have fit := hk.fit mem
  rw [combWords_length] at fit
  have ht := hk.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)
  refine ⟨?_, wr, os, oc, sc, ko, ks, kc, no, ns, nc, hb, fit, fun j hj => ?_,
    ht.2.1 _ (by rw [wr]; exact List.mem_cons_self),
    ht.2.1 _ (by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self),
    ht.2.2 _ (by simp [Arm.abi, stackBelow])⟩
  · have e1 := hk.1
    rw [combConsts_regs] at e1
    have hl : VG.Impl.Ed25519.Arm.combConsts.length = 1 := rfl
    rw [hl] at e1
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd, List.singleton_append]
    rfl
  · have hw := hk.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

/-- A seed of zeros, and its digest at `0x2000`. -/
def satSeedE : List Byte := List.replicate 32 0
def satDigestE : List Byte := Spec.Sha512.sha512 satSeedE

def satMemE (a : Addr) : Byte :=
  if a.toNat < 0x2000 then 0 else satDigestE[a.toNat - 0x2000]?.getD 0

theorem sat_digestE : Spec.Ed25519.bytesAt satMemE 0x2000 64 = satDigestE := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satDigestE, sha512_length]
  · intro i hi hj
    have hi' : i < 64 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
      change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
      omega_using [hi']
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega_using [], ite_false,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The witness's memory: `satMemE` below the tables, the tables from `0x100000`. -/
def satMemTE : Mem := fun a => if a.toNat < 0x100000 then satMemE a else baseSatMem a

theorem satMemTE_frame : Frame [⟨0, 0x100000⟩] baseSatMem satMemTE := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  rw [show (x - 0 : Addr) = x from by simp] at hn
  simp only [satMemTE, show ¬ x.toNat < 0x100000 by omega_using [hn], ↓reduceIte]

theorem satMemTE_held : ∀ i < 64 * 192,
    satMemTE.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.Ed25519.Arm.combWords.getD i 0 := by
  intro i hi
  rw [← baseSatMem_held i (by rw [combWords_length]; exact hi)]
  refine satMemTE_frame.readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  have e : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (0x100000 + 8 * i % 2 ^ 64) % 2 ^ 64 = _
    omega_using [hi]
  refine (Offset.disjoint_of_le (r₁ := ⟨0, 0x100000⟩) ?_ ?_).symm
  · change 0 + 0x100000 ≤ (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat
    omega_using [e]
  · change (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat + 8 ≤ 2 ^ 64
    omega_using [e]

theorem satMemTE_digest : Spec.Ed25519.bytesAt satMemTE 0x2000 64 = satDigestE := by
  rw [← sat_digestE]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega_using [hi]
  simp only [satMemTE, e, show 0x2000 + i < 0x100000 by omega_using [hi], ↓reduceIte]

def satStateE : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMemTE
  rd := [⟨0x2000, 64⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem pkE_sat : pkSpecE.pre satStateE := by
  have held := satMemTE_held
  generalize eqs : satStateE = s
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  refine ⟨by decide, by decide, by decide, held, by decide, ?_, Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    ⟨satSeedE, by simp [satSeedE], satMemTE_digest⟩⟩
  intro r hr
  change r ∈ [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem pkE_implies : pkLocalE.Implies pkSpecE where
  pre _ h := pkE_pre h
  post := by
    intro s s' _ h
    sig_post [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨satStateE, pkE_sat⟩

theorem publicKeyExpanded_verified : Verified Arm.target (codeExpanded umaal) pkSpecE :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => pkE_ok h) pkE_ct (.refl pkE_implies.sat_left))
    pkE_implies

end VG.Proof.Ed25519.Arm.PublicKey

end

end

/-!
# Ed25519 key-pair derivation on ARMv7

`keyPair` calls the one-shot SHA-512 digest (`vg_sha512_digest`), which
writes the seed's digest to `expanded`, and then
`vg_ed25519_public_key_expanded`, which derives the public key from it. Its
proof uses only the two callees' contracts.

Addresses on the stack are offsets of `K s`, the lowest byte of the stack the
contract gives it (`sp - 600` on entry): `lr` is saved at `K s + 596`, `out`,
`expanded` and `scratch` at `K s + 584`, `+ 588` and `+ 592`, and both calls
enter with `sp` at `K s + 584`, the digest using the 584 bytes below it.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.KeyPair

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Ed25519.Arm VG.Impl.Ed25519.Arm.KeyPair

variable {umaal : Bool}

/-- The contract. -/
abbrev spec : Contract isa :=
  Spec.Ed25519.keyPairContract (Arm.abi.withConsts combConsts) 600

/-- The lowest byte of the stack used. -/
abbrev K (s : State) : Addr := State.addr s.sp - BitVec.ofNat 64 600

abbrev OUT (s : State) : Region := ⟨State.addr (s.gpr .r0), 32⟩
abbrev EXP (s : State) : Region := ⟨State.addr (s.gpr .r1), 64⟩
abbrev SEED (s : State) : Region := ⟨State.addr (s.gpr .r2), 32⟩
abbrev SCR (s : State) : Region := ⟨State.addr (s.gpr .r3), 8192⟩
abbrev STK (s : State) : Region := ⟨K s, 600⟩
abbrev TB (s : State) : Region := ⟨State.addr (s.syms combSym), 8 * combWords.length⟩

/-- The precondition, spelled out. -/
structure Pre (s : State) : Prop where
  sp : 600 ≤ s.sp.toNat
  rd : s.rd = [SEED s, TB s]
  wr : s.wr = [OUT s, EXP s, SCR s]
  held : ∀ i < combWords.length,
    s.mem.readW (State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0
  fit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 32
  al : (s.syms combSym).toNat % 64 = 0
  tO : (TB s).Disjoint (OUT s)
  tE : (TB s).Disjoint (EXP s)
  tC : (TB s).Disjoint (SCR s)
  tK : (TB s).Disjoint (STK s)
  oe : (OUT s).Disjoint (EXP s)
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  es : (EXP s).Disjoint (SEED s)
  ec : (EXP s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ko : (STK s).Disjoint (OUT s)
  ke : (STK s).Disjoint (EXP s)
  ks : (STK s).Disjoint (SEED s)
  kc : (STK s).Disjoint (SCR s)
  no : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  ne : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  ns : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  nc : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem pre_of {s : State} (h : spec.pre s) : Pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨hsp, -, hd, hheld, hfit, hdw, hdk, hal, ht, hw, oe, os, oc, es, ec, sc,
    ko, ke, ks, kc, no, ne, ns, nc⟩ := h
  refine ⟨hsp, ?_, hw, hheld, hfit, hal, hdw _ (by rw [hw]; simp [State.addr]),
    hdw _ (by rw [hw]; simp [State.addr]), hdw _ (by rw [hw]; simp [State.addr]), hdk, oe, os, oc, es, ec, sc, ko, ke, ks, kc, no, ne, ns, nc⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl

/-- The precondition, from its facts. -/
theorem spec_of {s : State} (h : Pre s) : spec.pre s := by
  sig_pre [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨h.sp, by have := s.sp.isLt; omega_using [], by rw [h.rd]; rfl, h.held, h.fit, fun r hr => ?_, h.tK, h.al,
    by rw [h.rd]; rfl, h.wr, h.oe, h.os, h.oc, h.es, h.ec, h.sc, h.ko, h.ke, h.ks, h.kc, h.no, h.ne, h.ns,
    h.nc⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.tO
  · exact h.tE
  · exact h.tC

/-! ## Addresses on the stack -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sub_sub' (x : BitVec 32) (a b : Nat) :
    x - BitVec.ofNat 32 a - BitVec.ofNat 32 b = x - BitVec.ofNat 32 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]

/-- `sp - k`, as an offset of `K s`. -/
theorem addrK {s : State} (h : Pre s) {k : Nat} (hk : k ≤ 600) :
    State.addr (s.sp - BitVec.ofNat 32 k) = K s + BitVec.ofNat 64 (600 - k) := by
  rw [addr_sub' (by have := h.sp; omega_using [hk, this])]
  exact Offset.sub_ofNat_eq _ hk

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 600) : Region.Sub ⟨K s + BitVec.ofNat 64 d, n⟩ (STK s) :=
  Offset.sub_base _ h

namespace Pre

variable {s : State}

theorem kO (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (OUT s) :=
  h.ko.sub_left (stk_sub s hd)
theorem kE (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (EXP s) :=
  h.ke.sub_left (stk_sub s hd)
theorem kS (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SEED s) :=
  h.ks.sub_left (stk_sub s hd)
theorem kC (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩ (SCR s) :=
  h.kc.sub_left (stk_sub s hd)
theorem kT (h : Pre s) {d n : Nat} (hd : d + n ≤ 600) : Region.Disjoint (TB s) ⟨K s + BitVec.ofNat 64 d, n⟩ :=
  h.tK.sub_right (stk_sub s hd)

end Pre

/-! ## Between the pushes and the pops -/

/-- The saved arguments. -/
abbrev AR (s : State) : Region := ⟨K s + BitVec.ofNat 64 584, 12⟩
/-- Where `lr` is saved. -/
abbrev LR (s : State) : Region := ⟨K s + BitVec.ofNat 64 596, 4⟩

/-- What holds between the pushes and the pops, for the entry state `s`. -/
structure Ctx (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = AR s :: LR s :: s.wr
  sp : t.sp = s.sp - BitVec.ofNat 32 16
  cs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r
  lr : t.mem.readW (K s + BitVec.ofNat 64 596) 32 = s.gpr .lr
  fOut : t.mem.readW (K s + BitVec.ofNat 64 584) 32 = s.gpr .r0
  fExp : t.mem.readW (K s + BitVec.ofNat 64 588) 32 = s.gpr .r1
  fScr : t.mem.readW (K s + BitVec.ofNat 64 592) 32 = s.gpr .r3
  sym : t.syms = s.syms
  frame : Frame [OUT s, EXP s, SCR s, STK s] s.mem t.mem

theorem Ctx.sp_toNat {s t : State} (h : Pre s) (hc : Ctx s t) : t.sp.toNat = s.sp.toNat - 16 := by
  rw [hc.sp, sub_toNat' (by have := h.sp; omega_using [this])]

/-- `sp + d`, from between the pushes and the pops. -/
theorem Ctx.addr_sp {s t : State} (h : Pre s) (hc : Ctx s t) {d : Nat} (hd : d ≤ 16) :
    State.addr (t.sp + BitVec.ofNat 32 d) = K s + BitVec.ofNat 64 (584 + d) := by
  have := s.sp.isLt
  rw [addr_add (by rw [hc.sp_toNat h]; omega_using [hd]), hc.sp, addrK h (by decide), add_add]

/-- The `n` bytes below `sp`, from between the pushes and the pops. -/
theorem Ctx.below {s t : State} (h : Pre s) (hc : Ctx s t) {n : Nat} (hn : n ≤ 584) :
    belowA t.sp n = ⟨K s + BitVec.ofNat 64 (584 - n), n⟩ := by
  simp only [belowA]
  rw [hc.sp, sub_sub', addrK h (by omega_using [hn]), show 600 - (16 + n) = 584 - n by omega_using []]

/-- A write of a register the ABI does not preserve. -/
theorem Ctx.setReg {s t : State} (hc : Ctx s t) {r : Reg} (hr : r ∉ preserved) (x : BitVec 32) :
    Ctx s (t.setReg r x) :=
  ⟨hc.rd, hc.wr, hc.sp, fun q hq hq' => by
      have hne : ¬q = r := fun e => hr (e ▸ hq)
      rw [RegUpd.gpr_setReg_of_ne (h := hne)]; exact hc.cs q hq hq',
    hc.lr, hc.fOut, hc.fExp, hc.fScr, hc.sym, hc.frame⟩

/-- The state the body starts in. -/
abbrev entered (s : State) : State := pushed [.r0, .r1, .r3] (pushed [.lr] s)

theorem entered_ctx {s : State} (h : Pre s) : Ctx s (entered s) := by
  have hsp := h.sp
  have hlt := s.sp.isLt
  have h4 : 4 * [Reg.lr].length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; omega_using [hsp]
  have e4 : (pushed [.lr] s).sp = s.sp - BitVec.ofNat 32 4 := rfl
  have h12 : 4 * [Reg.r0, .r1, .r3].length ≤ (pushed [.lr] s).sp.toNat := by
    rw [e4, sub_toNat' (by omega_using [hsp])]; simp only [List.length_cons, List.length_nil]; omega_using [hsp]
  have e16 : (entered s).sp = s.sp - BitVec.ofNat 32 16 := by
    show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12 = _
    rw [sub_sub']
  have em : (entered s).mem =
      storeWords (pushed [.lr] s).mem (s.sp - BitVec.ofNat 32 16) [s.gpr .r0, s.gpr .r1, s.gpr .r3] := by
    show storeWords _ (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12) _ = _
    rw [sub_sub']; rfl
  have em₁ : (pushed [.lr] s).mem = storeWords s.mem (s.sp - BitVec.ofNat 32 4) [s.gpr .lr] := rfl
  have t16 : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := sub_toNat' (by omega_using [hsp])
  -- The saved arguments.
  have slot : ∀ i (hi : i < 3), (entered s).mem.readW (K s + BitVec.ofNat 64 (584 + 4 * i)) 32 =
      [s.gpr .r0, s.gpr .r1, s.gpr .r3][i] := fun i hi => by
    have e := Argon2.Arm.storeWords_readW (pushed [.lr] s).mem (s.sp - BitVec.ofNat 32 16)
      [s.gpr .r0, s.gpr .r1, s.gpr .r3] (by simp only [List.length_cons, List.length_nil]; omega_using [t16]) hi
    rw [addr_add (by rw [t16]; omega_using [hi]), addrK h (by decide), add_add] at e
    rw [em]; exact e
  -- The saved `lr`, which the second push leaves alone.
  have hf₂ : Frame [⟨K s + BitVec.ofNat 64 584, 12⟩] (pushed [.lr] s).mem (entered s).mem := by
    have := Argon2.Arm.pushed_stk (rs := [.r0, .r1, .r3]) (s := pushed [.lr] s) h12
    simp only [Argon2.Arm.stkR, e4, List.length_cons, List.length_nil] at this
    rwa [← addr_sub' (by rw [sub_toNat' (by omega_using [hsp])]; omega_using [hsp]), sub_sub', addrK h (by decide)] at this
  have hf₁ : Frame [⟨State.addr s.sp - BitVec.ofNat 64 4, 4⟩] s.mem (pushed [.lr] s).mem :=
    Argon2.Arm.pushed_stk (rs := [.lr]) (s := s) h4
  have hk : STK s ∈ [OUT s, EXP s, SCR s, STK s] := by simp
  refine ⟨rfl, ?_, e16, fun _ _ _ => rfl, ?_, slot 0 (by decide), slot 1 (by decide), slot 2 (by decide), rfl,
    (hf₁.sub fun r hr => ?_).trans (hf₂.sub fun r hr => ?_)⟩
  · show (⟨State.addr (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 12), 12⟩ : Region) ::
      ⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩ :: s.wr = _
    rw [sub_sub', addrK h (by decide), addrK h (by decide)]
  · rw [hf₂.readW (r := ⟨K s + BitVec.ofNat 64 596, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)) (by decide), em₁]
    have e := Argon2.Arm.storeWords_readW s.mem (s.sp - BitVec.ofNat 32 4) [s.gpr .lr]
      (by rw [sub_toNat' (by omega_using [hsp])]; simp only [List.length_cons, List.length_nil]; omega_using []) (i := 0) (by simp)
    rw [Nat.mul_zero, BitVec.add_zero, addrK h (by decide)] at e
    exact e
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, hk, Offset.sub_below _ (by decide) (by decide)⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, hk, stk_sub s (by decide)⟩

/-! ## The digest's arguments -/

theorem exec_ldrSp {u : State} {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (u.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (u.rd ++ u.wr) a 4) :
    exec (.ldrSp t off) u = some (u.setReg t (u.mem.readW a 32)) := by
  subst ha; simp [exec, ho, State.load32, hin]

theorem Ctx.inAR {s t : State} (hc : Ctx s t) {d : Nat} (hd : d + 4 ≤ 12) :
    InRegions (t.rd ++ t.wr) (K s + BitVec.ofNat 64 (584 + d)) 4 := by
  rw [hc.wr]
  exact ⟨AR s, by simp, Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])⟩

/-- The digest's arguments: `data = seed`, `len = 32`, `out = expanded`. -/
theorem digestArgs_ok {s : State} (h : Pre s) :
    WP isa (.block digestArgs) (entered s) fun u => Ctx s u ∧ u.gpr .r0 = s.gpr .r2 ∧
      u.gpr .r1 = BitVec.ofNat 32 32 ∧ u.gpr .r2 = s.gpr .r1 := by
  have hc := entered_ctx h
  have hl := hc.inAR (d := 4) (by decide)
  have ha := hc.addr_sp h (d := 4) (by decide)
  have e2 : (entered s).gpr .r2 = s.gpr .r2 := rfl
  generalize entered s = t at hc hl ha e2
  refine WP.block_cons_iff.mpr ⟨t.setReg .r0 (t.gpr .r2), rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t.setReg .r0 (t.gpr .r2)) (t := .r2) (by decide) ha hl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil_iff.mpr ⟨((hc.setReg (by decide) _).setReg (by decide) _).setReg
    (by decide) _, ?_, ?_, ?_⟩⟩
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r1 by decide)),
      RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r2 by decide)), RegUpd.gpr_setReg_self, e2]
  · rw [RegUpd.gpr_setReg_self]; rfl
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r2 = Reg.r1 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fExp

/-! ## Memory -/

/-- Bytes outside the regions a frame lists are kept. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' p n = Spec.Ed25519.bytesAt m p n :=
  List.map_congr_left fun _ hi => Frame.bytes hf (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem Ctx.bytes {s t : State} (hc : Ctx s t) {p : Addr} {n : Nat}
    (h₁ : Region.Disjoint ⟨p, n⟩ (OUT s)) (h₂ : Region.Disjoint ⟨p, n⟩ (EXP s))
    (h₃ : Region.Disjoint ⟨p, n⟩ (SCR s)) (h₄ : Region.Disjoint ⟨p, n⟩ (STK s)) (hn : n ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem p n = Spec.Ed25519.bytesAt s.mem p n := by
  refine bytesAt_frame hc.frame (fun r hr => ?_) hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- After a call from between the pushes and the pops that writes `wr`
(within `out`, `expanded` and `scratch`) and `n` bytes below `sp`, `Ctx`
holds again. -/
theorem Ctx.call {s t t' : State} (h : Pre s) (hc : Ctx s t) {wr : List Region} {n : Nat}
    (hn : n ≤ 584) (hsub : ∀ r ∈ wr, r = OUT s ∨ r = EXP s ∨ r = SCR s)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hf : Frame (wr ++ [belowA t.sp n]) t.mem t'.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) (hsy : t'.syms = t.syms) : Ctx s t' := by
  rw [hc.below h hn] at hf
  have keep : ∀ e, 584 ≤ e → e + 4 ≤ 600 →
      t'.mem.readW (K s + BitVec.ofNat 64 e) 32 = t.mem.readW (K s + BitVec.ofNat 64 e) 32 := by
    intro e h₁ h₂
    refine hf.readW (r := ⟨K s + BitVec.ofNat 64 e, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rcases hsub r hr with rfl | rfl | rfl
      · exact h.kO (by omega_using [h₂])
      · exact h.kE (by omega_using [h₂])
      · exact h.kC (by omega_using [h₂])
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (Or.inr (by omega_using [hn, h₁])) (by omega_using [h₂]) (by omega_using [hn])
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hcs r hr hr').trans (hc.cs r hr hr'),
    (keep 596 (by decide) (by decide)).trans hc.lr, (keep 584 (by decide) (by decide)).trans hc.fOut,
    (keep 588 (by decide) (by decide)).trans hc.fExp, (keep 592 (by decide) (by decide)).trans hc.fScr,
    hsy.trans hc.sym, hc.frame.trans (hf.sub fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hsub r hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp, stk_sub s (by omega_using [hn])⟩

/-! ## The digest -/

abbrev dgCode : Prog isa := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'

abbrev dgK : Contract isa := Spec.Sha512.digestContract Arm.abi 64 Spec.Sha512.sha512 584

theorem dg_verified : Verified Arm.target dgCode dgK := Proof.MdStream.Arm.Digest.sha512_digest

theorem dg_stack : armStack dgCode = 584 := by decide +kernel

theorem dg_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .r0 = s.gpr .r2)
    (hx1 : t.gpr .r1 = BitVec.ofNat 32 32) (hx2 : t.gpr .r2 = s.gpr .r1) :
    dgK.pre (t.callEntry.withRegions [SEED s] [EXP s]) := by
  sig_pre [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, stackBelow]
  have hle : 584 ≤ t.sp.toNat := by rw [hc.sp_toNat h]; have := h.sp; omega_using [this]
  have hb := hc.below h (n := 584) (le_refl _)
  simp only [belowA, addr_sub' hle] at hb
  rw [hx0, hx1, hx2, hb]
  exact ⟨hle, by have := t.sp.isLt; omega_using [], rfl, rfl, h.es.symm, h.kS (by decide), h.kE (by decide), h.ns, h.ne⟩

theorem dg_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers ([SEED s] ++ [EXP s]) (t.rd ++ t.wr) ∧ Covers [EXP s] t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp

/-- The digest's call: the seed's digest at `expanded`. -/
theorem digest_ok {s t : State} (h : Pre s) (hc : Ctx s t) {dn : String} (hx0 : t.gpr .r0 = s.gpr .r2)
    (hx1 : t.gpr .r1 = BitVec.ofNat 32 32) (hx2 : t.gpr .r2 = s.gpr .r1) :
    WP isa (.call dn dgCode) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  refine WP.of_syms (WP.callF dg_verified.1 (dg_pre h hc hx0 hx1 hx2) (dg_cov h hc).1 (dg_cov h hc).2
    (by rw [dg_stack, hc.sp_toNat h]; have := h.sp; omega_using [this])
    (fun t' hrd hwr hsp hf hcs hpost hsy => ⟨?_, ?_⟩))
  · rw [dg_stack] at hf
    exact Ctx.call h hc (le_refl _) (by simp) hrd hwr hsp hf hcs hsy
  · sig_post [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
    rw [hx0, hx1, hx2] at hpost
    have hS : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r2)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32 :=
      hc.bytes h.os.symm h.es.symm h.sc h.ks.symm (by decide)
    exact hpost.trans (congrArg Spec.Sha512.sha512 hS)

/-! ## The public key -/

/-- The public key's arguments, from the saved ones. -/
theorem pkArgs_ok {s t : State} (h : Pre s) (hc : Ctx s t) :
    WP isa (.block pkArgs) t fun t' => Ctx s t' ∧ t'.mem = t.mem ∧ t'.gpr .r0 = s.gpr .r0 ∧
      t'.gpr .r1 = s.gpr .r1 ∧ t'.gpr .r2 = s.gpr .r3 := by
  have a0 := hc.addr_sp h (d := 0) (by decide)
  have a4 := hc.addr_sp h (d := 4) (by decide)
  have a8 := hc.addr_sp h (d := 8) (by decide)
  have i0 := hc.inAR (d := 0) (by decide)
  have i4 := hc.inAR (d := 4) (by decide)
  have i8 := hc.inAR (d := 8) (by decide)
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t) (t := .r0) (by decide) a0 i0, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := t.setReg .r0 _) (t := .r1) (by decide) a4 i4, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrSp (u := (t.setReg .r0 _).setReg .r1 _) (t := .r2) (by decide) a8 i8,
    WP.block_nil_iff.mpr
    ⟨((hc.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _, rfl, ?_, ?_, ?_⟩⟩
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r2 by decide)),
      RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r0 = Reg.r1 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fOut
  · rw [RegUpd.gpr_setReg_of_ne (h := (show ¬Reg.r1 = Reg.r2 by decide)), RegUpd.gpr_setReg_self]
    exact hc.fExp
  · rw [RegUpd.gpr_setReg_self]
    exact hc.fScr

abbrev pkK : Contract isa := Proof.Ed25519.Arm.PublicKey.pkSpecE

abbrev pkRd (s : State) : List Region := [EXP s, TB s]
abbrev pkWr (s : State) : List Region := [OUT s, SCR s]

theorem pk_stack : armStack (PublicKey.codeExpanded umaal) ≤ 280 := by cases umaal <;> decide +kernel

theorem pk_pre {s t : State} (h : Pre s) (hc : Ctx s t) (hx0 : t.gpr .r0 = s.gpr .r0)
    (hx1 : t.gpr .r1 = s.gpr .r1) (hx2 : t.gpr .r2 = s.gpr .r3)
    (hE : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)) :
    pkK.pre (t.callEntry.withRegions (pkRd s) (pkWr s)) := by
  sig_pre [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  have hle : 280 ≤ t.sp.toNat := by rw [hc.sp_toNat h]; have := h.sp; omega_using [this]
  have hb := hc.below h (n := 280) (by decide)
  simp only [belowA, addr_sub' hle] at hb
  rw [hx0, hx1, hx2, hb, hc.sym]
  have hT : ∀ r ∈ [OUT s, EXP s, SCR s, STK s], (TB s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tO
    · exact h.tE
    · exact h.tC
    · exact h.tK
  refine ⟨hle, by have := t.sp.isLt; omega_using [], rfl, fun i hi => ?_, h.fit, h.tO, h.tC, h.kT (by decide), h.al,
    rfl, rfl, h.oe, h.oc, h.ec, h.kO (by decide), h.kE (by decide), h.kC (by decide), h.no, h.ne, h.nc,
    _, by simp [Spec.Ed25519.bytesAt], hE⟩
  · exact (hc.frame.readW (r := TB s) (a := State.addr (s.syms combSym) + BitVec.ofNat 64 (8 * i)) (w := 64)
      (Offset.contains_base _ (show 8 * i + 64 / 8 ≤ 8 * combWords.length by omega_using [hi])
        (by have := h.fit; omega_using [hi, this])) hT (by decide)).trans (h.held i hi)

theorem pk_cov {s t : State} (h : Pre s) (hc : Ctx s t) :
    Covers (pkRd s ++ pkWr s) (t.rd ++ t.wr) ∧ Covers (pkWr s) t.wr := by
  refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
  · rw [hc.rd, hc.wr, h.rd, h.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [hc.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The public key's call: the seed's public key at `out`, the digest kept. -/
theorem pk_ok {s t : State} (h : Pre s) (hc : Ctx s t) {pn : String} (hx0 : t.gpr .r0 = s.gpr .r0)
    (hx1 : t.gpr .r1 = s.gpr .r1) (hx2 : t.gpr .r2 = s.gpr .r3)
    (hE : Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)) :
    WP isa (.call pn (PublicKey.codeExpanded umaal)) t fun t' => Ctx s t' ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) ∧
      Spec.Ed25519.bytesAt t'.mem (State.addr (s.gpr .r0)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  have hd := pk_stack (umaal := umaal)
  refine WP.of_syms (WP.callF Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.1
    (pk_pre h hc hx0 hx1 hx2 hE) (pk_cov h hc).1 (pk_cov h hc).2
    (by rw [hc.sp_toNat h]; have := h.sp; omega_using [hd, this])
    (fun t' hrd hwr hsp hf hcs hpost hsy =>
      ⟨Ctx.call h hc (by omega_using [hd]) (by simp) hrd hwr hsp hf hcs hsy, ?_, ?_⟩))
  · rw [← hE]
    rw [hc.below h (by omega_using [hd])] at hf
    refine bytesAt_frame hf (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.oe.symm
    · exact h.ec
    · exact (h.kE (by omega_using [hd])).symm
  · sig_post [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts] at hpost
    rw [hx0, hx1] at hpost
    exact hpost _ (by simp [Spec.Ed25519.bytesAt]) hE

/-! ## The whole function -/

/-- The body, from the pushes. -/
theorem body_ok {s : State} (h : Pre s) {dn pn : String} :
    WP isa (.seq (.block digestArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs) (.call pn (PublicKey.codeExpanded umaal)))))
      (entered s) fun t => Ctx s t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) ∧
      Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32) := by
  refine WP.seq (WP.mono (digestArgs_ok h) fun t ⟨hc, hx0, hx1, hx2⟩ => ?_)
  refine WP.seq (WP.mono (digest_ok h hc hx0 hx1 hx2) fun t ⟨hc, hE⟩ => ?_)
  refine WP.seq (WP.mono (pkArgs_ok h hc) fun t' ⟨hc', hm, hx0, hx1, hx2⟩ => ?_)
  exact pk_ok h hc' hx0 hx1 hx2 (by rw [hm]; exact hE)

theorem popped_gpr_self (r : Reg) (n : Nat) (s : State) :
    (popped r n s).gpr r = s.mem.readW (State.addr s.sp) 32 := by
  simp [popped, State.setReg]

theorem sub16_add12 (x : BitVec 32) : x - BitVec.ofNat 32 16 + BitVec.ofNat 32 12 = x - BitVec.ofNat 32 4 := by
  rw [show (16 : Nat) = 4 + 12 from rfl, ← sub_sub', BitVec.sub_add_cancel]

theorem keyPair_ok {s : State} (hs : spec.pre s) {dn pn : String} :
    WP isa (keyPair dn dgCode pn (PublicKey.codeExpanded umaal)) s fun s' => abiPreserved s s' ∧ spec.post s s' := by
  have h := pre_of hs
  have hsp := h.sp
  obtain outerR : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.lr].length)), 4 * [Reg.lr].length⟩ : Region) =
      ⟨K s + BitVec.ofNat 64 596, 4⟩ := by
    rw [show 4 * [Reg.lr].length = 4 from rfl, addrK h (by decide)]
  obtain innerR : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.lr].length) -
      BitVec.ofNat 32 (4 * [Reg.r0, .r1, .r3].length)), 4 * [Reg.r0, .r1, .r3].length⟩ : Region) =
      ⟨K s + BitVec.ofNat 64 584, 12⟩ := by
    rw [show 4 * [Reg.lr].length = 4 from rfl, show 4 * [Reg.r0, .r1, .r3].length = 12 from rfl, sub_sub',
      addrK h (by decide)]
  refine WP.frame (rs := [.lr]) (r := .lr) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_using [hsp]) (by decide) ?_
  refine WP.frame (rs := [.r0, .r1, .r3]) (r := .r3) (by decide)
    (by show 12 ≤ (s.sp - BitVec.ofNat 32 4).toNat; rw [sub_toNat' (by omega_using [hsp])]; omega_using [hsp]) (by decide)
    (WP.mono (body_ok h) fun u ⟨hu, hE, hO⟩ m₁ u₁ h₁ m₂ u₂ h₂ => ?_)
  rw [pushed_sp, innerR] at h₁
  rw [outerR] at h₂
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hl : r = .lr
    · subst hl
      dsimp only
      rw [popped_gpr_self]
      dsimp only
      rw [popped_sp, show 4 * [Reg.r0, .r1, .r3].length = 12 from rfl, hu.sp, sub16_add12, addrK h (by decide),
        h₁.readW (r := ⟨K s + BitVec.ofNat 64 596, 4⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide)]
      exact hu.lr
    · have h3 : r ≠ .r3 := by rintro rfl; revert hr; decide
      dsimp only
      rw [popped_gpr hl]
      dsimp only
      rw [popped_gpr h3]; exact hu.cs r hr hl
  · show u.sp + BitVec.ofNat 32 12 + BitVec.ofNat 32 4 = s.sp
    simp only [hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.sub_add_cancel]
  · have hf : Frame [⟨K s + BitVec.ofNat 64 584, 12⟩, ⟨K s + BitVec.ofNat 64 596, 4⟩] u.mem m₂ :=
      (h₁.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; simp).trans
        (h₂.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; simp)
    have apart : ∀ R : Region, (∀ {d n : Nat}, d + n ≤ 600 → R.Disjoint ⟨K s + BitVec.ofNat 64 d, n⟩) →
        ∀ r ∈ [(⟨K s + BitVec.ofNat 64 584, 12⟩ : Region), ⟨K s + BitVec.ofNat 64 596, 4⟩], R.Disjoint r := by
      intro R hR r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR (by decide)
      · exact hR (by decide)
    rw [← bytesAt_frame hf (apart _ fun hd => (h.kE hd).symm) (by decide)] at hE
    rw [← bytesAt_frame hf (apart _ fun hd => (h.kO hd).symm) (by decide)] at hO
    sig_post [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts]
    exact ⟨hE, hO⟩

/-! ## Constant time -/

structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  sy : s₁.syms combSym = s₂.syms combSym

theorem pub_of {s₁ s₂ : State} (h : spec.pub s₁ s₂) : Pub s₁ s₂ := by
  sig_pub [Spec.Ed25519.keyPairContract, Spec.Ed25519.keyPairSig, Spec.Ed25519.scratchWords, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts] at h
  obtain ⟨h0, hs, h1, h2, h3, h4⟩ := h
  exact ⟨h0, h1, h2, h3, h4, hs⟩

def Rel (Φ : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ Ctx s₁ a ∧ Ctx s₂ b ∧ Φ s₁ a ∧ Φ s₂ b

theorem rel_wp {c : Prog isa} {Φ Ψ : State → State → Prop} (hct : RelCT isa (Rel Φ) c fun _ _ => True)
    (hw : ∀ s t, Pre s → Ctx s t → Φ s t → WP isa c t fun t' => Ctx s t' ∧ Ψ s t') :
    RelCT isa (Rel Φ) c (Rel Ψ) := by
  intro a b ta tb a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, h₁, h₂, hp', c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ a h₁ c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ b h₂ c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem rel_sp {Φ : State → State → Prop} {a b : State} (h : Rel Φ a b) : a.sp = b.sp := by
  obtain ⟨_, _, _, _, hp, c₁, c₂, _⟩ := h
  rw [c₁.sp, c₂.sp, hp.sp]

abbrev Φ₁ (s t : State) : Prop :=
  t.gpr .r0 = s.gpr .r2 ∧ t.gpr .r1 = BitVec.ofNat 32 32 ∧ t.gpr .r2 = s.gpr .r1
abbrev Φ₂ (s t : State) : Prop :=
  Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r1)) 64 =
    Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)
abbrev Φ₃ (s t : State) : Prop :=
  Φ₂ s t ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r1 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r3

/-- The blocks' addresses are offsets of `sp`. -/
theorem digestArgs_sp : RelCT isa (fun a b => a.sp = b.sp) (.block digestArgs) fun a b => a.sp = b.sp :=
  Whole.step_sp_ct (fun _ _ _ => rfl) (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h])
    (Whole.step_sp_ct (fun _ _ _ => rfl) Whole.block_nil_ct))

theorem pkArgs_sp : RelCT isa (fun a b => a.sp = b.sp) (.block pkArgs) fun a b => a.sp = b.sp :=
  Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h])
    (Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) Whole.block_nil_ct))

abbrev Entered (a b : State) : Prop :=
  ∃ s₁ s₂, Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem body_ct {dn pn : String} :
    RelCT isa Entered (.seq (.block digestArgs) (.seq (.call dn dgCode) (.seq (.block pkArgs)
      (.call pn (PublicKey.codeExpanded umaal))))) fun _ _ => True := by
  have b₁ : RelCT isa Entered (.block digestArgs) (Rel Φ₁) := by
    intro a b ta tb a' b' hp e₁ e₂
    obtain ⟨ht, -⟩ := digestArgs_sp _ _ _ _ _ _ (by
      obtain ⟨s₁, s₂, -, -, hp, rfl, rfl⟩ := hp
      simp only [entered, pushed_sp, hp.sp]) e₁ e₂
    obtain ⟨s₁, s₂, h₁, h₂, hp', rfl, rfl⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := digestArgs_ok h₁
    obtain ⟨_, u₂, x₂, y₂⟩ := digestArgs_ok h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, h₁, h₂, hp', y₁.1, y₂.1, y₁.2, y₂.2⟩
  have b₂ : RelCT isa (Rel Φ₁) (.call dn dgCode) (Rel Φ₂) := by
    refine rel_wp (Whole.callEx dg_verified.1 dg_verified.2.1 fun a b hr => ?_)
      fun s _ h hc ⟨hx0, hx1, hx2⟩ => digest_ok h hc hx0 hx1 hx2
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨d₁, i₁, x₁⟩, ⟨d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, dg_pre h₁ c₁ d₁ i₁ x₁, dg_pre h₂ c₂ d₂ i₂ x₂, ?_, (dg_cov h₁ c₁).1, (dg_cov h₁ c₁).2,
      (dg_cov h₂ c₂).1, (dg_cov h₂ c₂).2⟩
    sig_pub [Spec.Sha512.digestContract, Spec.Sha512.digestSig, Spec.Sha512.digestPost, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, hp.sp, hp.r2, hp.r1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have b₃ : RelCT isa (Rel Φ₂) (.block pkArgs) (Rel Φ₃) :=
    rel_wp (pkArgs_sp.mono (fun _ _ hr => rel_sp hr) fun _ _ _ => trivial) fun _ _ h hc hE =>
      WP.mono (pkArgs_ok h hc) fun _ ⟨hc', hm, a, b, d⟩ => ⟨hc', by rw [Φ₂, hm]; exact hE, a, b, d⟩
  have b₄ : RelCT isa (Rel Φ₃) (.call pn (PublicKey.codeExpanded umaal)) fun _ _ => True := by
    refine Whole.callEx Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.1
      Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified.2.1 fun a b hr => ?_
    obtain ⟨s₁, s₂, h₁, h₂, hp, c₁, c₂, ⟨e₁, d₁, i₁, x₁⟩, ⟨e₂, d₂, i₂, x₂⟩⟩ := hr
    refine ⟨_, _, _, _, pk_pre h₁ c₁ d₁ i₁ x₁ e₁, pk_pre h₂ c₂ d₂ i₂ x₂ e₂, ?_, (pk_cov h₁ c₁).1,
      (pk_cov h₁ c₁).2, (pk_cov h₂ c₂).1, (pk_cov h₂ c₂).2⟩
    sig_pub [Proof.Ed25519.publicKeyExpandedContract, Proof.Ed25519.publicKeyExpandedSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Proof.Ed25519.Arm.combConsts_eq, Abi.withConsts]
    rw [c₁.sp, c₂.sp, d₁, d₂, i₁, i₂, x₁, x₂, c₁.sym, c₂.sym, hp.sp, hp.r0, hp.r1, hp.r3, hp.sy]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact b₁.seq (b₂.seq (b₃.seq b₄))

theorem keyPair_ct {dn pn : String} :
    ConstantTime isa spec.pre spec.pub (keyPair dn dgCode pn (PublicKey.codeExpanded umaal)) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => (pub_of h.2.2).sp) ?_)
  refine RelCT.frame (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_) ?_
  · rw [Argon2.Arm.push_eq (by decide) pa, Argon2.Arm.push_eq (by decide) pb, pushed_sp, pushed_sp,
      (pub_of hp.2.2).sp]
  refine RelCT.mono body_ct ?_ fun _ _ _ => trivial
  rintro a b ⟨a₀, b₀, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, pa₀, pb₀⟩, pa, pb⟩
  rw [Argon2.Arm.push_eq (by decide) pa₀] at pa
  rw [Argon2.Arm.push_eq (by decide) pb₀] at pb
  exact ⟨s₁, s₂, pre_of h₁, pre_of h₂, pub_of hp, Argon2.Arm.push_eq (by decide) pa,
    Argon2.Arm.push_eq (by decide) pb⟩

/-! ## A witness, and the artifact's obligation -/

/-- A state satisfying the precondition: `out` at `0x1000`, `expanded` at `0x2000`, the seed at
`0x3000`, `scratch` at `0x4000`, the stack below `0x9000` and the comb's tables at `0x100000`. -/
def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := Proof.Ed25519.Arm.PublicKey.satMemTE
  rd := [⟨0x3000, 32⟩, ⟨0x100000, 98304⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem sat_pre : Pre satState := by
  have hl := Proof.Ed25519.Arm.combWords_length
  refine ⟨by decide, by simp only [satState, SEED, TB, hl]; rfl, rfl,
    fun i hi => by
      have e : State.addr (satState.syms combSym) = 0x100000 := by decide
      rw [e]; exact Proof.Ed25519.Arm.PublicKey.satMemTE_held i (by rw [← hl]; exact hi), by simp only [satState, hl]; decide,
    by decide,
    by simp only [TB, OUT, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, EXP, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, SCR, hl]; exact Region.disjoint_of_sep (by decide),
    by simp only [TB, STK, hl]; exact Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩

theorem verified {dn pn : String} :
    Verified Arm.target (keyPair dn dgCode pn (PublicKey.codeExpanded umaal)) spec :=
  ⟨fun _ h => keyPair_ok h, keyPair_ct, ⟨_, spec_of sat_pre⟩⟩

end VG.Proof.Ed25519.Arm.KeyPair

end

end

/-!
# Ed25519 on ARMv7, without secret residue

`vg_ed25519_key_pair`, `vg_ed25519_sign_expanded` and `vg_ed25519_verify`,
with either multiplication of the field (`umaal`), have frames. The
postconditions of the first two read the memory on return only within their
outputs, and that of the third not at all (`Arm.Scrub.PostOut`). Each is
emitted with its cleanup (`Impl.Ed25519.Arm.Fn`): a wipe of the stack its
contract reserves, then instructions that set the registers a callee may
change, but the result, and the flags to constants. `Fn` has the theorem of
each (`Arm.Scrub.verifiedScrubbedAll`), which its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.Ed25519.Arm
open VG.Proof.Ed25519.WholeLocal (bytesAt_congr)

theorem keyPairOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.keyPairContract (abi.withConsts cs) stack) (Spec.Ed25519.keyPairSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, sd, sc], _ =>
      simp only [Spec.Ed25519.keyPairSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed25519.bytesAt m₂ ex 64 = _ ∧ Spec.Ed25519.bytesAt m₂ o 32 = _
      rw [bytesAt_congr hb.2.1, bytesAt_congr hb.1]
      exact h

theorem signExpandedOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.signExpandedContract (abi.withConsts cs) stack)
      (Spec.Ed25519.signExpandedSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, ex, pk, msg, len, sc], _ =>
      simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show ∀ seed : List Byte, _ → _ → Spec.Ed25519.bytesAt m₂ o 64 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut (cs : List (String × List (BitVec 64))) (stack : Nat) :
    PostOut (Spec.Ed25519.verifyContract (abi.withConsts cs) stack) (Spec.Ed25519.verifySig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _], _ => exact h

theorem frameOk_280 : FrameOk 280 := by decide

theorem frameOk_600 : FrameOk 600 := by decide

/-- The code of `vg_ed25519_key_pair`: the digest by `vg_sha512_digest`'s code, called as the
internal `vg_sha512_digest_core`, and the public key by
`vg_ed25519_public_key_expanded` (with `umaal`, `vg_ed25519_public_key_expanded_umaal`). -/
def keyPairCode (umaal : Bool) : Prog isa :=
  Impl.Ed25519.Arm.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core") Proof.Ed25519.Arm.KeyPair.dgCode
    ("vg_ed25519_public_key_expanded" ++ suffix umaal) (PublicKey.codeExpanded umaal)

/-! ## What the cleanup needs of the code

The code's shape is the same with either product of the field but where the
product is chosen (`Proof.Ed25519.Arm.Shape`), so each function proves it
once for both, from those lemmas and the SHA-512 functions' (`ShaScrub`). -/

theorem publicKey_codeOk (umaal : Bool) : CodeOk (PublicKey.codeExpanded umaal) 280 := by
  simp only [
    CodeOk, Impl.Ed25519.Arm.PublicKey.codeExpanded, Impl.Ed25519.Arm.PublicKey.bodyFrom,
    Impl.Ed25519.Arm.PublicKey.copyExpanded, Impl.Ed25519.Arm.Whole.wrap, Impl.Ed25519.Arm.scalarBase,
    Impl.Ed25519.Arm.scalarBaseEngine, Impl.Ed25519.Arm.combMultiply, Impl.Ed25519.Arm.combPrepare,
    Impl.Ed25519.Arm.combInit, Impl.Ed25519.Arm.combStep, Impl.Ed25519.Arm.combNeg,
    Impl.Ed25519.Arm.pointEncode, Impl.Ed25519.Arm.pointAffine, Impl.Ed25519.Arm.invert,
    Impl.Ed25519.Arm.asFn,
    Impl.Ed25519.Arm.chain250, Impl.Ed25519.Arm.sqn, Impl.Ed25519.Arm.sqnLoop, Impl.Ed25519.Arm.sqrCall, Impl.Ed25519.Arm.sqrFn,
    Impl.Ed25519.Arm.sqLoop, Impl.Ed25519.Arm.mulP,
    Impl.Ed25519.Arm.mulPc, Impl.Ed25519.Arm.mulCall, Impl.Ed25519.Arm.Whole.callWith,
    Impl.Ed25519.Arm.FieldOp.code, Impl.Ed25519.Arm.fieldCode, armStack, noIcall,
    (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.1, (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.1,
    (Proof.Ed25519.Arm.Shape.mulFn _).2.1, (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.2,
    (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.2, (Proof.Ed25519.Arm.Shape.mulFn _).2.2, Bool.and_self,
    Nat.max_self, List.length_cons, List.length_nil]
  decide

theorem keyPair_codeOk (umaal : Bool) : CodeOk (keyPairCode umaal) 600 := by
  have hd : CodeOk Proof.Ed25519.Arm.KeyPair.dgCode 584 :=
    CodeOk.mono Proof.MdStream.Arm.ShaScrub.sha512_digest (by decide)
  exact (CodeOk.push (rs := [.lr]) (j := .pop .lr 4) (CodeOk.push (rs := [.r0, .r1, .r3]) (j := .pop .r3 12)
    (CodeOk.seq ((CodeOk.block _).mono (Nat.zero_le _)) (CodeOk.seq (CodeOk.call hd)
      (CodeOk.seq ((CodeOk.block _).mono (Nat.zero_le _))
        (CodeOk.call ((publicKey_codeOk umaal).mono (by decide)))))))).mono (by decide)

theorem signExpanded_codeOk (umaal : Bool) : CodeOk (SignCached.codeExpanded umaal) 280 := by
  have hi : CodeOk (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512) 0 := CodeOk.block _
  obtain ⟨i1, i2⟩ := hi
  obtain ⟨u1, u2⟩ := Proof.MdStream.Arm.ShaScrub.sha512_update
  obtain ⟨f1, f2⟩ := Proof.MdStream.Arm.ShaScrub.sha512_finalize
  rw [Nat.le_zero] at i1 u1 f1
  simp only [
    CodeOk, i1, i2, u1, u2, f1, f2, Impl.Ed25519.Arm.combNeg, Impl.Ed25519.Arm.combStep,
    Impl.Ed25519.Arm.combInit, Impl.Ed25519.Arm.combPrepare, Impl.Ed25519.Arm.combMultiply,
    Impl.Ed25519.Arm.mulCall, Impl.Ed25519.Arm.asFn, Impl.Ed25519.Arm.pointAffine,
    Impl.Ed25519.Arm.pointEncode, Impl.Ed25519.Arm.sqn,
    Impl.Ed25519.Arm.chain250,
    Impl.Ed25519.Arm.mulPc, Impl.Ed25519.Arm.sqnLoop, Impl.Ed25519.Arm.sqrCall, Impl.Ed25519.Arm.sqrFn,
    Impl.Ed25519.Arm.sqLoop, Impl.Ed25519.Arm.mulP, Impl.Ed25519.Arm.invert,
    Impl.Ed25519.Arm.PublicKey.copyExpanded, Impl.Ed25519.Arm.scalarMulD, Impl.Ed25519.Arm.scalarFold,
    Impl.Ed25519.Arm.scalarReduceEngine, Impl.Ed25519.Arm.scalarWideMul, Impl.Ed25519.Arm.scalarReduce,
    Impl.Ed25519.Arm.scalarBaseEngine, Impl.Ed25519.Arm.scalarBase,
    Impl.Ed25519.Arm.scalarMulAddEngine, Impl.Ed25519.Arm.scalarMulAdd,
    Impl.Ed25519.Arm.SignCached.init, Impl.Ed25519.Arm.SignCached.update,
    Impl.Ed25519.Arm.SignCached.finalize, Impl.Ed25519.Arm.SignCached.hashNonce,
    Impl.Ed25519.Arm.SignCached.reduce, Impl.Ed25519.Arm.SignCached.hashChallenge,
    Impl.Ed25519.Arm.SignCached.nonceCode, Impl.Ed25519.Arm.SignCached.challengeCode,
    Impl.Ed25519.Arm.SignCached.bodyFrom, Impl.Ed25519.Arm.SignCached.codeExpanded,
    Impl.Ed25519.Arm.Whole.wrap, Impl.Ed25519.Arm.Whole.callWith, Impl.Ed25519.Arm.FieldOp.code,
    Impl.Ed25519.Arm.fieldCode, armStack, noIcall, (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.1,
    (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.1, (Proof.Ed25519.Arm.Shape.mulFn _).2.1,
    (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.2, (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.2,
    (Proof.Ed25519.Arm.Shape.mulFn _).2.2, Bool.and_self, Nat.max_self, List.length_cons,
    List.length_nil]
  decide

theorem verify_codeOk (umaal : Bool) : CodeOk (VerifyMessage.code umaal) 280 := by
  have hi : CodeOk (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512) 0 := CodeOk.block _
  obtain ⟨i1, i2⟩ := hi
  obtain ⟨u1, u2⟩ := Proof.MdStream.Arm.ShaScrub.sha512_update
  obtain ⟨f1, f2⟩ := Proof.MdStream.Arm.ShaScrub.sha512_finalize
  rw [Nat.le_zero] at i1 u1 f1
  simp only [
    CodeOk, i1, i2, u1, u2, f1, f2, Impl.Ed25519.Arm.combNeg, Impl.Ed25519.Arm.combStep,
    Impl.Ed25519.Arm.combInit, Impl.Ed25519.Arm.combPrepare, Impl.Ed25519.Arm.combMultiply,
    Impl.Ed25519.Arm.pointAdd, Impl.Ed25519.Arm.pointDouble, Impl.Ed25519.Arm.fieldZero,
    Impl.Ed25519.Arm.fieldEqual, Impl.Ed25519.Arm.constPoint, Impl.Ed25519.Arm.copyPointToQ,
    Impl.Ed25519.Arm.mulCall, Impl.Ed25519.Arm.asFn, Impl.Ed25519.Arm.Point16.addFn,
    Impl.Ed25519.Arm.Point16.doubleFn, Impl.Ed25519.Arm.Point16.addCall,
    Impl.Ed25519.Arm.Point16.doubleCall, Impl.Ed25519.Arm.canonicalY, Impl.Ed25519.Arm.pointDecodeLoad,
    Impl.Ed25519.Arm.pointDecode, Impl.Ed25519.Arm.pointEqual,
    Impl.Ed25519.Arm.sqn, Impl.Ed25519.Arm.chain250,
    Impl.Ed25519.Arm.mulPc, Impl.Ed25519.Arm.sqnLoop, Impl.Ed25519.Arm.sqrCall, Impl.Ed25519.Arm.sqrFn,
    Impl.Ed25519.Arm.sqLoop, Impl.Ed25519.Arm.mulP,
    Impl.Ed25519.Arm.rootPower, Impl.Ed25519.Arm.recoverCandidate, Impl.Ed25519.Arm.recoverSuccess,
    Impl.Ed25519.Arm.recoverInvalid, Impl.Ed25519.Arm.recoverAdjustSign, Impl.Ed25519.Arm.recoverSign,
    Impl.Ed25519.Arm.recoverPoint, Impl.Ed25519.Arm.scalarMulD, Impl.Ed25519.Arm.scalarFold,
    Impl.Ed25519.Arm.scalarReduceEngine, Impl.Ed25519.Arm.scalarReduce, Impl.Ed25519.Arm.verifyLhs,
    Impl.Ed25519.Arm.verifyCombine, Impl.Ed25519.Arm.recBit, Impl.Ed25519.Arm.recByte,
    Impl.Ed25519.Arm.recode, Impl.Ed25519.Arm.oddTableInit, Impl.Ed25519.Arm.oddTableStep,
    Impl.Ed25519.Arm.oddTable, Impl.Ed25519.Arm.slideHead, Impl.Ed25519.Arm.addEntry,
    Impl.Ed25519.Arm.slideTail, Impl.Ed25519.Arm.slideStep, Impl.Ed25519.Arm.topStep,
    Impl.Ed25519.Arm.topDigit, Impl.Ed25519.Arm.slideStart, Impl.Ed25519.Arm.slideRest,
    Impl.Ed25519.Arm.publicMul, Impl.Ed25519.Arm.verifyRhs, Impl.Ed25519.Arm.verifyEquationPoints,
    Impl.Ed25519.Arm.decodeBody, Impl.Ed25519.Arm.decodeBoth, Impl.Ed25519.Arm.verifyDecode,
    Impl.Ed25519.Arm.verifyBody, Impl.Ed25519.Arm.verifyEquation, Impl.Ed25519.Arm.VerifyMessage.init,
    Impl.Ed25519.Arm.VerifyMessage.update, Impl.Ed25519.Arm.VerifyMessage.finalize,
    Impl.Ed25519.Arm.VerifyMessage.hash, Impl.Ed25519.Arm.VerifyMessage.body,
    Impl.Ed25519.Arm.VerifyMessage.code, Impl.Ed25519.Arm.Whole.wrap, Impl.Ed25519.Arm.Whole.callWith,
    Impl.Ed25519.Arm.repeatThen, Impl.Ed25519.Arm.FieldOp.code, Impl.Ed25519.Arm.fieldCode, armStack,
    noIcall, (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.1, (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.1,
    (Proof.Ed25519.Arm.Shape.mulFn _).2.1, (Proof.Ed25519.Arm.Shape.fieldCode _ _).2.2,
    (Proof.Ed25519.Arm.Shape.mulIn _ _ _ _).2.2, (Proof.Ed25519.Arm.Shape.mulFn _).2.2, Bool.and_self,
    Nat.max_self, List.length_cons, List.length_nil]
  decide

end VG.Proof.Ed25519.Arm.Scrub

namespace VG.Proof.Ed25519.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ed25519_key_pair`, with either product of the field. -/
theorem keyPair (umaal : Bool) :
    VerifiedScrubbed target (Impl.Ed25519.Arm.Fn.keyPair umaal)
      (Spec.Ed25519.keyPairContract (abi.withConsts Impl.Ed25519.Arm.combConsts) 600) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.keyPairApi)
    { code := Scrub.keyPairCode umaal, verified := Proof.Ed25519.Arm.KeyPair.verified }
    (Scrub.keyPairOut Impl.Ed25519.Arm.combConsts 600) (scrubSideF_of (Scrub.keyPair_codeOk umaal) Scrub.frameOk_600 _)

/-- `vg_ed25519_sign_expanded`, with either product of the field. -/
theorem signExpanded (umaal : Bool) :
    VerifiedScrubbed target (Impl.Ed25519.Arm.Fn.signExpanded umaal)
      (Spec.Ed25519.signExpandedContract (abi.withConsts Impl.Ed25519.Arm.combConsts) 280) 0 :=
  verifiedScrubbedAll (api := Spec.Ed25519.signExpandedApi)
    { code := Impl.Ed25519.Arm.SignCached.codeExpanded umaal
      verified := Proof.Ed25519.Arm.SignCached.signExpanded_verified }
    (Scrub.signExpandedOut Impl.Ed25519.Arm.combConsts 280) (scrubSideF_of (Scrub.signExpanded_codeOk umaal) Scrub.frameOk_280 _)

/-- `vg_ed25519_verify`, with either product of the field. -/
theorem verify (umaal : Bool) :
    VerifiedScrubbed target (Impl.Ed25519.Arm.Fn.verify umaal)
      (Spec.Ed25519.verifyContract (abi.withConsts Impl.Ed25519.Arm.combConsts) 280) 32 :=
  verifiedScrubbedAll (api := Spec.Ed25519.verifyApi)
    { code := Impl.Ed25519.Arm.VerifyMessage.code umaal
      verified := Proof.Ed25519.Arm.VerifyMessage.verifyMessage_verified }
    (Scrub.verifyOut Impl.Ed25519.Arm.combConsts 280) (scrubSideF_of (Scrub.verify_codeOk umaal) Scrub.frameOk_280 _)

end VG.Proof.Ed25519.Arm.Fn

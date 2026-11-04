module

public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
public import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Body
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Verified
meta import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Body
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CopyDigest
meta import VerifiedGarbage.Spec.Ed25519.ExpandedSign
meta import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Expanded
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete Ed25519 signing with the seed's cached SHA-512 digest (Arm)

`codeExpanded` is `code` with its first step, `hashSeed`, replaced by
`PublicKey.copyExpanded`: the digest at the second argument is copied to `frame 184`,
where `hashSeed` leaves it. The rest is proven once, by `bodyFrom_ok` and `bodyFrom_ct`, for
both. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed25519.Arm.PublicKey (copyArgs copyWords copyExpanded)
open VG.Proof.Ed25519 (sign_of_sha512_eq sha512_length)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

/-- The digest at `seed`, read only and outside what signing writes. -/
theorem copy_src (hL : L.Ok) (h64 : L.seedLen = 64) :
    Whole.CopySrc L.E L.inputs L.outputs L.seed := by
  have hs : (⟨State.addr L.seed, 64⟩ : Region) = L.SEED := by rw [Lay.SEED, h64]
  have hi : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  refine ⟨by rw [hs]; exact hi, fun r hr => ?_, by have := hL.ns; rw [h64] at this; exact this,
    by have := hL.top; omega⟩
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

theorem bodyE_noFrames : (bodyFrom copyExpanded).noFrames = true := by
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
    WP isa codeExpanded s fun u => abiPreserved s u ∧ signLocalE.post s u := by
  obtain ⟨seed, -, hE, hk⟩ := expanded_key h
  have hw := Whole.wrap_ok bodyE_noFrames (by decide : 6 ≤ 6) (entry_below h) (entry_top h)
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
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, fun seed' _ hs' => ?_⟩
  have hm := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 64 = _
  rw [hp, hm]
  exact sign_of_sha512_eq (hE.symm.trans hs') _

theorem signE_ct : ConstantTime isa signLocalE.pre signLocalE.pub codeExpanded := by
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
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMemE, ha,
      show ¬ 0x2000 + i < 0x2000 from by omega, show 0x2000 + i < 0x2040 from by omega, ite_false,
      ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem satE_key : Spec.Ed25519.bytesAt satMemE 0x3000 32 = satKey := by
  rw [← sat_key]
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
    change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
    omega
  simp only [satMemE, e, show ¬ 0x3000 + i < 0x2000 by omega, show ¬ 0x3000 + i < 0x2040 by omega,
    show 0x3000 + i < 0x100000 by omega, ↓reduceIte]

theorem satMemE_frame : Frame [⟨0, 0x100000⟩] baseSatMem satMemE := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  rw [show (x - 0 : Addr) = x from by simp] at hn
  simp only [satMemE, show ¬ x.toNat < 0x2000 by omega, show ¬ x.toNat < 0x2040 by omega,
    show ¬ x.toNat < 0x100000 by omega, ↓reduceIte]

def satStateE : State :=
  { satStateT with mem := satMemE, rd := [⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩,
    ⟨0x100000, 98304⟩] }

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
    omega
  refine (Offset.disjoint_of_le (r₁ := ⟨0, 0x100000⟩) ?_ ?_).symm
  · change 0 + 0x100000 ≤ (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat
    omega
  · change (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat + 8 ≤ 2 ^ 64
    omega

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

theorem signExpanded_verified : Verified Arm.target codeExpanded signSpecE :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signE_ok h) signE_ct (.refl signE_implies.sat_left))
    signE_implies

end VG.Proof.Ed25519.Arm.SignCached

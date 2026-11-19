module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Dsa.Arm.Prime.TaintD
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Fin
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Base
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Load1
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Trial2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Seqs
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.St
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Body
import VerifiedGarbage.Proof.Framework.ReadHalves
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots

/-! ### `Dsa.Arm.Gen.Verified`, which the modules that import this one used -/

section

/-! # DSA parameter generation over refillable tapes on ARMv7 meets its contract

From the shared contract's precondition, the body (`body_vp`) between the
frame's allocation and release returns the status of
`Spec.Dsa.parameterSearch` and writes its parameters (or zeros), `used` and
`state`, each `u64` as two 32-bit halves (`code_ok`); two calls with the same
public data have the same public parameters, so the same trace (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP Two)
open VG.Proof.RsaKeyGen.Arm (slot)

section
variable {g1 g2 g3 : Geo}

theorem pre_preserved : ∀ r ∈ preserved, r ∈ VG.Impl.Dsa.Arm.Generation.saved.map Prod.fst := by decide

theorem outBytes_eq (G : GP) (o : COut) :
    outBytes G o = match (cRes G o).outcome with
      | .accepted a => Spec.Dsa.encodeParams G.pLen G.qLen a
      | _ => List.replicate G.outLen 0 := by
  cases o with
  | found => rfl
  | noSeeds => rfl
  | ranOut j c =>
    simp only [outBytes, cRes, VG.Proof.Dsa.Generation.ranOutResult]
    by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]

private theorem wordsAt_lost {m m' : Mem} {rs : List Region} (frame : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ w ∈ rs, (⟨a, 8 * n⟩ : Region).Disjoint w) (fit : 8 * n < 2 ^ 64) :
    Spec.Rsa.wordsAt m' a n = Spec.Rsa.wordsAt m a n := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < n := List.mem_range.mp hj
  exact frame.readW (r := ⟨a, 8 * n⟩) (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound, fit]))
    hd (by decide)

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : (Spec.Dsa.parameterSearchContract abi 304).pre s) :
    WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ (Spec.Dsa.parameterSearchContract abi 304).post s t := by
  have hpre := cin_of_pre s hs
  have spLo := hpre.spLo
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by simp only [F]; omega_using [spLo])
    (WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩) fun u hu lm lu hfl => ?_)
  have hfl' : Frame [⟨State.addr s.sp - 304#64, 304⟩] u.mem lm := by
    refine hfl.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    rw [FrameStack.addr_sub' (by simp only [F]; omega_using [spLo])]
    exact Offset.sub_below _ (by simp only [F]; omega_using []) (by simp only [F]; omega_using [])
  dsimp only
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (pre_preserved r hr)
    exact hu.regs p hp
  · show u.sp + BitVec.ofNat 32 F = s.sp
    rw [hu.sp, BitVec.sub_add_cancel]; rfl
  obtain ⟨v, fo, m, r0⟩ := hu.fo
  have res := hu.res
  have ok := hu.ok
  sig_post [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, reduceClassify,
    Loc.val, stackArgAddr, BitVec.add_zero]
  have hp : 0 < pLenOf s := by
    have := hpre.valid; simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this; omega_using [this]
  have l := hpre.lens
  have h32 : (stackArg s 0).toNat < 2 ^ 32 := (stackArg s 0).isLt
  have ht : Spec.Dsa.parameterSearch (s.mem.readW (BitVec.setWidth 64 (stackArg s 3) + 8) 64).toNat
      (s.mem.readW (BitVec.setWidth 64 (stackArg s 3)) 64).toNat
      (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r3)) (stackArg s 0).toNat) =
      cRes (mkG s) (oOf (mkG s)) := res.symm
  rw [ht]
  generalize hO : oOf (mkG s) = o at fo ok
  have hB : Spec.Dsa.parameterEntropy (pLenOf s) < 2 ^ 32 := by
    simp only [mkG] at l; simp only [Spec.Dsa.parameterEntropy]
    rcases l with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  -- The words' bounds.
  have hU : (cRes (mkG s) o).used < 2 ^ 32 := by
    cases o with
    | found a u => exact Nat.lt_of_le_of_lt ok h32
    | noSeeds c => exact Nat.lt_of_le_of_lt ok h32
    | ranOut j c =>
      simp only [cRes, VG.Proof.Dsa.Generation.ranOutResult]
      split <;> exact Nat.lt_of_le_of_lt ok.1 h32
  have hR : (cRes (mkG s) o).remaining < 2 ^ 32 := by
    cases o with
    | found => exact Nat.zero_lt_succ _
    | noSeeds => exact Nat.zero_lt_succ _
    | ranOut j c =>
      simp only [cRes, VG.Proof.Dsa.Generation.ranOutResult]
      split
      · exact Nat.zero_lt_succ _
      · simp only [Spec.Dsa.ParameterSearchResult.remaining]
        have := ok.2; simp only [Spec.Dsa.parameterSeeds] at this; omega_using [this]
  have hQ : VG.Proof.Dsa.Generation.requested (mkG s).pLen (cRes (mkG s) o) < 2 ^ 32 := by
    simp only [VG.Proof.Dsa.Generation.requested, VG.Proof.Entropy.requested]
    split
    · simp only [VG.Proof.Dsa.Generation.parameterRequest, VG.Proof.Entropy.request]
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hB
    · exact Nat.zero_lt_succ _
  -- `state[1]` and `state[2]`, from the call.
  have w8 : s.mem.readW (State.addr (stackArg s 3) + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (pLenOf s) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have w16 := hpre.budget
  have lo : ∀ {a : Addr} {n : Nat}, s.mem.readW a 64 = BitVec.ofNat 64 n → n < 2 ^ 32 →
      s.mem.readW a 32 = BitVec.ofNat 32 n := fun {a n} h hn => by
    rw [Mem.readW_lo32 h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega_using []
  have hi : ∀ {a : Addr} {n : Nat}, s.mem.readW a 64 = BitVec.ofNat 64 n → n < 2 ^ 32 →
      s.mem.readW (a + BitVec.ofNat 64 4) 32 = 0 := fun {a n} h hn => by
    rw [Mem.readW_hi32 h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow,
      show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [hn]
  have hp32 : pLenOf s < 2 ^ 32 := by
    simp only [mkG] at l; rcases l with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
  have a12 : BitVec.setWidth 64 (stackArg s 3) + BitVec.ofNat 64 12 =
      State.addr (stackArg s 3) + BitVec.ofNat 64 8 + BitVec.ofNat 64 4 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  have a20 : BitVec.setWidth 64 (stackArg s 3) + BitVec.ofNat 64 20 =
      State.addr (stackArg s 3) + BitVec.ofNat 64 16 + BitVec.ofNat 64 4 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  refine ⟨?_, ?_, ?_, VG.Proof.Dsa.Generation.requested (pLenOf s) (cRes (mkG s) o), ?_,
    by rw [← hO, ← ht]; exact VG.Proof.Dsa.Generation.requested_requests hp _ _⟩
  · have hst : (cRes (mkG s) o).status < 4 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    rw [BitVec.setWidth_append_eq_right]
    show (u.gpr .r0).toNat = _
    rw [r0, fo.r0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · rw [show Spec.Rsa.bytesAt lm (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat =
        Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat from
      VG.Proof.Rsa.rsa_bytes_frame hfl' (by have := (s.gpr .r1).isLt; omega_using [])
        fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hpre.fO.symm, m]
    exact fo.out.trans (outBytes_eq _ _)
  · rw [wordsAt_lost (n := 1) hfl' (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hpre.fU.symm)
      (by decide), m]
    show [v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [VG.Proof.RsaKeyGen.Arm.pair_word]
    have e0 : slot v.mem (State.addr (s.gpr .r2)) (2 * 0) = BitVec.ofNat 32 (cRes (mkG s) o).used := fo.u0
    have e1 : slot v.mem (State.addr (s.gpr .r2)) (2 * 0 + 1) = 0#32 := fo.u1
    rw [e0, e1, VG.Proof.RsaKeyGen.Arm.pair_ofNat hU]
  · rw [wordsAt_lost (n := 4) hfl' (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hpre.fS.symm)
      (by decide), m]
    have k : ∀ j, 2 ≤ j → j < 6 → slot v.mem (BitVec.setWidth 64 (stackArg s 3)) j =
        slot s.mem (BitVec.setWidth 64 (stackArg s 3)) j := fo.s25
    refine VG.Proof.RsaKeyGen.Arm.wordsAt_slots v.mem _ hR hp32 hB hQ fo.s0 fo.s1 ?_ ?_ ?_ ?_ fo.s6 fo.s7
    · rw [k 2 (by decide) (by decide)]; exact lo w8 hp32
    · rw [k 3 (by decide) (by decide)]
      show s.mem.readW (BitVec.setWidth 64 (stackArg s 3) + BitVec.ofNat 64 12) 32 = 0
      rw [a12]; exact hi w8 hp32
    · rw [k 4 (by decide) (by decide)]; exact lo w16 hB
    · rw [k 5 (by decide) (by decide)]
      show s.mem.readW (BitVec.setWidth 64 (stackArg s 3) + BitVec.ofNat 64 20) 32 = 0
      rw [a20]; exact hi w16 hB

theorem map_toNat_inj {a b : List Byte} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

theorem map_toNat_inj64 {a b : List (BitVec 64)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two calls with the same public data have the same public parameters. -/
theorem mkG_eq {s₁ s₂ : State} (h : (Spec.Dsa.parameterSearchContract abi 304).pub s₁ s₂) : mkG s₁ = mkG s₂ := by
  sig_pub [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, reduceClassify,
    Loc.val, stackArgAddr, BitVec.add_zero] at h
  obtain ⟨hsp, hl, r0, r1, r2, r3, a0, a1, a2, a3⟩ := h
  obtain ⟨hW, hR⟩ := List.append_inj hl (by simp [Spec.Rsa.wordsAt])
  have eW := map_toNat_inj64 hW
  have eR := map_toNat_inj hR
  simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.cons.injEq] at eW
  obtain ⟨w0, w1, -, -⟩ := eW
  have pl : pLenOf s₁ = pLenOf s₂ := congrArg BitVec.toNat w1
  have kk : s₁.mem.readW (State.addr (stackArg s₁ 3)) 64 = s₂.mem.readW (State.addr (stackArg s₂ 3)) 64 := by
    have := w0; simp only [Nat.mul_zero, BitVec.add_zero] at this; exact this
  unfold mkG
  rw [pl, kk]
  have eR' : Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat := eR
  rw [eR', hsp, r0, r1, r2, r3, a0, a1, a2, a3]

theorem alloc_push {s : State} (h : CIn s) : isa.push (.alloc F) s = some (allocated F s) := by
  have hsp : F ≤ s.sp.toNat := by have := h.spLo; simp only [F]; omega_using [this]
  have hn : 0 < F ∧ F < 4096 ∧ F % 8 = 0 ∧ encodable (BitVec.ofNat 32 F) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- The code leaks only what its contract makes public. -/
theorem code_ct (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    ConstantTime isa (Spec.Dsa.parameterSearchContract abi 304).pre
      (Spec.Dsa.parameterSearchContract abi 304).pub (code g1 g2 g3) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  have p₁ := cin_of_pre s₁ h₁
  have p₂ := cin_of_pre s₂ h₂
  have hG := mkG_eq hp
  cases e₁ with
  | frame ha₁ hb₁ _ =>
    cases e₂ with
    | frame ha₂ hb₂ _ =>
      rw [alloc_push p₁, Option.some.injEq] at ha₁
      rw [alloc_push p₂, Option.some.injEq] at ha₂
      subst ha₁ ha₂
      have hh := (body_vp (G := mkG s₁) K1 K2 K3).ct _ _ _ _ _ _
        ⟨s₁, s₂, ⟨rfl, p₁, rfl⟩, ⟨rfl, p₂, hG.symm⟩⟩ hb₁ hb₂ |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

/-- A 1024/160 call with an empty tape: `out` at `0x1000`, `used` at
`0x2000`, `rand` at `0x5000`, `state` at `0x3000` (`[0, 128, 32769 · 128, 0]`),
`scratch` at `0x30000`, the stack arguments at `0x20000`. -/
def searchSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 276 | .r2 => 0x2000 | .r3 => 0x5000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20006 then 0x03 else if a = 0x20009 then 0x24 else if a = 0x2000d then 0x30
    else if a = 0x3008 then 0x80 else if a = 0x3010 then 0x80 else if a = 0x3012 then 0x40 else 0
  rd := [⟨0x5000, 0⟩, ⟨0x20000, 16⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x30000, 73728⟩, ⟨0x3000, 32⟩]

theorem search_satisfiable : ∃ s, (Spec.Dsa.parameterSearchContract abi 304).pre s := by
  sig_implies_sat [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr, stackArgAddr, BitVec.add_zero]
    [searchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using searchSat

/-- `vg_dsa_parameter_search` over the three geometries meets its contract. -/
theorem search_verified (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    Verified target (code g1 g2 g3) (Spec.Dsa.parameterSearchContract abi 304) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok K1 K2 K3 hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct K1 K2 K3,
    search_satisfiable⟩

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Prime.Top5`, which only this module used -/

section

/-! ### `Dsa.Arm.Prime.Body`, which this module and modules that import it used -/

section

/-! # DSA's probable-prime test on ARMv7: the body (`body_vp`)

The candidate loaded, trial division, and then Miller–Rabin or 2: which is
public, as the candidate is (`compv_pub`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {P : CP}

theorem compv_pub {σ : State} (pre : In P σ) :
    compv P σ = Spec.RsaKeyGen.obviouslyComposite P.bits P.cand := by
  unfold compv; rw [pre.cand]

theorem b2n_eq0' (b : Bool) : decide (b2n b = 0) = !b := by cases b <;> rfl

/-- The body: the status and the octets read of the test. -/
theorem body_vp (v : RoundImpl) {E : State → Prop} (hE : ∀ σ, E σ → In P σ) :
    VP (fun σ s => E σ ∧ Bk P σ s) (Impl.Dsa.Arm.ProbablePrime.body v.name v.code)
      (RF P E (statD P) (usedD P)) := by
  unfold Impl.Dsa.Arm.ProbablePrime.body
  rw [List.append_assoc]
  refine VP.seqs_app (List.cons_ne_nil _ _) (by simp) loadC_vp
    (VP.seqs_app (fun h => by simp [trial] at h) (List.cons_ne_nil _ _)
      (VP.mono (F := S1 P E) (trial_vp (E := E))
        (fun σ s (h : S0 P E σ s) => h.mono (fun j hj => ⟨by mem_sub, rfl⟩) fun d hd => ⟨hd, rfl⟩)
        fun _ _ h => h) ?_)
  have k2 : ∀ σ, E σ → V2 P σ sTr = b2n (Spec.RsaKeyGen.obviouslyComposite P.bits P.cand) := fun σ e => by
    simp only [V2, upd_self]; rw [compv_pub (hE σ e)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [isa_eq, isa_eq, h₁.2, h₂.2, k2 σ₁ h₁.1.1, k2 σ₂ h₂.1.1]) ?_ ?_
  · refine VP.ofImp (p := Spec.RsaKeyGen.obviouslyComposite P.bits P.cand = false) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0'] at t; simpa using t) fun hc => ?_
    exact (mrPart_vp v (E := E) fun σ e => ⟨hE σ e, by rw [EM, compv_pub (hE σ e), hc]⟩).mono
      (fun σ s h => h.1.1) fun _ _ h => h
  · refine VP.ofImp (p := Spec.RsaKeyGen.obviouslyComposite P.bits P.cand = true) (fun σ s h => by
      have t := h.2; rw [isa_eq, h.1.2, k2 σ h.1.1.1, b2n_eq0'] at t; simpa using t) fun hc => ?_
    exact (composite_vp (E := E) fun σ e => ⟨hE σ e, by rw [compv_pub (hE σ e), hc]⟩).mono
      (fun σ s h => h.1.1) fun _ _ h => h

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Top4`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Prime.Top3`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Prime.Top2`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Prime.Top1`, which this module and modules that import it used -/

section

/-! # DSA's probable-prime test on ARMv7: the contract's arguments

`mkP bits s`: the public parameters of a call from `s`; `CIn bits s`: the
contract's precondition for the size `bits`, the second stack argument, as
the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- The public parameters of a call: the frame, the pointers, the lengths,
the candidate and the tape. -/
def mkP (bits : Nat) (s : State) : CP where
  sp := s.sp - BitVec.ofNat 32 88
  uP := stackArg s 0
  nP := s.gpr .r2
  cP := s.gpr .r0
  B := s.gpr .r0 + BitVec.ofNat 32 keyOff
  L := 8 * Impl.Dsa.Arm.ProbablePrime.words bits
  rl := (s.gpr .r3).toNat
  SL := keyWords bits
  bits := bits
  cand := Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))
  rnd := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat

/-- The arguments' regions, and the stack below the caller's. -/
abbrev cW (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
abbrev cU (s : State) : Region := ⟨State.addr (stackArg s 0), 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 8⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 144#64, 144⟩

/-- The sizes the test takes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

theorem bits_iff {bits : Nat} : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes ↔ Bits bits := by
  simp [Impl.Dsa.Arm.ProbablePrime.sizes]

/-- The test's contract. -/
abbrev primeK : Contract isa :=
  Proof.Dsa.ProbablePrime.sizedContract layout Impl.Dsa.Arm.ProbablePrime.sizes abi 144

/-- The contract's precondition, for the size `bits`. -/
structure CIn (bits : Nat) (s : State) : Prop where
  sized : Bits bits
  arg : stackArg s 1 = BitVec.ofNat 32 bits
  spLo : 144 ≤ s.sp.toNat
  spHi : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [cR s, cA s]
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  wA : (cW s).Disjoint (cA s)
  rU : (cR s).Disjoint (cU s)
  uA : (cU s).Disjoint (cA s)
  FW : (cF s).Disjoint (cW s)
  FR : (cF s).Disjoint (cR s)
  FU : (cF s).Disjoint (cU s)
  FA : (cF s).Disjoint (cA s)
  fw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  fr : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fu : (stackArg s 0).toNat + 8 ≤ 2 ^ 32
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))) = bits

theorem cin_of_pre (s : State) (h : primeK.pre s) : CIn (stackArg s 1).toNat s := by
  sig_pre [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, wR, wU, wA, rU, uA, FW, FR, FU, FA, fw, fr, fu, hb, size, odd, bl⟩ := h
  exact ⟨bits_iff.1 hb, by simp, spLo, spHi, rd, wr, wR, wU, wA, rU, uA, FW, FR, FU, FA, fw, fr, fu, size, odd, bl⟩

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # DSA's probable-prime test on ARMv7: the arguments to the allocation (`pre_ok`)

After the allocation of 32 bytes at `aA s`, `pre` stores the words
`allocVals` there, those of the size from the second stack argument
(`sizeVals`), `used` into `r2` and `L` into `r1`; only `r1`–`r3`, `r12` and
the allocation change.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_str wp_mov wp_dp wp_ldr op2_imm op2_lsl op2_lsr dpVal)
open VG.Proof.Bignum.Arm (wp_stackAddr)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords len draw checks)
open VG.Impl.RsaKeyGen.Arm.Candidate (aoR aoRl aoP aoS aoSl aoEl aoPl)

/-- The allocation's base. -/
abbrev aA (s : State) : Addr := State.addr (s.sp - BitVec.ofNat 32 32)

/-- The allocation's words, by offset. -/
def allocVals (bits : Nat) (s : State) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 (len bits)), (4, s.gpr .r0), (8, BitVec.ofNat 32 (draw bits)), (12, s.gpr .r2),
    (16, s.gpr .r3), (20, s.gpr .r0 + BitVec.ofNat 32 keyOff), (24, BitVec.ofNat 32 (keyWords bits)),
    (28, BitVec.ofNat 32 (checks bits))]

/-- The words `pre` computes from the size, for each size. -/
theorem sizeVals {bits : Nat} (hb : Bits bits) :
    ((BitVec.ofNat 32 bits + 255) >>> 8) <<< 5 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧
      BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) <<< 4 + 32 = BitVec.ofNat 32 (keyWords bits) ∧
      BitVec.ofNat 32 bits >>> 3 = BitVec.ofNat 32 (len bits) ∧
      ((BitVec.ofNat 32 bits + 63) >>> 6) <<< 3 = BitVec.ofNat 32 (draw bits) ∧
      ((BitVec.ofNat 32 bits - 1) >>> 11) <<< 6 + 64 = BitVec.ofNat 32 (checks bits) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

theorem readW_writeW_off (m : Mem) (A : Addr) {o p : Nat} (v : BitVec 32) (h : o + 4 ≤ p ∨ p + 4 ≤ o)
    (ho : o + 4 ≤ 2 ^ 64) (hp : p + 4 ≤ 2 ^ 64) :
    (m.writeW (A + BitVec.ofNat 64 o) v).readW (A + BitVec.ofNat 64 p) 32 = m.readW (A + BitVec.ofNat 64 p) 32 :=
  Mem.readW_writeW_sep (Offset.sep A (by omega_arith) hp ho) (by decide)

section
variable {s : State}

theorem aA_add (h : 32 ≤ s.sp.toNat) {o : Nat} (ho : s.sp.toNat + o < 2 ^ 32 + 32) :
    State.addr (s.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := by
  rw [BitVec.add_zero]
  exact addr_add (by rw [sub_toNat' h]; omega_arith)

/-- Stack argument `i < 2` is readable. -/
theorem argIn (h1 : s.sp.toNat + 8 ≤ 2 ^ 32) (hA : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr) {i : Nat}
    (hi : i < 2) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 := by
  refine ⟨_, hA, ?_⟩
  obtain e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]; exact addr_add (by omega_arith)
  rw [e]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem CIn.argsIn {bits : Nat} (h : CIn bits s) : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr :=
  List.mem_append_left _ (by rw [h.rd]; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- The allocation's arguments. -/
theorem pre_ok {bits : Nat} (hb : Bits bits) (h1 : 144 ≤ s.sp.toNat) (h2 : s.sp.toNat + 8 ≤ 2 ^ 32)
    (hA : (⟨stackArgAddr s 0, 8⟩ : Region) ∈ s.rd ++ s.wr) (harg : stackArg s 1 = BitVec.ofNat 32 bits) :
    WP isa (.block Impl.Dsa.Arm.ProbablePrime.pre) (allocated 32 s) fun t =>
      Rest [.r1, .r2, .r3, .r12] (allocated 32 s) t ∧ Frame [⟨aA s, 32⟩] s.mem t.mem ∧
      (∀ p ∈ allocVals bits s, t.mem.readW (aA s + BitVec.ofNat 64 p.1) 32 = p.2) ∧
      t.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧ t.gpr .r2 = stackArg s 0 := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := sizeVals hb
  have hs := s.sp.isLt
  have hsp : (allocated 32 s).sp = s.sp - BitVec.ofNat 32 32 := rfl
  have hwr : (allocated 32 s).wr = ⟨aA s, 32⟩ :: s.wr := rfl
  have hrd : (allocated 32 s).rd ++ (allocated 32 s).wr = s.rd ++ (⟨aA s, 32⟩ :: s.wr) := rfl
  obtain win : ∀ o, o + 4 ≤ 32 → InRegions (allocated 32 s).wr (aA s + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨_, by rw [hwr]; exact List.mem_cons_self, Offset.contains_base _ ho (by omega_arith)⟩
  -- The stack arguments, above the allocation.
  obtain argIn' : ∀ i, i < 2 → InRegions ((allocated 32 s).rd ++ (allocated 32 s).wr) (stackArgAddr s i) 4 :=
    fun i hi => by
      obtain ⟨r, hr, hc⟩ := argIn h2 hA hi; refine ⟨r, ?_, hc⟩
      rw [hrd]; rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain eA : ∀ i, i < 2 → stackArgAddr s i = aA s + BitVec.ofNat 64 (32 + 4 * i) := fun i hi => by
    rw [aA, addr_sub' (by omega_arith), BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    exact addr_add (by omega_arith)
  obtain eA0 : stackArgAddr s 0 = aA s + BitVec.ofNat 64 32 := eA 0 (by decide)
  obtain eA1 : stackArgAddr s 1 = aA s + BitVec.ofNat 64 36 := eA 1 (by decide)
  unfold Impl.Dsa.Arm.ProbablePrime.pre Impl.Dsa.Arm.ProbablePrime.wordsOf Impl.Dsa.Arm.ProbablePrime.bitsOf
  simp only [List.cons_append, List.nil_append, aoR, aoRl, aoP, aoS, aoSl, aoEl, aoPl,
    Impl.Dsa.Arm.ProbablePrime.aoChk]
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u0 h0 => ?_
  obtain r12 : ∀ {u : State}, u.gpr .r12 = u0.gpr .r12 → ∀ o, o ≤ 36 →
      State.addr (u.gpr .r12 + BitVec.ofNat 32 o) = aA s + BitVec.ofNat 64 o := fun hu o ho => by
    rw [hu, h0.gpr, hsp]; exact aA_add (by omega_arith) (by omega_arith)
  obtain hr12 : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u → u.gpr .r12 = u0.gpr .r12 := fun R => R.gpr _ (by decide)
  obtain hwr' : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u → u.wr = (allocated 32 s).wr := fun R => by
    rw [R.wr, h0.wr]
  obtain hrd' : ∀ {u : State}, Rest [.r1, .r2, .r3] u0 u →
      u.rd ++ u.wr = (allocated 32 s).rd ++ (allocated 32 s).wr := fun R => by
    rw [R.rd, R.wr, h0.rd, h0.wr]
  -- The arguments.
  refine wp_str (a := aA s + BitVec.ofNat 64 12) (by decide) (r12 rfl _ (by decide))
    (by rw [h0.wr]; exact win 12 (by decide)) fun u1 m1 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 16) (by decide) (r12 (by rw [m1.gpr]) _ (by decide))
    (by rw [m1.wr, h0.wr]; exact win 16 (by decide)) fun u2 m2 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 4) (by decide) (r12 (by rw [m2.gpr, m1.gpr]) _ (by decide))
    (by rw [m2.wr, m1.wr, h0.wr]; exact win 4 (by decide)) fun u3 m3 => ?_
  refine wp_dp (op2_imm (by decide)) fun u4 h4 => ?_
  refine wp_str (a := aA s + BitVec.ofNat 64 20) (by decide)
    (r12 (by rw [h4.other _ (by decide), m3.gpr, m2.gpr, m1.gpr]) _ (by decide))
    (by rw [h4.wr, m3.wr, m2.wr, m1.wr, h0.wr]; exact win 20 (by decide)) fun u5 m5 => ?_
  obtain R5 : Rest [.r1, .r2, .r3] u0 u5 :=
    ((((m1.rest _).trans (m2.rest _)).trans (m3.rest _)).trans (h4.rest (by simp))).trans (m5.rest _)
  -- The size.
  refine wp_ldr (a := stackArgAddr s 1) (by decide) (by rw [r12 (hr12 R5) 36 (by decide), eA1])
    (by rw [hrd' R5]; exact argIn' 1 (by decide)) fun u6 h6 => ?_
  obtain R6 : Rest [.r1, .r2, .r3] u0 u6 := R5.trans (h6.rest (by simp))
  obtain x6 : u6.gpr .r2 = BitVec.ofNat 32 bits := by
    rw [h6.gpr, ← harg, m5.mem, h4.mem, m3.mem, m2.mem, m1.mem, h0.mem]
    show _ = s.mem.readW (stackArgAddr s 1) 32
    rw [eA1]
    simp (disch := first | decide | omega_arith) only [readW_writeW_off]
    rfl
  -- `L`.
  refine wp_dp (op2_imm (by decide)) fun u7 h7 => wp_mov (op2_lsr (by decide)) fun u8 h8 =>
    wp_mov (op2_lsl (by decide)) fun u9 h9 => ?_
  obtain x9 : u9.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits) := by
    rw [h9.gpr, h8.gpr, h7.gpr, x6]; simp only [dpVal]; exact v1
  obtain Q9 : Rest [.r1, .r3] u6 u9 := ((h7.rest (by simp)).trans (h8.rest (by simp))).trans (h9.rest (by simp))
  -- The key working space's words.
  refine wp_mov (op2_lsl (by decide)) fun u10 h10 => wp_dp (op2_imm (by decide)) fun u11 h11 => ?_
  obtain x11 : u11.gpr .r3 = BitVec.ofNat 32 (keyWords bits) := by
    rw [h11.gpr, h10.gpr, x9]; simp only [dpVal]; exact v2
  obtain Q11 : Rest [.r1, .r3] u6 u11 := (Q9.trans (h10.rest (by simp))).trans (h11.rest (by simp))
  obtain R11 : Rest [.r1, .r2, .r3] u0 u11 := R6.trans (Q11.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 24) (by decide) (r12 (hr12 R11) _ (by decide))
    (by rw [hwr' R11]; exact win 24 (by decide)) fun u12 m12 => ?_
  -- The candidate's bytes.
  refine wp_mov (op2_lsr (by decide)) fun u13 h13 => ?_
  obtain r2_12 : u12.gpr .r2 = BitVec.ofNat 32 bits := by rw [m12.gpr, Q11.gpr _ (by decide), x6]
  obtain x13 : u13.gpr .r3 = BitVec.ofNat 32 (len bits) := by rw [h13.gpr, r2_12, v3]
  obtain R13 : Rest [.r1, .r2, .r3] u0 u13 := (R11.trans (m12.rest _)).trans (h13.rest (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 0) (by decide) (r12 (hr12 R13) _ (by decide))
    (by rw [hwr' R13]; exact win 0 (by decide)) fun u14 m14 => ?_
  -- A witness's octets.
  obtain r2_14 : u14.gpr .r2 = BitVec.ofNat 32 bits := by rw [m14.gpr, h13.other _ (by decide), r2_12]
  refine wp_dp (op2_imm (by decide)) fun u15 h15 => wp_mov (op2_lsr (by decide)) fun u16 h16 =>
    wp_mov (op2_lsl (by decide)) fun u17 h17 => ?_
  obtain x17 : u17.gpr .r3 = BitVec.ofNat 32 (draw bits) := by
    rw [h17.gpr, h16.gpr, h15.gpr, r2_14]; simp only [dpVal]; exact v4
  obtain Q17 : Rest [.r3] u14 u17 := ((h15.rest (by simp)).trans (h16.rest (by simp))).trans (h17.rest (by simp))
  obtain R17 : Rest [.r1, .r2, .r3] u0 u17 := (R13.trans (m14.rest _)).trans (Q17.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 8) (by decide) (r12 (hr12 R17) _ (by decide))
    (by rw [hwr' R17]; exact win 8 (by decide)) fun u18 m18 => ?_
  -- The uniform witnesses needed.
  obtain r2_18 : u18.gpr .r2 = BitVec.ofNat 32 bits := by rw [m18.gpr, Q17.gpr _ (by decide), r2_14]
  refine wp_dp (op2_imm (by decide)) fun u19 h19 => wp_mov (op2_lsr (by decide)) fun u20 h20 =>
    wp_mov (op2_lsl (by decide)) fun u21 h21 => wp_dp (op2_imm (by decide)) fun u22 h22 => ?_
  obtain x22 : u22.gpr .r3 = BitVec.ofNat 32 (checks bits) := by
    rw [h22.gpr, h21.gpr, h20.gpr, h19.gpr, r2_18]; simp only [dpVal]; exact v5
  obtain Q22 : Rest [.r3] u18 u22 :=
    (((h19.rest (by simp)).trans (h20.rest (by simp))).trans (h21.rest (by simp))).trans (h22.rest (by simp))
  obtain R22 : Rest [.r1, .r2, .r3] u0 u22 := (R17.trans (m18.rest _)).trans (Q22.mono (by simp))
  refine wp_str (a := aA s + BitVec.ofNat 64 28) (by decide) (r12 (hr12 R22) _ (by decide))
    (by rw [hwr' R22]; exact win 28 (by decide)) fun u23 m23 => ?_
  obtain R23 : Rest [.r1, .r2, .r3] u0 u23 := R22.trans (m23.rest _)
  obtain mem23 : u23.mem = ((((((((s.mem.writeW (aA s + BitVec.ofNat 64 12) (s.gpr .r2)).writeW
      (aA s + BitVec.ofNat 64 16) (s.gpr .r3)).writeW (aA s + BitVec.ofNat 64 4) (s.gpr .r0)).writeW
      (aA s + BitVec.ofNat 64 20) (s.gpr .r0 + BitVec.ofNat 32 keyOff)).writeW
      (aA s + BitVec.ofNat 64 24) (BitVec.ofNat 32 (keyWords bits))).writeW
      (aA s + BitVec.ofNat 64 0) (BitVec.ofNat 32 (len bits))).writeW
      (aA s + BitVec.ofNat 64 8) (BitVec.ofNat 32 (draw bits))).writeW
      (aA s + BitVec.ofNat 64 28) (BitVec.ofNat 32 (checks bits))) := by
    rw [m23.mem, x22, h22.mem, h21.mem, h20.mem, h19.mem, m18.mem, x17, h17.mem, h16.mem, h15.mem, m14.mem, x13,
      h13.mem, m12.mem, x11, h11.mem, h10.mem, h9.mem, h8.mem, h7.mem, h6.mem, m5.mem, h4.gpr, dpVal, h4.mem,
      m3.mem, m2.mem, m1.mem, h0.mem]
    simp only [m1.gpr, m2.gpr, m3.gpr, h0.other .r0 (by decide), h0.other .r2 (by decide),
      h0.other .r3 (by decide)]
    rfl
  -- `used`.
  refine wp_ldr (a := stackArgAddr s 0) (by decide) (by rw [r12 (hr12 R23) 32 (by decide), eA0])
    (by rw [hrd' R23]; exact argIn' 0 (by decide)) fun t ht => WP.block_nil ?_
  obtain Q23 : Rest [.r2, .r3] u9 u23 :=
    ((((((((((((((h10.rest (by simp)).trans (h11.rest (by simp))).trans (m12.rest _)).trans
      (h13.rest (by simp))).trans (m14.rest _)).trans (h15.rest (by simp))).trans (h16.rest (by simp))).trans
      (h17.rest (by simp))).trans (m18.rest _)).trans (h19.rest (by simp))).trans (h20.rest (by simp))).trans
      (h21.rest (by simp))).trans (h22.rest (by simp))).trans (m23.rest _))
  obtain fr : Frame [⟨aA s, 32⟩] s.mem u23.mem := by
    rw [mem23]
    obtain c : ∀ o, o + 4 ≤ 32 → (⟨aA s, 32⟩ : Region).Contains (aA s + BitVec.ofNat 64 o) (32 / 8) :=
      fun o ho => Offset.contains_base _ ho (by omega_arith)
    exact (((((((((Frame.refl _ _).writeW List.mem_cons_self _ (c 12 (by decide))).writeW List.mem_cons_self _
      (c 16 (by decide))).writeW List.mem_cons_self _ (c 4 (by decide))).writeW List.mem_cons_self _
      (c 20 (by decide))).writeW List.mem_cons_self _ (c 24 (by decide))).writeW List.mem_cons_self _
      (c 0 (by decide))).writeW List.mem_cons_self _ (c 8 (by decide))).writeW List.mem_cons_self _
      (c 28 (by decide)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, by rw [ht.mem]; exact fr, fun p hp => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.other _ hr.2.1, R23.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h0.other _ hr.2.2.2]
  · rw [ht.rd, R23.rd, h0.rd]
  · rw [ht.wr, hwr' R23]
  · rw [ht.sp, R23.sp, h0.sp]
  · rw [ht.mem, mem23]
    simp only [allocVals, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := first | decide | omega_arith) only [readW_writeW_off, Mem.readW_writeW_self32]
  · rw [ht.other _ (by decide), Q23.gpr _ (by decide), x9]
  · rw [ht.gpr, mem23]
    simp only [stackArg]
    rw [eA0]
    simp (disch := first | decide | omega_arith) only [readW_writeW_off]

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # DSA's probable-prime test on ARMv7: the body's start (`in_c`)

After the allocation, `pre` (`PreOut`) and the push, with the regions
`xRegs` and the candidate readable, the body starts (`In`). The allocation,
the frame and the round's frame below it are the 144 bytes below the
caller's stack pointer (`cF`), at offsets of its base (`fB`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- What `pre` leaves. -/
structure PreOut (bits : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r12] (allocated 32 s) t
  frame : Frame [⟨aA s, 32⟩] s.mem t.mem
  vals : ∀ p ∈ allocVals bits s, t.mem.readW (aA s + BitVec.ofNat 64 p.1) 32 = p.2
  r1 : t.gpr .r1 = BitVec.ofNat 32 (8 * Impl.Dsa.Arm.ProbablePrime.words bits)
  r2 : t.gpr .r2 = stackArg s 0

/-- The candidate's region. -/
abbrev cCd (bits : Nat) (s : State) : Region := ⟨State.addr (s.gpr .r0), Impl.Dsa.Arm.ProbablePrime.len bits⟩

/-- The regions the body runs with. -/
def xRegs (P : CP) : List Region := [P.rFr, P.rAl, P.rU, P.rS, P.rM]

/-- The state the body runs from. -/
abbrev sx (bits : Nat) (s t : State) : State := (pcPushed t).withRegions (cCd bits s :: s.rd) (xRegs (mkP bits s))

/-- `cF`'s base. -/
abbrev fB (s : State) : Addr := State.addr s.sp - 144#64

section
variable {bits : Nat} {s t : State}

theorem Bits.facts (hb : Bits bits) :
    32 ≤ 8 * Impl.Dsa.Arm.ProbablePrime.words bits ∧ 8 * Impl.Dsa.Arm.ProbablePrime.words bits ≤ 512 ∧
      Impl.Dsa.Arm.ProbablePrime.len bits ≤ 384 ∧
      keyWords bits = Spec.Rsa.scratchWords (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ∧
      Impl.Dsa.Arm.ProbablePrime.checks bits = Spec.Dsa.primeChecks bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

theorem below_eq (h : 144 ≤ s.sp.toNat) {a : Nat} (ha : a ≤ 144) :
    State.addr (s.sp - BitVec.ofNat 32 a) = fB s + BitVec.ofNat 64 (144 - a) := by
  rw [addr_sub' (by omega_using [h, ha])]; exact Offset.sub_ofNat_eq _ ha

theorem spP (h : CIn bits s) : State.addr (mkP bits s).sp = fB s + BitVec.ofNat 64 56 :=
  below_eq h.spLo (a := 88) (by decide)

theorem aA_eq (h : CIn bits s) : aA s = fB s + BitVec.ofNat 64 112 := below_eq h.spLo (a := 32) (by decide)

theorem pushed_sp (o : PreOut bits s t) : (pcPushed t).sp = (mkP bits s).sp := by
  show t.sp - BitVec.ofNat 32 56 = s.sp - BitVec.ofNat 32 88
  rw [o.rest.sp]; show s.sp - BitVec.ofNat 32 32 - BitVec.ofNat 32 56 = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem cF_sub {d n : Nat} (hd : d + n ≤ 144) :
    Region.Sub ⟨fB s + BitVec.ofNat 64 d, n⟩ (cF s) := Offset.sub_base _ hd

/-- Memory after `pre` and the push: changed only in `cF`. -/
theorem tFrame (h : CIn bits s) (o : PreOut bits s t) : Frame [cF s] s.mem (pcPushed t).mem := by
  have f := pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := t) (by
      rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
      rw [sub_toNat' (by have := h.spLo; omega_using [this])]; have := h.spLo; omega_using [this])
  have e : belowA t.sp (4 * 14) = ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
    show (⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h]
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  have a := o.frame
  rw [aA_eq h] at a
  exact (a.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩).trans
    (f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩)

theorem bytesT (h : CIn bits s) (o : PreOut bits s t) {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (pcPushed t).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame (tFrame h o) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

/-- The allocation's words after the push. -/
theorem allocW (h : CIn bits s) (o : PreOut bits s t) {k : Nat} {v : BitVec 32} (hk : (k, v) ∈ allocVals bits s) :
    fw (pcPushed t).mem (mkP bits s) (56 + k) = v := by
  have hk' : k + 4 ≤ 32 := by
    simp only [allocVals, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
    rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have ea : off (State.addr (mkP bits s).sp) (56 + k) = aA s + BitVec.ofNat 64 k := by
    show State.addr (mkP bits s).sp + BitVec.ofNat 64 (56 + k) = _
    rw [spP h, aA_eq h, Offset.add_add, Offset.add_add, show 56 + (56 + k) = 112 + k by omega_using []]
  have f := pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := t) (by
      rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
      rw [sub_toNat' (by have := h.spLo; omega_using [this])]; have := h.spLo; omega_using [this])
  have e : belowA t.sp (4 * [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length) =
      ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
    show (⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h]
  rw [e] at f
  show (pcPushed t).mem.readW (off (State.addr (mkP bits s).sp) (56 + k)) 32 = v
  have fr := f.readW (r := ⟨aA s + BitVec.ofNat 64 k, 4⟩) (a := aA s + BitVec.ofNat 64 k) (w := 32)
    (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [aA_eq h, Offset.add_add]
    exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hk']) (by decide)) (by decide)
  rw [ea]
  exact fr.trans (o.vals (k, v) hk)


end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # DSA's probable-prime test on ARMv7: the body's start (`in_c`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Impl.RsaKeyGen.Arm.Candidate (aoR aoRl aoP aoS aoSl aoEl aoPl foL foUsed)

section
variable {bits : Nat} {s t : State}

theorem rS_eq (h : CIn bits s) :
    (mkP bits s).rS = ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 keyOff, keyWords bits * 8⟩ := by
  have := h.fw; have := h.size
  have : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  show (⟨State.addr (s.gpr .r0 + BitVec.ofNat 32 keyOff), keyWords bits * 8⟩ : Region) = _
  rw [addr_add (by simp only [keyOff] at *; omega_arith)]

theorem rC_eq (h : CIn bits s) : (mkP bits s).rC = ⟨fB s + BitVec.ofNat 64 0, 56⟩ := by
  show (⟨State.addr (s.sp - BitVec.ofNat 32 88 - BitVec.ofNat 32 56), 56⟩ : Region) = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, below_eq h.spLo (a := 88 + 56) (by decide)]

theorem rF_eq (h : CIn bits s) : (mkP bits s).rF = ⟨fB s + BitVec.ofNat 64 56, 88⟩ := by
  show (⟨State.addr (mkP bits s).sp, 88⟩ : Region) = _; rw [spP h]

theorem rFr_eq (h : CIn bits s) : (mkP bits s).rFr = ⟨fB s + BitVec.ofNat 64 56, 56⟩ := by
  show (⟨State.addr (mkP bits s).sp, 56⟩ : Region) = _; rw [spP h]

/-- The body's start. -/
theorem in_c (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) : In (mkP bits s) (sx bits s t) := by
  have spLo := h.spLo; have spHi := h.spHi; have fw := h.fw; have size := h.size
  obtain ⟨k1, k2, hlen, hkw, hchk⟩ := hb.facts
  simp only [keyOff] at size
  have kpos : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  have hL : (mkP bits s).len = Impl.Dsa.Arm.ProbablePrime.len bits := rfl
  have spN : (mkP bits s).sp.toNat = s.sp.toNat - 88 := sub_toNat' (by omega_arith)
  have subS : Region.Sub (mkP bits s).rS (cW s) := by
    rw [rS_eq h]; exact Offset.sub_base _ (by simp only [keyOff]; omega_arith)
  have subCd : Region.Sub (mkP bits s).rCd (cW s) := Region.sub_prefix (by
    show Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith)
  have subF : Region.Sub (mkP bits s).rF (cF s) := by rw [rF_eq h]; exact cF_sub (by decide)
  have subFr : Region.Sub (mkP bits s).rFr (cF s) := by rw [rFr_eq h]; exact cF_sub (by decide)
  have subC : Region.Sub (mkP bits s).rC (cF s) := by rw [rC_eq h]; exact cF_sub (by decide)
  have rdm : ∀ r ∈ cCd bits s :: s.rd, r ∈ (sx bits s t).rd ++ (sx bits s t).wr := fun r hr =>
    List.mem_append_left _ hr
  have M : (sx bits s t).mem = (pcPushed t).mem := rfl
  have tsp : t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp := pushed_sp o
  have saved := pc_push_saved t (by
    rw [o.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
    rw [sub_toNat' (by omega_arith)]; omega_arith)
  rw [show (t.sp - 56 : BitVec 32) = (mkP bits s).sp from tsp] at saved
  have bCd := bytesT h o (R := (mkP bits s).rCd) (h.FW.sub_right subCd) (by
    show Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith)
  have bR := bytesT h o (R := cR s) h.FR (by have := h.fr; show (s.gpr .r3).toNat ≤ _; omega_arith)
  have hcv : cv (mkP bits s) (sx bits s t) =
      Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) := by
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt (pcPushed t).mem (mkP bits s).rCd.base (mkP bits s).rCd.len) = _
    rw [bCd]
    show _ = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 0) (bits / 8))
    rw [BitVec.add_zero]; rfl
  refine ⟨pushed_sp o, by omega_arith, by omega_arith, rfl, ⟨cR s, rdm _ (List.mem_cons_of_mem _ (by rw [h.rd]; exact List.mem_cons_self)), Region.contains_self _ _⟩,
    ⟨cCd bits s, rdm _ List.mem_cons_self, Region.contains_self _ _⟩,
    ⟨(mkP bits s).rAl, List.mem_append_right _ (by simp [xRegs]), ?_⟩, hb, rfl, k1, k2, Nat.mul_mod_right _ _,
    by show Spec.Rsa.scratchWords (8 * Impl.Dsa.Arm.ProbablePrime.words bits) ≤ keyWords bits; rw [hkw], h.fu, h.fr, by show (s.gpr .r0).toNat + Impl.Dsa.Arm.ProbablePrime.len bits ≤ _; omega_arith,
    BitVec.isLt _, ?_,
    h.wU.sub_left subS, h.wR.sub_left subS, ?_, (h.FW.symm.sub_left subS).sub_right subF,
    (h.FW.symm.sub_left subS).sub_right subC, h.rU.symm, h.wU.symm.sub_right subCd, h.FU.symm.sub_right subF,
    h.FU.symm.sub_right subC, h.FR.symm.sub_right subFr, h.FR.symm.sub_right subC,
    (h.FW.symm.sub_left subCd).sub_right subFr, (h.FW.symm.sub_left subCd).sub_right subC,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hcv]; exact h.odd, by rw [hcv]; exact h.bl, hcv, bR⟩
  · show (⟨State.addr ((mkP bits s).sp + BitVec.ofNat 32 56), 32⟩ : Region).Contains
      (State.addr (mkP bits s).sp + BitVec.ofNat 64 56) 32
    rw [addr_add (by omega_arith)]; exact Region.contains_self _ _
  · show (s.gpr .r0 + BitVec.ofNat 32 keyOff).toNat + keyWords bits * 8 ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := keyOff) (by simp only [keyOff]; omega_arith),
      Nat.mod_eq_of_lt (by simp only [keyOff]; omega_arith)]
    simp only [keyOff]; omega_arith
  · rw [rS_eq h]; exact Offset.disjoint_base _ (by simp only [keyOff]; omega_arith) (by simp only [keyOff]; omega_arith)
  · show (pcPushed t).mem.readW (State.addr (mkP bits s).sp + BitVec.ofNat 64 4) 32 = _
    rw [saved (.r1, 4) (by simp [pcAllSaved]), o.r1]; rfl
  · show (pcPushed t).mem.readW (State.addr (mkP bits s).sp + BitVec.ofNat 64 8) 32 = _
    rw [saved (.r2, 8) (by simp [pcAllSaved]), o.r2]; rfl
  · exact allocW h o (k := 4) (v := s.gpr .r0) (by simp [allocVals])
  · exact allocW h o (k := 0) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.len bits)) (by simp [allocVals])
  · exact allocW h o (k := 8) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.draw bits)) (by simp [allocVals])
  · show _ = BitVec.ofNat 32 (Spec.Dsa.primeChecks bits)
    rw [← hchk]
    exact allocW h o (k := 28) (v := BitVec.ofNat 32 (Impl.Dsa.Arm.ProbablePrime.checks bits)) (by simp [allocVals])
  · exact allocW h o (k := 12) (v := s.gpr .r2) (by simp [allocVals])
  · show _ = BitVec.ofNat 32 (s.gpr .r3).toNat
    rw [show BitVec.ofNat 32 (s.gpr .r3).toNat = s.gpr .r3 by simp]
    exact allocW h o (k := 16) (v := s.gpr .r3) (by simp [allocVals])
  · exact allocW h o (k := 20) (v := s.gpr .r0 + BitVec.ofNat 32 keyOff) (by simp [allocVals])
  · exact allocW h o (k := 24) (v := BitVec.ofNat 32 (keyWords bits)) (by simp [allocVals])

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # DSA's probable-prime test on ARMv7: a call's result (`prime_ok`)

The allocation, `pre`, the push, the body (run with the regions `xRegs` and
the candidate, and widened to the caller's), the restore, the pop and the
release.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)

/-- The test's result, from the caller's memory. -/
def resC (bits : Nat) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)))
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- A call's result. -/
def CPost (bits : Nat) (s t : State) : Prop :=
  (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (resC bits s) ∧
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem t.mem ∧
    ∀ b rest, resC bits s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (State.addr (stackArg s 0)) 1 = [BitVec.ofNat 64 ((s.gpr .r3).toNat - rest.length)]

section
variable {bits : Nat} {s t : State}

theorem res_c {σ : State} (pre : In (mkP bits s) σ) : res (mkP bits s) σ = resC bits s := by
  unfold res resC; rw [pre.cand, pre.rnd]; rfl

/-- The body's regions are among the caller's, the allocation's and the frame's. -/
theorem xCovers (h : CIn bits s) (o : PreOut bits s t) :
    Covers (xRegs (mkP bits s)) (pcPushed t).wr := by
  have spLo := h.spLo; have fw := h.fw; have size := h.size
  have kpos : 0 < keyWords bits := by simp [keyWords, Spec.Rsa.scratchWords]
  have wT : (pcPushed t).wr = (mkP bits s).rFr :: ⟨fB s + BitVec.ofNat 64 112, 32⟩ :: [cW s, cU s] := by
    show ⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ :: t.wr = _
    rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, o.rest.wr]
    show _ :: ⟨aA s, 32⟩ :: s.wr = _
    rw [aA_eq h, h.wr]
  have eAl : (mkP bits s).rAl = ⟨fB s + BitVec.ofNat 64 112, 32⟩ := by
    show (⟨State.addr ((mkP bits s).sp + BitVec.ofNat 32 56), 32⟩ : Region) = _
    rw [addr_add (by show (s.sp - BitVec.ofNat 32 88).toNat + 56 < _; rw [sub_toNat' (by omega_using [spLo])]; have := h.spHi; omega_using []),
      spP h, Offset.add_add]
  have hkw : keyWords bits = 16 * (8 * Impl.Dsa.Arm.ProbablePrime.words bits) + 32 := rfl
  have hw : (mkP bits s).w = Impl.Dsa.Arm.ProbablePrime.words bits := by
    show 8 * Impl.Dsa.Arm.ProbablePrime.words bits / 8 = _; omega_using []
  have hoM : (mkP bits s).oM = 8 * (21 * Impl.Dsa.Arm.ProbablePrime.words bits + 30) := by
    show 8 * (21 * (mkP bits s).w + 30) = _; rw [hw]
  have hlM : (mkP bits s).lenM = 8 * Impl.Dsa.Arm.ProbablePrime.words bits + 48 := by
    show 8 * (mkP bits s).w + 48 = _; rw [hw]
  have w4 : 4 ≤ Impl.Dsa.Arm.ProbablePrime.words bits := Nat.le_max_left _ _
  simp only [keyOff] at size ⊢
  rw [wT]
  refine Covers.of_forall fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [eAl]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · refine Covers.of_sub fun r hr => ⟨cW s, by simp, 384, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; rw [rS_eq h]; rfl
    · simp only [List.mem_singleton] at hr; subst hr
      show 384 + keyWords bits * 8 ≤ (s.gpr .r1).toNat * 8; omega_using [size]
  · refine Covers.of_sub fun r hr => ⟨cW s, by simp, 384 + (mkP bits s).oM, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      show State.addr (s.gpr .r0 + BitVec.ofNat 32 keyOff + BitVec.ofNat 32 (mkP bits s).oM) = _
      rw [Offset.add_add, addr_add (by simp only [keyOff]; rw [hoM]; omega_using [fw, size, hkw])]; rfl
    · simp only [List.mem_singleton] at hr; subst hr
      show 384 + (mkP bits s).oM + 8 * (mkP bits s).lenM ≤ (s.gpr .r1).toNat * 8
      rw [hoM, hlM]; omega_using [size, hkw, w4]

theorem rdT (o : PreOut bits s t) : (pcPushed t).rd = s.rd := o.rest.rd

/-- Every region the body may access, the caller's. -/
theorem allCovers (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) :
    Covers ((sx bits s t).rd ++ (sx bits s t).wr) (s.rd ++ (pcPushed t).wr) := by
  have := h.size; have hl := hb.facts.2.2.1
  simp only [keyOff] at this
  refine Covers.cons ?_ (Covers.append (Covers.refl _) (xCovers h o))
  refine Covers.right (Covers.of_sub fun r hr => ⟨cW s, ?_, 0, ?_, ?_⟩)
  · show cW s ∈ (pcPushed t).wr
    rw [show (pcPushed t).wr = _ :: t.wr from rfl, o.rest.wr]
    show cW s ∈ _ :: ⟨aA s, 32⟩ :: s.wr
    rw [h.wr]; simp
  · simp only [List.mem_singleton] at hr; subst hr; exact (BitVec.add_zero _).symm
  · simp only [List.mem_singleton] at hr; subst hr
    show 0 + Impl.Dsa.Arm.ProbablePrime.len bits ≤ (s.gpr .r1).toNat * 8; omega_using [this, hl]

/-- The body's run, widened to the caller's regions. -/
theorem body_wide (v : RoundImpl) (hb : Bits bits) (h : CIn bits s) (o : PreOut bits s t) :
    ∃ tr w, Exec isa (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (sx bits s t) tr w ∧
      Exec isa (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (pcPushed t) tr
        (w.withRegions s.rd (pcPushed t).wr) ∧
      RF (mkP bits s) (In (mkP bits s)) (statD (mkP bits s)) (usedD (mkP bits s)) (sx bits s t) w := by
  have pre := in_c hb h o
  obtain ⟨tr, w, e, rf⟩ := (body_vp v (P := mkP bits s) (E := In (mkP bits s)) fun _ e => e).wp _ _
    ⟨pre, ⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  have run := Exec.widen (rd := s.rd) (wr := (pcPushed t).wr) e (allCovers hb h o) (xCovers h o)
  rw [State.withRegions_withRegions, ← rdT o, State.withRegions_self] at run
  exact ⟨tr, w, e, by rw [← rdT o]; exact run, rf⟩

theorem subC (h : CIn bits s) : Region.Sub (mkP bits s).rC (cF s) := by rw [rC_eq h]; exact cF_sub (by decide)

theorem subW0 (h : CIn bits s) : Region.Sub (mkP bits s).rW0 (cF s) := by
  show Region.Sub ⟨State.addr (mkP bits s).sp, 4⟩ _; rw [spP h]; exact cF_sub (by decide)

/-- The candidate's bytes are outside the key working space, the stack and `used`. -/
theorem keeps (h : CIn bits s) (o : PreOut bits s t) {w : State}
    (bk : Bk (mkP bits s) (sx bits s t) w) :
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem w.mem := by
  have fw := h.fw
  intro i hi hr
  have hr' := hr _ List.mem_cons_self
  simp only at hr'
  have inW : (cW s).Contains (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) 1 := by
    simpa using Offset.contains_base (State.addr (s.gpr .r0)) (d := i) (n := 1) (k := (s.gpr .r1).toNat * 8)
      (by omega_using [hi]) (by omega_using [hi])
  have own : (⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 i, 1⟩ : Region).Contains
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) 1 := Region.contains_self _ _
  have pre := bk.pre
  refine (bk.frame _ fun r hr hc => ?_).trans (tFrame h o _ fun r hr hc => ?_)
  · simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [rS_eq h] at hc
      have := h.size; simp only [keyOff] at this hr' ⊢
      exact Offset.disjoint (State.addr (s.gpr .r0)) (d := i) (n := 1) (e := 384) (k := keyWords bits * 8)
        (by omega_using [hr']) (by omega_using [hi]) (by omega_using [this]) _ own hc
    · exact h.wU _ inW hc
    · exact h.FW _ (subC h _ hc) inW
    · exact h.FW _ (subW0 h _ hc) inW
  · simp only [List.mem_singleton] at hr; subst hr; exact h.FW _ hc inW

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Top6`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7: a call's result (`prime_ok`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat} {s : State}

/-- A call's result. -/
theorem prime_ok (v : RoundImpl) (h : CIn bits s) :
    WP isa (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) s fun t => abiPreserved s t ∧ CPost bits s t := by
  have hb := h.sized
  have spLo := h.spLo; have spHi := h.spHi
  unfold Impl.Dsa.Arm.ProbablePrime.code
  refine WP.alloc (by decide) (by omega_using [spLo]) ?_
  rw [WP.seq_iff]
  refine WP.mono (pre_ok hb spLo spHi h.argsIn h.arg) fun t ⟨rest, fr, vals, r1, r2⟩ => ?_
  have o : PreOut bits s t := ⟨rest, fr, vals, r1, r2⟩
  have tspN : t.sp.toNat = s.sp.toNat - 32 := by
    rw [rest.sp]; exact sub_toNat' (by omega_using [spLo])
  refine WP.frame (by decide) (by simp only [List.length_cons, List.length_nil]; omega_using [spLo, tspN]) (by decide) ?_
  rw [WP.seq_iff]
  obtain ⟨tr, w, -, run', ⟨-, bk, r0, used⟩⟩ := body_wide v hb h o
  refine WP.mono (Q := fun x => x = w.withRegions s.rd (pcPushed t).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have pre := bk.pre
  have wsp : w.sp = (mkP bits s).sp := bk.sp.trans pre.sp
  have spN : (mkP bits s).sp.toNat = s.sp.toNat - 88 := sub_toNat' (by omega_using [spLo])
  have sv := pc_push_callee_saved t (by omega_using [spLo, tspN])
  rw [show (t.sp - 56 : BitVec 32) = (mkP bits s).sp from pushed_sp o] at sv
  have saved : Spill.Saved w.mem (State.addr (mkP bits s).sp) t.gpr pcCalleeSaved := fun p hp => by
    have ho : FwOk p.2 := by revert hp; revert p; decide
    exact (bk.frame.readW (r := ⟨State.addr (mkP bits s).sp + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
      (pre.fwSep ho) (by decide)).trans (sv p hp)
  have fit : (w.withRegions s.rd (pcPushed t).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show w.sp.toNat + 56 ≤ _; rw [wsp, spN]; omega_using []
  have read : InRegions ((w.withRegions s.rd (pcPushed t).wr).rd ++ (w.withRegions s.rd (pcPushed t).wr).wr)
      (State.addr (w.withRegions s.rd (pcPushed t).wr).sp) 56 := by
    refine ⟨⟨State.addr (mkP bits s).sp, 56⟩, List.mem_append_right _ ?_, ?_⟩
    · show _ ∈ ⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ :: t.wr
      rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o]; exact List.mem_cons_self
    · rw [State.withRegions_sp, wsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ t.gpr fit read (by rw [State.withRegions_sp, wsp]; exact saved)) ?_
  rintro t' ⟨restored, memT, restT⟩ m₁ u₁ h₁ m₂ u₂ h₂
  have rc := res_c pre
  have m' : t'.mem = w.mem := memT
  change Frame [⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩] t'.mem m₁ at h₁
  rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h] at h₁
  change Frame [⟨aA s, 32⟩] m₁ m₂ at h₂
  rw [aA_eq h] at h₂
  have lostF : Frame [cF s] t'.mem m₂ :=
    (h₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩).trans
    (h₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩)
  have usedL : Spec.Rsa.wordsAt m₂ (State.addr (stackArg s 0)) 1 = Spec.Rsa.wordsAt t'.mem (State.addr (stackArg s 0)) 1 :=
    Proof.Rsa.wordsAt_frame lostF (by decide) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.FU.symm
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, fun b rst hr => ?_⟩
  · have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    show (popped .r12 56 t').gpr r = _
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (restored (.r4, 16) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r5, 20) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r6, 24) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r7, 28) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r8, 32) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r9, 36) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r10, 40) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r11, 44) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.lr, 52) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
  · show t'.sp + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [restT.sp, State.withRegions_sp, wsp]
    show s.sp - BitVec.ofNat 32 88 + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.sub_add_cancel]
  · show ((popped .r12 56 t').gpr .r0).toNat = _
    rw [popped_gpr (by decide), restT.gpr .r0 (by simp [pcCalleeSaved]), State.withRegions_gpr, r0]
    unfold statD; rw [rc]
  · show Proof.Dsa.ModPow.Keeps _ _ _ s.mem m₂
    have k := keeps h o bk
    rw [← m'] at k
    intro i hi hr
    exact (lost_byte lostF (R := cW s) h.FW.symm (by change i < (s.gpr .r1).toNat * 8; omega_using [hi])).trans
      (k i hi hr)
  · show Spec.Rsa.wordsAt m₂ _ 1 = _
    rw [usedL, m']
    refine used.trans ?_
    unfold usedD; rw [rc, hr]; rfl

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Top7`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7: constant time (`prime_ct`)

Two calls with the same public parameters `mkP` leak the same: the
allocation and `pre`'s addresses are on the stack, the push's and the pop's
too, the body's are the stage's (`body_vp`), and the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat}

/-- `pre`'s addresses are `r12`'s offsets, which it keeps. -/
theorem pre_ct :
    RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Dsa.Arm.ProbablePrime.pre) (fun s t => s.sp = t.sp) := by
  unfold Impl.Dsa.Arm.ProbablePrime.pre Impl.Dsa.Arm.ProbablePrime.wordsOf Impl.Dsa.Arm.ProbablePrime.bitsOf
  simp only [List.cons_append, List.nil_append]
  apply VG.Proof.Rsa.Arm.setupBlock_ct
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro i hi s t h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addrs, h2]

theorem alloc_push {s : State} (h : 32 ≤ s.sp.toNat) : isa.push (.alloc 32) s = some (allocated 32 s) := by
  simp only [isa, push, show (0 : Nat) < 32 ∧ 32 < 4096 ∧ 32 % 8 = 0 ∧ encodable (BitVec.ofNat 32 32) = true from
    by decide, h, and_self, ite_true]
  rfl

/-- The states after `pre`, for two calls. -/
def AfterPre (bits : Nat) (a b : State) : Prop :=
  ∃ s t, (CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t) ∧ PreOut bits s a ∧ PreOut bits t b

theorem pre_out {s u : State} {tr : List Leak} (h : CIn bits s)
    (e : Exec isa (.block Impl.Dsa.Arm.ProbablePrime.pre) (allocated 32 s) tr u) : PreOut bits s u := by
  obtain ⟨tr', u', e', rest, fr, vals, r1, r2⟩ := pre_ok h.sized h.spLo h.spHi h.argsIn h.arg
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨rest, fr, vals, r1, r2⟩

/-- The frame's body, for two calls. -/
theorem inner_ct (v : RoundImpl) :
    RelCT isa (fun a' b' => ∃ a b, AfterPre bits a b ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) a = some a' ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) b = some b')
      (.seq (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (.block VG.Impl.Bignum.Arm.PcFn.restore)) (fun _ _ => True) := by
  intro a' b' tr1 tr2 u w hp e1 e2
  obtain ⟨a, b, ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩, pa, pb⟩ := hp
  have f1 : 56 ≤ a.sp.toNat := by rw [o1.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := hs.spLo; omega_using [this])]; have := hs.spLo; omega_using [this]
  have f2 : 56 ≤ b.sp.toNat := by rw [o2.rest.sp]; show 56 ≤ (t.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := ht.spLo; omega_using [this])]; have := ht.spLo; omega_using [this]
  have ea : pcPushed a = a' := Option.some.inj ((push_pushed (by decide) (by simpa using f1)).symm.trans pa)
  have eb : pcPushed b = b' := Option.some.inj ((push_pushed (by decide) (by simpa using f2)).symm.trans pb)
  subst a'; subst b'
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨n1, w1, en1, run1, ⟨-, bk1, -⟩⟩ := body_wide v hs.sized hs o1
      obtain ⟨n2, w2, en2, run2, ⟨-, bk2, -⟩⟩ := body_wide v hs.sized ht o2
      obtain ⟨rfl, rfl⟩ := Exec.det body1 run1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 run2
      have pre1 := in_c hs.sized hs o1
      have pre2 := in_c hs.sized ht o2
      have bx1 : Bk (mkP bits s) (sx bits s a) (sx bits s a) := ⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩
      have bx2 : Bk (mkP bits t) (sx bits t b) (sx bits t b) := ⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩
      have sp1 := bk1.sp.trans pre1.sp
      have sp2 := bk2.sp.trans pre2.sp
      rw [← hP] at pre2 bx2 sp2
      have trB := ((body_vp v (P := mkP bits s) (E := In (mkP bits s)) fun _ e => e).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, bx1⟩, ⟨pre2, bx2⟩⟩ en1 en2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [sp1, sp2]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

/-- Two calls with the same public parameters. -/
theorem prime_ct (v : RoundImpl) :
    RelCT isa (fun s t => CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t)
      (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) (fun _ _ => True) := by
  unfold Impl.Dsa.Arm.ProbablePrime.code
  apply VG.Proof.Rsa.Arm.allocation_ct
  intro a b tr1 tr2 u w hp e1 e2
  obtain ⟨s, t, ⟨hs, ht, sp, hP⟩, pa, pb⟩ := hp
  have ea : allocated 32 s = a := Option.some.inj ((alloc_push (by have := hs.spLo; omega_using [this])).symm.trans pa)
  have eb : allocated 32 t = b := Option.some.inj ((alloc_push (by have := ht.spLo; omega_using [this])).symm.trans pb)
  subst a; subst b
  cases e1 with
  | seq pre1 fr1 =>
    cases e2 with
    | seq pre2 fr2 =>
      have trP := (pre_ct _ _ _ _ _ _ (show (allocated 32 s).sp = (allocated 32 t).sp by
        show s.sp - _ = t.sp - _; rw [sp]) pre1 pre2).1
      have o1 := pre_out hs pre1
      have o2 := pre_out ht pre2
      have trF := (RelCT.frame (P := AfterPre bits) (fun x y ⟨s, t, ⟨_, _, sp, _⟩, o1, o2⟩ => by
          rw [o1.rest.sp, o2.rest.sp]; show s.sp - _ = t.sp - _; rw [sp])
        (fun a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2 => inner_ct v a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2)
        _ _ _ _ u w ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩ fr1 fr2).1
      exact ⟨by rw [trP, trF], trivial⟩

end

end VG.Proof.Dsa.Arm.Prime

end

end


/-! # `vg_dsa_probable_prime` on ARMv7 is verified against the shared contract

For every size of `sizes` (`Bits`), the second stack argument, and any
implementation of the Miller–Rabin round it calls (`RoundImpl`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (code layout keyOff keyWords)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem prime_contract_correct (v : RoundImpl) (s : State) (h : primeK.pre s) :
    ∃ tr t, Exec isa (code v.name v.code) s tr t ∧ abiPreserved s t ∧ primeK.post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, keeps, used⟩ := prime_ok v hc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨r0, keeps, used⟩

section
variable {bits : Nat}

/-- Calls with the same public arguments and leak have the same public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) (a0 : stackArg s 0 = stackArg t 0)
    (hc : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) =
      Proof.Dsa.ProbablePrime.candidateAt (layout bits) t.mem (State.addr (t.gpr .r0)))
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    mkP bits s = mkP bits t := by
  unfold mkP; rw [hc, hr, sp, p0, p2, p3, a0]

end

theorem prime_contract_ct (v : RoundImpl) : ConstantTime isa primeK.pre primeK.pub (code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, leak, p0, -, p2, p3, a0, a1⟩ := hp
  rw [← a1] at leak
  obtain ⟨-, leak⟩ := List.cons.inj leak
  obtain ⟨hc, hl⟩ := List.cons.inj leak
  have hr := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  rw [← a1] at it
  exact (prime_ct v s t tr1 tr2 u w ⟨is, it, sp, mkP_eq sp p0 p2 p3 a0 hc hr⟩ e1 e2).1

/-- A state satisfying the contract: the candidate of 160 ones at `0x1000`, in a working space of
6224 words, no `rand`, `used` at 0, and the stack at `0x80000`, its second word the size 160. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 6224 | .r2 => 0x20000 | .r3 => 0 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a.toNat < 0x10000 ∧ 0x1000 ≤ a.toNat then 0xFF else if a = 0x80004 then 160 else 0
  rd := [⟨0x20000, 0⟩, ⟨0x80000, 8⟩]
  wr := [⟨0x1000, 49792⟩, ⟨0, 8⟩]

theorem prime_contract_sat : ∃ s, primeK.pre s := by
  refine ⟨satState, ?_⟩
  have ha : stackArg satState 1 = 160 := by decide
  sig_pre [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val]
  rw [ha]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide

theorem prime_verified (v : RoundImpl) : Verified target (code v.name v.code) primeK :=
  ⟨prime_contract_correct v, prime_contract_ct v, prime_contract_sat⟩

end VG.Proof.Dsa.Arm.Prime

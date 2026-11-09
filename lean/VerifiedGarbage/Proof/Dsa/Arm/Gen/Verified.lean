module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Body
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.ReadHalves
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

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

theorem code_ok (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) {s : State}
    (hs : (Spec.Dsa.parameterSearchContract abi 304).pre s) :
    WP isa (code g1 g2 g3) s fun t => abiPreserved s t ∧ (Spec.Dsa.parameterSearchContract abi 304).post s t := by
  have hpre := cin_of_pre s hs
  have spLo := hpre.spLo
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by simp only [F]; omega)
    (WP.mono ((body_vp (G := mkG s) K1 K2 K3).wp s _ ⟨rfl, hpre, rfl⟩) fun u hu => ?_)
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
    have := hpre.valid; simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this; omega
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
        have := ok.2; simp only [Spec.Dsa.parameterSeeds] at this; omega
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
    omega
  have hi : ∀ {a : Addr} {n : Nat}, s.mem.readW a 64 = BitVec.ofNat 64 n → n < 2 ^ 32 →
      s.mem.readW (a + BitVec.ofNat 64 4) 32 = 0 := fun {a n} h hn => by
    rw [Mem.readW_hi32 h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow,
      show (0 : BitVec 32).toNat = 0 from rfl]
    omega
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
    rw [r0, fo.r0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [m]; exact fo.out.trans (outBytes_eq _ _)
  · rw [m]
    show [v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [VG.Proof.RsaKeyGen.Arm.pair_word]
    have e0 : slot v.mem (State.addr (s.gpr .r2)) (2 * 0) = BitVec.ofNat 32 (cRes (mkG s) o).used := fo.u0
    have e1 : slot v.mem (State.addr (s.gpr .r2)) (2 * 0 + 1) = 0#32 := fo.u1
    rw [e0, e1, VG.Proof.RsaKeyGen.Arm.pair_ofNat hU]
  · rw [m]
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
  have hsp : F ≤ s.sp.toNat := by have := h.spLo; simp only [F]; omega
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

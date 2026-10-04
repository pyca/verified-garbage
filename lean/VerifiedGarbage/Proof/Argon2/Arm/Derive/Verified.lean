import VerifiedGarbage.Proof.Argon2.Arm.Derive.BodyCT

/-!
# Argon2 on ARMv7: the derivation is verified

`derive_verified`: the derivation against `deriveArm` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, through `deriveFlat`, whose
precondition spells `DPre` out as `Sig.contract` lays the regions out.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Argon2.Arm (stkR)

/-! ## A state satisfying the precondition -/

/-- The stack arguments: Argon2d, empty inputs, one pass over 8 KiB in one
lane, a 4-byte tag (the register arguments are zero). -/
def satStack : List Nat := [0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satStack` at `0x40000`. -/
def satMem (a : Addr) : Byte :=
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40038 then
    ((BitVec.ofNat 32 (satStack[(a.toNat - 0x40000) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40000) % 4))).setWidth 8
  else 0

def satState : State where
  gpr _ := 0
  sp := 0x40000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 56⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

/-- The arguments of `satState`. -/
def satArgs : List Nat := [0, 0, 0, 0] ++ satStack

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
  have e : stackArgAddr satState 0 = 0x40000 := by decide
  have sp : satState.sp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, stkR0, stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, sp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified Arm.target Impl.Argon2.Arm.Derive.derive deriveArm :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## The shared contract -/

/-- `deriveArm`, its precondition spelt out as `Sig.contract` lays the regions
out. -/
def deriveFlat : Contract Arm.isa :=
  { deriveArm with
    pre := fun s =>
      let pw : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
      let salt : Region := ⟨State.addr (arg s 3), (arg s 4).toNat⟩
      let sec : Region := ⟨State.addr (arg s 9), (arg s 10).toNat⟩
      let ad : Region := ⟨State.addr (arg s 11), (arg s 12).toNat⟩
      let mem : Region := ⟨State.addr (arg s 13), (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨State.addr (arg s 15), 16384⟩
      let out : Region := ⟨State.addr (arg s 16), (arg s 17).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 56⟩
      let stack : Region := stkR s.sp 240
      s.rd = [pw, salt, sec, ad, args] ∧ s.wr = [mem, scr, out] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32 ∧ 240 ≤ s.sp.toNat ∧ s.sp.toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg s 8).toNat ∧ (arg s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat).blocks }

theorem deriveFlat_pre {s : State} (h : deriveFlat.pre s) : DPre s := by
  obtain ⟨hrd, hwr, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  refine
    { rd := hrd
      wr := hwr
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      sp_lo := lo
      sp_hi := hi
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    exacts [d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [k₁, k₂, k₃, k₄, k₅, k₆, k₇]

theorem deriveFlat_implies : deriveArm.Implies deriveFlat :=
  ⟨fun _ h => deriveFlat_pre h, fun _ _ _ h => h, fun _ _ _ _ h => h,
    ⟨satState, by
      have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
      have e : stackArgAddr satState 0 = 0x40000 := by decide
      simp only [deriveFlat, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩⟩

theorem flat_implies : deriveFlat.Implies (Spec.Argon2.deriveContract Arm.abi 240) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveFlat, deriveArm, stkR, arg, prm, pwB,
    saltB, secB, adB, pwR, saltR, secR, adR, pwP, pwL, saltP, saltL, secP, secL, adP, adL, kindV, itersN, mcostN,
    lanesN, outL, outP,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, satMem, satStack, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using satState

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified Arm.target Impl.Argon2.Arm.Derive.derive (Spec.Argon2.deriveContract Arm.abi 240) :=
  (derive_verified.of_implies deriveFlat_implies).of_implies flat_implies

end VG.Proof.Argon2.Arm.Derive

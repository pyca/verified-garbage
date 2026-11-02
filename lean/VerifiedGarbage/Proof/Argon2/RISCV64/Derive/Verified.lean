module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Derive
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Contract
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.BodyCT
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Correct

/-!
# Argon2 on RISC-V: the derivation is verified

`derive_verified`: the derivation against `deriveRV` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, through `deriveFlat`, whose
precondition spells `DPre` out as `Sig.contract` lays the regions out, and
whose public data are the arguments one by one.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64

/-! ## A state satisfying the precondition -/

/-- The arguments on the stack: one thread, empty secret and associated data,
8 blocks at `0x10000`, scratch at `0x20000` and a 4-byte tag at `0x30000`
(the register arguments are Argon2d, an empty password and salt, one pass
over 8 KiB in one lane). -/
def satStack : List Nat := [1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satStack` at the stack pointer, `0x40000`, where the
first argument in memory is. -/
def satMem (a : Addr) : Byte :=
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40050 then
    ((BitVec.ofNat 64 (satStack[(a.toNat - 0x40000) / 8]?.getD 0)) >>> (8 * ((a.toNat - 0x40000) % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .a5 => 1 | .a6 => 8 | .a7 => 1 | _ => 0
  sp := 0x40000
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 80⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

/-- The arguments of `satState`. -/
def satArgs : List Nat := [0, 0, 0, 0, 0, 1, 8, 1] ++ satStack

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := sat_args
  have e : stackArgAddr satState 0 = 0x40000 := by decide
  have sp : satState.sp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, stkR0, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, kindV, itersN, mcostN, lanesN, threadsN, prm, arg32,
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

theorem derive_verified : Verified RISCV64.target Impl.Argon2.RISCV64.Derive.derive deriveRV :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## The shared contract -/

/-- `deriveRV`, its precondition spelt out as `Sig.contract` lays the
regions out, and its public data argument by argument. -/
def deriveFlat : Contract RISCV64.isa :=
  { deriveRV with
    pre := fun s =>
      let pw : Region := ⟨arg s 1, (arg s 2).toNat⟩
      let salt : Region := ⟨arg s 3, (arg s 4).toNat⟩
      let sec : Region := ⟨arg s 9, (arg s 10).toNat⟩
      let ad : Region := ⟨arg s 11, (arg s 12).toNat⟩
      let mem : Region := ⟨arg s 13, (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨arg s 15, 16384⟩
      let out : Region := ⟨arg s 16, (arg s 17).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 80⟩
      let stack : Region := below s.sp 320
      s.rd = [pw, salt, sec, ad, args] ∧ s.wr = [mem, scr, out] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 64 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 64 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 64 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 64 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 64 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 64 ∧ 320 ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 10 ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ (arg s 13).toNat % 8 = 0 ∧ (arg s 15).toNat % 8 = 0 ∧
      (arg32 s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg32 s 0).toNat (arg32 s 5).toNat (arg32 s 6).toNat
        (arg32 s 7).toNat (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg32 s 8).toNat ∧ (arg32 s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg32 s 0).toNat (arg32 s 5).toNat (arg32 s 6).toNat
        (arg32 s 7).toNat (arg s 17).toNat).blocks
    pub := fun s₁ s₂ =>
      (s₁.sp = s₂.sp ∧ Spec.Argon2.references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
        Spec.Argon2.references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)) ∧
      arg32 s₁ 0 = arg32 s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧
      arg s₁ 4 = arg s₂ 4 ∧ arg32 s₁ 5 = arg32 s₂ 5 ∧ arg32 s₁ 6 = arg32 s₂ 6 ∧
      arg32 s₁ 7 = arg32 s₂ 7 ∧ arg32 s₁ 8 = arg32 s₂ 8 ∧ arg s₁ 9 = arg s₂ 9 ∧
      arg s₁ 10 = arg s₂ 10 ∧ arg s₁ 11 = arg s₂ 11 ∧ arg s₁ 12 = arg s₂ 12 ∧ arg s₁ 13 = arg s₂ 13 ∧
      arg s₁ 14 = arg s₂ 14 ∧ arg s₁ 15 = arg s₂ 15 ∧ arg s₁ 16 = arg s₂ 16 ∧ arg s₁ 17 = arg s₂ 17 }

theorem deriveFlat_pre {s : State} (h : deriveFlat.pre s) : DPre s := by
  obtain ⟨hrd, hwr, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, sa, ma, ca, kd, vd, t₁, t₂, bl⟩ := h
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
      sp_al := sa
      mem_al := ma
      scr_al := ca
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

theorem argPub_int {s : State} {i : Nat} (h : i ∈ intArgs) : argPub s i = (arg32 s i).setWidth 64 :=
  ite_eq_left_iff.mpr fun n => absurd h n

theorem argPub_word {s : State} {i : Nat} (h : i ∉ intArgs) : argPub s i = arg s i :=
  ite_eq_right_iff.mpr fun n => absurd n h

theorem deriveFlat_pub {s₁ s₂ : State} (h : deriveFlat.pub s₁ s₂) : deriveRV.pub s₁ s₂ := by
  obtain ⟨⟨sp, refs⟩, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17⟩ := h
  refine ⟨⟨sp, fun i hi => ?_⟩, refs⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
    | rw [argPub_int (by decide), argPub_int (by decide)]; simp only [*]
    | rw [argPub_word (by decide), argPub_word (by decide)]; simp only [*]

theorem deriveFlat_implies : deriveRV.Implies deriveFlat :=
  ⟨fun _ h => deriveFlat_pre h, fun _ _ _ h => h, fun _ _ _ _ h => deriveFlat_pub h,
    ⟨satState, by
      have a : ∀ i < 18, arg satState i = BitVec.ofNat 64 (satArgs[i]?.getD 0) := sat_args
      have e : stackArgAddr satState 0 = 0x40000 := by decide
      simp only [deriveFlat, arg32, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide),
        a 4 (by decide), a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide),
        a 10 (by decide), a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide),
        a 15 (by decide), a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩⟩

theorem flat_implies : deriveFlat.Implies (Spec.Argon2.deriveContract RISCV64.abi 320) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveFlat, deriveRV, arg, arg32, prm, pwB,
    saltB, secB, adB, pwR, saltR, secR, adR, pwP, pwL, saltP, saltL, secP, secL, adP, adL, kindV, itersN, mcostN,
    lanesN, outL, outP, below, RISCV64.abi, RISCV64.argRegs, List.getD, List.range, List.range.loop]
    [satState, satMem, satStack, RISCV64.stackArg, RISCV64.stackArgAddr, Mem.readW, Mem.read,
      Spec.Argon2.params, Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]
    using satState

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified RISCV64.target Impl.Argon2.RISCV64.Derive.derive (Spec.Argon2.deriveContract RISCV64.abi 320) :=
  (derive_verified.of_implies deriveFlat_implies).of_implies flat_implies

end VG.Proof.Argon2.RISCV64.Derive

module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecFin
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.List.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT4
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `RsaPkcs1Enc.PPC64LE.DecCorrect`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: correctness

The frame's push, the setup, the private-key operation, `D`, `DH`, `KDK`,
`CL`, `AM`, the alternative length, the scan and the output, and the pop
(`code_correct`), to the outcome on the registers and the stack (`fnPost`,
`result_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.RsaPkcs1Enc (outByte)

variable {pc : Bool}

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg s'.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r7).toNat ((s'.gpr .r3).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (dOf s)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) (cOf s))

theorem rOf_setWidth (x : BitVec 64) : (rOf x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [rOf, BitVec.toNat_setWidth]
  omega_using []

theorem rOf_one (x : BitVec 64) : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = decide (x.setWidth 32 = 1) := by
  have : rOf x ^^^ BitVec.ofNat 64 1 = 0 ↔ x.setWidth 32 = 1 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [← rOf_setWidth, h]; rfl
    · intro h; simp only [rOf, h]; rfl
  simp only [this]

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (s : State) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) C
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)

/-- The outcome, from what the private-key operation gave and the end. -/
theorem result_ok {s : State} (h : DPre pc s) {x : BitVec 64} {mc : Mem} {t : State} {kd : List Byte}
    (hkd : kd = Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s))
    (hres : Spec.Rsa.writtenOutcome mc (s.gpr .r3) (s.gpr .r7).toNat (x.setWidth 32) (rsadpOf s (cOf s)))
    (hx : t.gpr .r3 = rOf x)
    (hout : ∀ i < (s.gpr .r7).toNat, t.mem (s.gpr .r3 + BitVec.ofNat 64 i) =
      outByte (vOfEM s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat)) (decide (rOf x ^^^ BitVec.ofNat 64 1 = 0))
        ((s.gpr .r7).toNat - lenOf s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) kd) i
        ((Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat).getD i 1) ((amOf s kd).getD i 0))
    (hml : t.mem.readW (s.gpr .r5) 64 =
      BitVec.ofNat 64 (lenOf s (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) kd) &&&
        bm (decide (rOf x ^^^ BitVec.ofNat 64 1 = 0)))
    (hAM : (amOf s kd).length = (s.gpr .r7).toNat) : fnPost s t := by
  have hk := h.k1
  unfold fnPost
  have hn : (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length = (s.gpr .r7).toNat :=
    Proof.Rsa.bytesAt_length' _ _ _
  have hC : (cOf s).length = (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length := by
    rw [hn]; exact Proof.Rsa.bytesAt_length' _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r7).toNat =
      (List.range (s.gpr .r7).toNat).map fun i => t.mem (s.gpr .r3 + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (s.gpr .r5) 1 = [t.mem.readW (s.gpr .r5) 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat).length (dOf s) (cOf s))
  cases hO : rsadpOf s (cOf s) with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = true := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega_using [hk]) hO]
    subst hb
    have hEMl := Proof.Rsa.bytesAt_length' mc (s.gpr .r3) (s.gpr .r7).toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega_using [hk]) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dOf s) (cOf s) (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat))
            (Spec.Rsa.bytesAt mc (s.gpr .r3) (s.gpr .r7).toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd)) (amOf s kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid hO]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega_using [hk]) hO]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem codeG_correct (s : State) (h : DPre pc s) (X : pc = true → PreX s) :
    WP isa (codeG pc) s fun t => abiPreserved s t ∧ fnPost s t := by
  have hk := h.k2
  unfold codeG
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega_using [this]) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (call_ok h X A fun t₂ A₂ => ?_)
  refine WP.seq (WP.mono (dBuild_ok h A₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (hashD_ok h h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (kdkMac_ok h h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (clLoop_ok h h₅.post h₅.kdk) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (amLoop_ok h h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (maskPart_ok h h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (alPart_ok h h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (scanPart_ok h h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.mono (selPart_ok h h₁₀ (rOf_lt _)) fun u hu mL _ fl => ?_
  have hAM : (amOf s (Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s))).length = (s.gpr .r7).toNat := by
    show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _
    rw [← h₇.am]; exact Proof.Rsa.bytesAt_length' _ _ _
  refine ⟨abiPreserved_lost ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [freed_gpr]; exact hu.hi r hr
  · rw [freed_sp, hu.sp]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact hu.lr
  · -- The `free` loses the frame's bytes, which lie apart from the outputs.
    have hfb : frameBytes ≤ stackBytes := by unfold stackBytes; omega_using []
    have hsub : Region.Sub ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (kR s) :=
      Offset.sub_below _ hfb (by omega_using [hfb])
    have hoR : (⟨s.gpr .r3, (s.gpr .r7).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
    refine result_ok h rfl ?_ hu.r3
      (fun i hi => (lost_byte fl (R := ⟨s.gpr .r3, (s.gpr .r7).toNat⟩)
        (by rw [hoR]; exact (h.ko.sub_left hsub).symm) hi).trans (hu.out i hi))
      ((fl.readW (r := mlR s) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (h.km.sub_left hsub).symm)
        (by decide)).trans hu.ml) hAM
    have e : rsadpOf s (cOf s) = Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .r7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) := rfl
    rw [e]
    exact A₂.out

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  codeG_correct s (dPre_of hpre) nofun

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

end

end


/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract's postcondition on the registers and
the stack (`dec_implies`); with correctness (`code_correct`) and constant
time (`code_ct`), `code` is verified for the stack its frame and
`vg_rsa_private_checked`'s use (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`,
one-byte exponents, primes, CRT exponents and `qInv`, and the stack
arguments at `0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000
    | .r9 => 1 | .r10 => 0x3100 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x10060 then 1 else if a = 0x10069 then 0x40 else if a = 0x10070 then 0x40
    else if a = 0x10079 then 0x41 else if a = 0x10080 then 1 else if a = 0x10089 then 0x42
    else if a = 0x10090 then 1 else if a = 0x10099 then 0x43 else if a = 0x100A0 then 1
    else if a = 0x100A9 then 0x44 else if a = 0x100B0 then 1 else if a = 0x100B9 then 0x45
    else if a = 0x100C0 then 1 else if a = 0x100CA then 0x02 else if a = 0x100D0 then 0x20
    else if a = 0x100D1 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x10060, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_implies : fnContract.Implies (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      fnPost, stackArgs_fifteen, List.append_eq, dOf, cOf]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, fnContract,
      stackArgs_fifteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_decrypt`. -/
theorem dec_verified : Verified target code (Spec.RsaPkcs1Enc.decryptContract abi stackBytes) :=
  Verified.of_correct code_correct code_ct dec_implies

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

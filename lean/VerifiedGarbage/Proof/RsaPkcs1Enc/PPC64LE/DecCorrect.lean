module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecFin
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  omega

theorem rOf_one (x : BitVec 64) : decide (rOf x ^^^ BitVec.ofNat 64 1 = 0) = decide (x.setWidth 32 = 1) := by
  have : rOf x ^^^ BitVec.ofNat 64 1 = 0 ↔ x.setWidth 32 = 1 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [← rOf_setWidth, h]; rfl
    · intro h; simp only [rOf, h]; rfl
  simp only [this]

theorem rOf_lt (x : BitVec 64) : (rOf x ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  have : (rOf x).toNat < 2 ^ 32 := by simp only [rOf, BitVec.toNat_setWidth]; omega
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 32) this (by decide)) (by decide)

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
theorem result_ok {s : State} (h : DPre s) {x : BitVec 64} {mc : Mem} {t : State} {kd : List Byte}
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
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega) hO]
    subst hb
    have hEMl := Proof.Rsa.bytesAt_length' mc (s.gpr .r3) (s.gpr .r7).toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .r7).toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega) hal
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
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega) hO]
    refine ⟨by rw [hx, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]

theorem freed_sp (b : Nat) (s : State) : (freed b s).sp = s.sp + BitVec.ofNat 64 b := rfl
theorem freed_lr (b : Nat) (s : State) : (freed b s).lr = s.lr := rfl
theorem freed_gpr (b : Nat) (s : State) : (freed b s).gpr = s.gpr := rfl
theorem freed_mem (b : Nat) (s : State) : (freed b s).mem = s.mem := rfl

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := dPre_of hpre
  have hk := h.k2
  unfold code
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (call_ok h A fun t₂ A₂ => ?_)
  refine WP.seq (WP.mono (dBuild_ok h A₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (hashD_ok h h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (kdkMac_ok h h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (clLoop_ok h h₅.post h₅.kdk) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (amLoop_ok h h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (maskPart_ok h h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (alPart_ok h h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (scanPart_ok h h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.mono (selPart_ok h h₁₀ (rOf_lt _)) fun u hu => ?_
  have hAM : (amOf s (Spec.RsaPkcs1Enc.kdk (s.gpr .r7).toNat (dOf s) (cOf s))).length = (s.gpr .r7).toNat := by
    show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _
    rw [← h₇.am]; exact Proof.Rsa.bytesAt_length' _ _ _
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [freed_gpr]; exact hu.hi r hr
  · rw [freed_sp, hu.sp]; exact BitVec.sub_add_cancel _ _
  · rw [freed_lr]; exact hu.lr
  · refine result_ok h rfl ?_ hu.r3 hu.out hu.ml hAM
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

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

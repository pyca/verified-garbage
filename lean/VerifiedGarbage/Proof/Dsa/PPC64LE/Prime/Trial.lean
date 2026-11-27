module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Trial.Loop
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Dsa.PPC64LE.ProbablePrime
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Dsa.PPC64LE.Prime.Hdr`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Prime.Load`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Prime.Entry`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Prime.Pre`, which this module and modules that import it used -/

section

/-!
# DSA's probable-prime test on PPC64LE: the contract's precondition

`CIn bits s`: the contract's precondition (with the table's region readable
too, `CIn.ofStrip`), as the proofs use it (`cin_of_pre`). `Bits`: the widths of DSA's primes, and
`Shape`: what the code needs of each (`shape_of`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime

/-- The widths of DSA's primes. -/
abbrev Bits (bits : Nat) : Prop := bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

/-- The arguments' regions. -/
abbrev cW (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩
abbrev cR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
abbrev cU (s : State) : Region := ⟨s.gpr .r7, 8⟩
abbrev cS (s : State) : Region := ⟨s.sp - 176#64, 176⟩

/-- The contract's precondition. -/
structure CIn (bits : Nat) (s : State) : Prop where
  spLo : 176 ≤ s.sp.toNat
  rd : cR s ∈ s.rd
  wr : s.wr = [cW s, cU s]
  wR : (cW s).Disjoint (cR s)
  wU : (cW s).Disjoint (cU s)
  rU : (cR s).Disjoint (cU s)
  sW : (cS s).Disjoint (cW s)
  sR : (cS s).Disjoint (cR s)
  sU : (cS s).Disjoint (cU s)
  fw : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64
  fr : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  fu : (s.gpr .r7).toNat + 8 ≤ 2 ^ 64
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r4).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .r3) % 2 = 1
  bl : Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (s.gpr .r3)) = bits

theorem cin_of_pre (bits : Nat) (s : State) (h : (Proof.Dsa.ProbablePrime.contract (layout bits) abi 176).pre s) :
    CIn bits s := by
  sig_pre [Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨spLo, rd, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl⟩ := h
  exact ⟨spLo, by rw [rd]; exact List.mem_singleton_self _, wr, wR, wU, rU, sW, sR, sU, fw, fr, fu, size, odd, bl⟩

/-- What the code needs of a width: the immediates fit, and the witness's
top word is word `t` with `b` bits. -/
structure Shape (bits : Nat) : Prop where
  w4 : 4 ≤ words bits
  w48 : words bits ≤ 48
  kw : keyWords bits < 2 ^ 15
  hlen : len bits = bits / 8
  hlen8 : 8 * len bits = bits
  hlenw : len bits ≤ 8 * words bits
  hlen1 : 1 ≤ len bits
  t0 : 0 < (bits - 1) / 64
  tw : (bits - 1) / 64 < words bits
  b1 : 1 ≤ topBits bits
  b64 : topBits bits ≤ 64
  bt : bits = 64 * ((bits - 1) / 64) + topBits bits
  hdraw : draw bits = 8 * ((bits - 1) / 64 + 1)
  hoff : topOff bits = 8 * ((bits - 1) / 64)
  hchecks : checks bits = Spec.Dsa.primeChecks bits
  hcount : count bits = if words bits ≤ 16 then 512 else 1024
  stride : 8 * (words bits + 2) < 2 ^ 15
  arr7 : 256 + 7 * (8 * (words bits + 2)) < 2 ^ 15
  big : 13 ≤ bits - 1
  key : keyWords bits = 32 + 28 * (words bits + 2)
  maskb : 64 - topBits bits < 64
  wbits : 64 * words bits = bits ∨ (bits = 160 ∧ words bits = 4)

theorem shape_of {bits : Nat} (hb : Bits bits) : Shape bits := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end VG.Proof.Dsa.PPC64LE.Prime

end

end

/-!
# DSA's probable-prime test on PPC64LE: the entry

`entry_ok`: the return address and our caller's registers saved in `ws`
from `saveOff` (`Spill.save_ok`); the header's values computed into
registers (`values_ok`) and stored (`Spill.save_ok` again): `EntryPost`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off Outside)

/-- The registers `values` writes. -/
def valRegs : List Reg :=
  [.r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29,
    .r30, .r31]

/-- The header's values in the registers, for the working space at `ws`. -/
structure HRegs (bits : Nat) (ws : Addr) (g : Reg → BitVec 64) : Prop where
  r31 : g .r31 = ws + BitVec.ofNat 64 keyOff
  r14 : g .r14 = BitVec.ofNat 64 (keyWords bits)
  r15 : g .r15 = BitVec.ofNat 64 0
  r16 : g .r16 = BitVec.ofNat 64 (words bits)
  r29 : g .r29 = BitVec.ofNat 64 (8 * (words bits + 2))
  arr : ∀ j < 8, g (arrReg j) = ws + BitVec.ofNat 64 (keyOff + (hdrBytes + j * (8 * (words bits + 2))))
  r17 : g .r17 = BitVec.ofNat 64 (draw bits)
  r18 : g .r18 = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  r19 : g .r19 = BitVec.ofNat 64 (topOff bits)
  r20 : g .r20 = BitVec.ofNat 64 (checks bits)
  r21 : g .r21 = BitVec.ofNat 64 (count bits)
  r10 : g .r10 = ws + BitVec.ofNat 64 (keyOff + hdrBytes)
  r11 : g .r11 = BitVec.ofNat 64 (2 * words bits)

/-- What `values` leaves. -/
structure Vals (bits : Nat) (s v : State) : Prop where
  regs : HRegs bits (s.gpr .r3) v.gpr
  mem : v.mem = s.mem
  keep : Keep valRegs s v

theorem mask_val {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 64) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 1) >>> (64 - b) = BitVec.ofNat 64 (2 ^ b - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ^ b ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  have h3 : (2 : Nat) ^ 64 = 2 ^ b * 2 ^ (64 - b) := by rw [← Nat.pow_add]; congr 1; omega
  have e1 : (BitVec.ofNat 64 0 - BitVec.ofNat 64 1).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_ushiftRight, e1, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [h2])]
  have hX1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hP1 : 1 ≤ 2 ^ (64 - b) := Nat.one_le_two_pow
  rw [h3]
  generalize 2 ^ b = X at *
  generalize 2 ^ (64 - b) = P at *
  have hXP : P ≤ X * P := Nat.le_mul_of_pos_left _ (by omega_using [hX1])
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, Nat.one_mul]; omega_using [hP1]
  · rw [Nat.sub_add_cancel hX1]; omega_using [h3]

/-- The header's values into registers. -/
theorem values_ok {bits : Nat} (hs : Shape bits) (s : State) :
    WP isa (.block (values bits)) s (Vals bits s) := by
  have hkw := hs.kw
  have hw48 := hs.w48
  have hst := hs.stride
  have ha7 := hs.arr7
  have e : values bits = [.addi .r31 .r3 keyOff, .li .r14 (keyWords bits), .li .r15 0, .li .r16 (words bits),
      .li .r29 (8 * (words bits + 2)),
      .addi .r22 .r31 (hdrBytes + 0 * (8 * (words bits + 2))), .addi .r23 .r31 (hdrBytes + 1 * (8 * (words bits + 2))),
      .addi .r24 .r31 (hdrBytes + 2 * (8 * (words bits + 2))), .addi .r25 .r31 (hdrBytes + 3 * (8 * (words bits + 2))),
      .addi .r26 .r31 (hdrBytes + 4 * (8 * (words bits + 2))), .addi .r27 .r31 (hdrBytes + 5 * (8 * (words bits + 2))),
      .addi .r28 .r31 (hdrBytes + 6 * (8 * (words bits + 2))), .addi .r30 .r31 (hdrBytes + 7 * (8 * (words bits + 2))),
      .li .r17 (draw bits), .li .r18 0, .subi .r18 .r18 1, .lsr .d .r18 .r18 (64 - topBits bits),
      .li .r19 (topOff bits), .li .r20 (checks bits), .li .r21 (count bits), .addi .r10 .r31 hdrBytes,
      .li .r11 (2 * words bits)] := rfl
  rw [e]
  refine WP.mono (Q := fun (v : State) => (v.gpr .r31 = s.gpr .r3 + BitVec.ofNat 64 keyOff ∧ v.gpr .r14 = BitVec.ofNat 64 (keyWords bits) ∧
      v.gpr .r15 = BitVec.ofNat 64 0 ∧ v.gpr .r16 = BitVec.ofNat 64 (words bits) ∧
      v.gpr .r29 = BitVec.ofNat 64 (8 * (words bits + 2)) ∧
      v.gpr .r22 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 0 * (8 * (words bits + 2)))) ∧
      v.gpr .r23 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 1 * (8 * (words bits + 2)))) ∧
      v.gpr .r24 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 2 * (8 * (words bits + 2)))) ∧
      v.gpr .r25 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 3 * (8 * (words bits + 2)))) ∧
      v.gpr .r26 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 4 * (8 * (words bits + 2)))) ∧
      v.gpr .r27 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 5 * (8 * (words bits + 2)))) ∧
      v.gpr .r28 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 6 * (8 * (words bits + 2)))) ∧
      v.gpr .r30 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + (hdrBytes + 7 * (8 * (words bits + 2)))) ∧
      v.gpr .r17 = BitVec.ofNat 64 (draw bits) ∧ v.gpr .r18 = BitVec.ofNat 64 (2 ^ topBits bits - 1) ∧
      v.gpr .r19 = BitVec.ofNat 64 (topOff bits) ∧ v.gpr .r20 = BitVec.ofNat 64 (checks bits) ∧
      v.gpr .r21 = BitVec.ofNat 64 (count bits) ∧
      v.gpr .r10 = s.gpr .r3 + BitVec.ofNat 64 (keyOff + hdrBytes) ∧
      v.gpr .r11 = BitVec.ofNat 64 (2 * words bits) ∧ v.mem = s.mem) ∧ Keep valRegs s v) (WP.keep _ ?_ rfl)
    fun v ⟨⟨a31, a14, a15, a16, a29, a22, a23, a24, a25, a26, a27, a28, a30, a17, a18, a19, a20, a21, a10, a11, am⟩, kv⟩ =>
      ⟨⟨a31, a14, a15, a16, a29, fun j hj => by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_using [hj]) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [a22, a23, a24, a25, a26, a27, a28, a30], a17, a18, a19, a20, a21, a10, a11⟩, am, kv⟩
  have hdraw : draw bits < 2 ^ 15 := by rw [hs.hdraw]; have := hs.tw; omega_using [hw48, this]
  have htopo : topOff bits < 2 ^ 15 := by rw [hs.hoff]; have := hs.tw; omega_using [hw48, this]
  have hchk : checks bits < 2 ^ 15 := by unfold checks; split <;> decide
  have hcnt : count bits < 2 ^ 15 := by unfold count; split <;> decide
  have hj : ∀ j ≤ 7, hdrBytes + j * (8 * (words bits + 2)) < 2 ^ 15 := fun j hj => by
    have := Nat.mul_le_mul_right (8 * (words bits + 2)) hj; simp only [hdrBytes]; omega_using [hw48, this]
  prun [hkw, hdraw, htopo, hchk, hcnt, mask_val hs.b1 hs.b64, hs.maskb, show words bits < 2 ^ 15 by omega_using [hw48],
    show 2 * words bits < 2 ^ 15 by omega_using [hw48], show keyOff < 2 ^ 15 by decide, hst, hj 0 (by decide), hj 1 (by decide),
    hj 2 (by decide), hj 3 (by decide), hj 4 (by decide), hj 5 (by decide), hj 6 (by decide), hj 7 (by decide),
    show hdrBytes < 2 ^ 15 by decide]

/-- After the entry. -/
structure EntryPost (bits : Nat) (σ s : State) : Prop where
  regs : HRegs bits (σ.gpr .r3) s.gpr
  other : ∀ r, r ∉ valRegs → r ≠ .r0 → s.gpr r = σ.gpr r
  svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem
  hdr : Spill.Saved (s.gpr .r31) s.gpr hdrSlots s.mem
  frame : Frame [⟨σ.gpr .r3 + BitVec.ofNat 64 saveOff, 168⟩, ⟨σ.gpr .r3 + BitVec.ofNat 64 keyOff, 256⟩] σ.mem s.mem
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  lr : s.lr = σ.lr

theorem savedSlots_fits : Spill.Fits savedSlots := by decide
theorem hdrSlots_fits : Spill.Fits hdrSlots := by decide
theorem savedSlots_in : ∀ p ∈ savedSlots, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 168 := by decide
theorem hdrSlots_in : ∀ p ∈ hdrSlots, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 256 := by decide

/-- The entry: the registers saved, the header. -/
theorem entry_ok {bits : Nat} (hs : Shape bits) {σ : State} (h : CIn bits σ) :
    WP isa (.block (save ++ setup bits)) σ (EntryPost bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hwsW : (⟨σ.gpr .r3, (σ.gpr .r4).toNat * 8⟩ : Region) ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .r4).toNat * 8 → InRegions σ.wr (σ.gpr .r3 + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hfw, hd])]; omega_using [hd]⟩
  simp only [save, setup, List.cons_append]
  refine WP.cons (exec_mflr) ?_
  have r3w : (σ.write .r0 σ.lr).gpr .r3 = σ.gpr .r3 := rfl
  refine Spill.save_ok (b := .r3) (l := savedSlots) (by decide) savedSlots_fits.1 (fun p hp => by
    rw [r3w]; exact inWs _ (by have := savedSlots_in p hp; simp only [saveOff, keyOff] at *; omega_using [hsz, this])) ?_
  generalize hM : Spill.saveMem (σ.write .r0 σ.lr).mem ((σ.write .r0 σ.lr).gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots = M
  rw [WP.block_append_iff]
  refine WP.mono (values_ok hs _) fun v hv => ?_
  have v31 : v.gpr .r31 = σ.gpr .r3 + BitVec.ofNat 64 keyOff := hv.regs.r31
  refine Spill.save_ok (b := .r31) (l := hdrSlots) (by decide) hdrSlots_fits.1 (fun p hp => by
    rw [hv.keep.wr, v31, Offset.add_add]
    exact inWs _ (by have := hdrSlots_in p hp; simp only [keyOff] at *; omega_using [hsz, hkey, this])) ?_
  refine WP.block_nil ⟨hv.regs, fun r hr h0 => by rw [hv.keep.gpr r hr]; simp [State.write, h0], ?_, ?_, ?_,
    hv.keep.sp, hv.keep.rd, hv.keep.wr, hv.keep.lr⟩
  · have hvm : v.mem = M := hv.mem
    have sM : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots v.mem := by
      rw [hvm, ← hM]; exact Spill.saveMem_saved savedSlots_fits _ _ _
    refine sM.frame (Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) _ _ _) fun p hp r hr => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [v31, Offset.add_add]
    have := savedSlots_in p hp
    exact Offset.disjoint _ (by simp only [saveOff, keyOff] at *; omega_using [this]) (by simp only [saveOff] at *; omega_using [this])
      (by simp only [keyOff]; omega_using [])
  · exact Spill.saveMem_saved hdrSlots_fits _ _ _
  · have f1 : Frame [⟨σ.gpr .r3 + BitVec.ofNat 64 saveOff, 168⟩] σ.mem M := by
      rw [← hM]; exact Spill.saveMem_frame savedSlots_in (by decide) _ _ _
    have hvm : v.mem = M := hv.mem
    rw [← hvm] at f1
    have f2 := Spill.saveMem_frame (lo := 0) (n := 256) hdrSlots_in (by decide) v.mem (v.gpr .r31) v.gpr
    have eb : v.gpr .r31 + BitVec.ofNat 64 0 = σ.gpr .r3 + BitVec.ofNat 64 keyOff := by rw [BitVec.add_zero, v31]
    refine (f1.mono (by simp)).trans (f2.mono fun r hr => ?_)
    rw [List.mem_singleton] at hr
    rw [hr, eb]
    simp

end VG.Proof.Dsa.PPC64LE.Prime

end

end

/-!
# DSA's probable-prime test on PPC64LE: the working space and the candidate

`env_of`: after the entry, the registers and the working space at
`B = ws + keyOff` are those of the Montgomery arithmetic (`Env`). `loadC_ok`:
the candidate's `bits / 8` big-endian bytes at `ws` into array 0
(`loadN_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off Outside slot)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- The working space's base. -/
abbrev wsB (σ : State) : Addr := σ.gpr .r3 + BitVec.ofNat 64 keyOff

/-- The working space is writable and does not wrap. -/
theorem scr_of {bits : Nat} {σ s : State} (h : CIn bits σ) (hwr : s.wr = σ.wr) :
    Scr s (wsB σ) (8 * keyWords bits) := by
  have hsz := h.size
  have hfw := h.fw
  refine ⟨⟨σ.gpr .r3, keyOff, (σ.gpr .r4).toNat * 8, by rw [hwr, h.wr]; exact List.mem_cons_self, rfl,
    by omega_using [hsz], by omega_using [hfw]⟩, ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((σ.gpr .r3).toNat + keyOff % 2 ^ 64) (2 ^ 64)
  simp only [keyOff] at *
  omega_using [hsz, hfw]

/-- After the entry, the Montgomery arithmetic's registers. -/
theorem env_of {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    Env s (wsB σ) (8 * keyWords bits) (words bits) :=
  ⟨scr_of h ep.wr, by
    rw [ep.regs.r10]; show _ = σ.gpr .r3 + BitVec.ofNat 64 keyOff + BitVec.ofNat 64 (slot (words bits) 0)
    rw [Offset.add_add]; simp only [slot, Nat.zero_mul, Nat.add_zero], ep.regs.r29, ep.regs.r11, ep.regs.r31, hs.w4,
    by have := hs.w48; omega_using [this], by rw [hs.key]; simp only [slot, hdrBytes]; omega_using []⟩

/-- The candidate's bytes lie below the working space. -/
theorem cand_sep {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < 384) {x : Addr}
    (hx : VG.Proof.Bignum.ofs (wsB σ) x < 8 * keyWords bits) : σ.gpr .r3 + BitVec.ofNat 64 i ≠ x := by
  rintro rfl
  have hsz := h.size
  have hfw := h.fw
  simp only [VG.Proof.Bignum.ofs, wsB, keyOff] at hx hsz
  have : (σ.gpr .r3 + BitVec.ofNat 64 i - (σ.gpr .r3 + BitVec.ofNat 64 552)).toNat = 2 ^ 64 - 552 + i := by
    bv_omega
  omega_using [hx, hsz, hfw, this]

/-- The candidate's bytes are unchanged by the entry. -/
theorem cand_keep {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) {n : Nat} (hn : n ≤ 384) :
    Spec.Rsa.bytesAt s.mem (σ.gpr .r3) n = Spec.Rsa.bytesAt σ.mem (σ.gpr .r3) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  refine ep.frame _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [Region.Contains, Offset.add_sub_add_left] <;> intro hc
  · exact Offset.not_lt_sub_ofNat (d := saveOff) (n := 168) (k := i) (Or.inl (by simp only [saveOff]; omega_using [hn, hi]))
      (by omega_using [hn, hi]) (by decide) (by decide) (by omega_using [hc])
  · exact Offset.not_lt_sub_ofNat (d := keyOff) (n := 256) (k := i) (Or.inl (by simp only [keyOff]; omega_using [hn, hi]))
      (by omega_using [hn, hi]) (by decide) (by decide) (by omega_using [hc])

/-- The candidate into array 0. -/
theorem loadC_ok {bits : Nat} (hs : Shape bits) {σ s : State} (h : CIn bits σ) (ep : EntryPost bits σ s) :
    WP isa (loadC bits) s fun t =>
      (arr t.mem (wsB σ) (words bits) 0 = Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .r3) ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s.mem t.mem) ∧
      Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17] s t := by
  have e := env_of hs h ep
  have hlen := hs.hlenw
  have hlen1 := hs.hlen1
  have hl384 : len bits ≤ 384 := by have := hs.w48; omega_using [hlen, this]
  have hfw := h.fw
  have hsz := h.size
  have r3 : s.gpr .r3 = σ.gpr .r3 := ep.other .r3 (by decide) (by decide)
  unfold loadC
  refine WP.seq (WP.mono (Q := fun (u : State) => (u.gpr .r12 = off (σ.gpr .r3) 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 (len bits) ∧ u.mem = s.mem) ∧ Keep [.r6, .r12] s u)
    (WP.keep _ (by prun [r3, show len bits < 2 ^ 15 by omega_using [hl384]]) rfl) fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_)
  have eu : Env u (wsB σ) (8 * keyWords bits) (words bits) := e.keep ku (by decide)
  refine WP.mono (VG.Proof.Bignum.PPC64LE.loadN_ok (k := len bits) eu.hs eu.h10 u12 u6 eu.h11 hlen1 hlen
    (by have := hs.w48; omega_using [this]) (by simp only [slot, hdrBytes]; omega_using []) (by have := eu.hZ; simp only [slot, hdrBytes] at *; omega_using [this])
    (fun i hi => ⟨_, by rw [ku.rd, ku.wr, ep.rd, ep.wr, h.wr]; exact List.mem_append_right _ List.mem_cons_self, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hl384, hi])]; have := hs.key; omega_using [hlen, hsz, hi, this]⟩)
    (fun i hi x hx => cand_sep h (by omega_using [hl384, hi]) hx)) fun t ⟨tv, to, kt⟩ => ?_
  refine ⟨⟨?_, by rw [← um]; exact to⟩, (ku.trans kt).mono (by decide)⟩
  show VG.Proof.Mont.val32 t.mem (wsB σ) (slot (words bits) 0) (2 * words bits) = _
  rw [tv, um, cand_keep ep hl384]
  simp only [Proof.Dsa.ProbablePrime.candidateAt, layout, BitVec.add_zero, ← hs.hlen]
  rfl

end VG.Proof.Dsa.PPC64LE.Prime

end

end

/-!
# DSA's probable-prime test on PPC64LE: the header

`Hdr`: the header's words after the entry (`hdr_of`), for the working space
at `B = ws + keyOff`: its length, the table's entries, `w`,
the arrays' size and addresses, the tape and its length, no octets read,
and the search's parameters. `Hdr.keep`: a change of memory that keeps the
header's words keeps `Hdr`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Impl.MillerRabin.PPC64LE.Blinded (hUni hTopOff)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off slot)

/-- The header's words. -/
structure Hdr (bits : Nat) (ws R : Addr) (rl : BitVec 64) (m : Mem) : Prop where
  len : word m (ws + BitVec.ofNat 64 keyOff) 0 = BitVec.ofNat 64 (keyWords bits)
  cnt : word m (ws + BitVec.ofNat 64 keyOff) (8 * hCnt) = BitVec.ofNat 64 (count bits)
  w : word m (ws + BitVec.ofNat 64 keyOff) 48 = BitVec.ofNat 64 (words bits)
  arr : ∀ j < 8, word m (ws + BitVec.ofNat 64 keyOff) (8 * (8 + j)) =
    off (ws + BitVec.ofNat 64 keyOff) (slot (words bits) j)
  topOff : word m (ws + BitVec.ofNat 64 keyOff) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits)
  rand : word m (ws + BitVec.ofNat 64 keyOff) (8 * hRand) = R
  randLen : word m (ws + BitVec.ofNat 64 keyOff) (8 * hRandLen) = rl
  used : word m (ws + BitVec.ofNat 64 keyOff) (8 * hUsed) = BitVec.ofNat 64 0
  checks : word m (ws + BitVec.ofNat 64 keyOff) (8 * hChecks) = BitVec.ofNat 64 (checks bits)
  top : word m (ws + BitVec.ofNat 64 keyOff) (8 * hTop) = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  k : word m (ws + BitVec.ofNat 64 keyOff) (8 * hK) = BitVec.ofNat 64 (draw bits)
  stride : word m (ws + BitVec.ofNat 64 keyOff) 224 = BitVec.ofNat 64 (8 * (words bits + 2))

/-- The header's word offsets. -/
def hdrWords : List Nat := hdrSlots.map Prod.snd

theorem hdrWords_eq : hdrWords = [0, 40, 48, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 168,
    192, 216, 224] := by decide

/-- A change of memory that keeps the header's words. -/
theorem Hdr.keep {bits : Nat} {ws R : Addr} {rl : BitVec 64} {m m' : Mem} (h : Hdr bits ws R rl m)
    (hw : ∀ d ∈ hdrWords, word m' (ws + BitVec.ofNat 64 keyOff) d = word m (ws + BitVec.ofNat 64 keyOff) d) :
    Hdr bits ws R rl m' := by
  rw [hdrWords_eq] at hw
  refine ⟨(hw _ (by simp)).trans h.len,
    (hw _ (by simp [hCnt])).trans h.cnt, (hw _ (by simp)).trans h.w, fun j hj => ?_,
    (hw _ (by simp [hTopOff])).trans h.topOff, (hw _ (by simp [hRand])).trans h.rand,
    (hw _ (by simp [hRandLen])).trans h.randLen, (hw _ (by simp [hUsed])).trans h.used,
    (hw _ (by simp [hChecks])).trans h.checks, (hw _ (by simp [hTop])).trans h.top, (hw _ (by simp [hK])).trans h.k,
    (hw _ (by simp)).trans h.stride⟩
  refine (hw _ ?_).trans (h.arr j hj)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_using [hj]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- After the entry. -/
theorem hdr_of {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) :
    Hdr bits (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r6) s.mem := by
  have hr := ep.regs
  have sv : ∀ r d, (r, d) ∈ hdrSlots → word s.mem (σ.gpr .r3 + BitVec.ofNat 64 keyOff) d = s.gpr r := fun r d hm => by
    have := ep.hdr (r, d) hm
    rw [hr.r31] at this
    exact this
  have o : ∀ r, r ∉ valRegs → r ≠ .r0 → s.gpr r = σ.gpr r := ep.other
  refine ⟨(sv .r14 _ (by decide)).trans hr.r14, (sv .r21 _ (by decide)).trans hr.r21,
    (sv .r16 _ (by decide)).trans hr.r16, fun j hj => ?_, (sv .r19 _ (by decide)).trans hr.r19,
    (sv .r5 _ (by decide)).trans (o .r5 (by decide) (by decide)),
    (sv .r6 _ (by decide)).trans (o .r6 (by decide) (by decide)), (sv .r15 _ (by decide)).trans hr.r15,
    (sv .r20 _ (by decide)).trans hr.r20, (sv .r18 _ (by decide)).trans hr.r18, (sv .r17 _ (by decide)).trans hr.r17,
    (sv .r29 _ (by decide)).trans hr.r29⟩
  rw [sv (arrReg j) _ (by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_using [hj]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hr.arr j hj]
  show _ = σ.gpr .r3 + BitVec.ofNat 64 keyOff + BitVec.ofNat 64 (slot (words bits) j)
  rw [Offset.add_add]
  rfl

end VG.Proof.Dsa.PPC64LE.Prime

end

end

/-!
# DSA's probable-prime test on PPC64LE: trial division

`Tab T m`: the table `VG_RSA_KEYGEN_TRIAL32` at `T` in `m`. `trial_ok`: the
table's address (`adrSym`), its entries for the width (`hCnt`), and the loop
(`loop_ok`): `r22` is 1 exactly when trial division finds `c` composite
(`Spec.RsaKeyGen.obviouslyComposite`, `trial_spec`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr)

/-- The table in memory `m` at `T`. -/
def Tab (T : Addr) (m : Mem) : Prop :=
  ∀ i < 1024, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i)

/-- Trial division by the width's entries is RSA's. -/
theorem trial_spec {bits c : Nat} (hb : Bits bits) (large : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (count bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := words bits) large
  rw [(shape_of hb).hcount, this]
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [Spec.RsaKeyGen.obviouslyComposite, Spec.RsaKeyGen.trialPrimes, words]

/-- The registers `trial` writes. -/
def trialRegs : List Reg := VG.Proof.RsaKeyGen.PPC64LE.Trial.entryRegs

/-- Trial division of `c` in array 0. -/
theorem trial_ok {bits c : Nat} {s : State} {B T : Addr}
    (e : Env s B (8 * keyWords bits) (words bits)) (hc : arr s.mem B (words bits) 0 = c)
    (hcnt : word s.mem B (8 * hCnt) = BitVec.ofNat 64 (count bits))
    (hT : s.syms TrialTable32.symbol = T) (htab : Tab T s.mem) (hTr : ⟨T, 8192⟩ ∈ s.rd) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hCnt) s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if VG.Proof.RsaKeyGen.trialPrefix c (count bits) then 1 else 0) ∧
        t.mem = s.mem) ∧ (∀ r, r ∉ trialRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.syms = s.syms := by
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hn : 1 ≤ count bits ∧ count bits ≤ 1024 := by unfold count; split <;> decide
  have hsc := e.hs
  unfold VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine WP.of_syms (WP.seq (WP.mono (Q := fun (u : State) => (u.gpr .r23 = T ∧
      u.gpr .r24 = BitVec.ofNat 64 (count bits) ∧ u.mem = s.mem ∧ u.syms = s.syms) ∧ (∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ u.sp = s.sp)
    ?_ fun u ⟨⟨u23, u24, um, us⟩, ug, urd, uwr, usp⟩ => ?_))
  · refine WP.cons (exec_adrSym (by decide)) ?_
    simp only [ldh, hCnt]
    prun [e.h31, hsc.ld (d := 40) (n := 8) (by omega_using [hZ])]
    refine ⟨⟨hT, hcnt, rfl⟩, fun r hr => ?_⟩
    have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
    have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
    simp only [h1, h2, ↓reduceIte]
  · refine WP.mono (VG.Proof.RsaKeyGen.PPC64LE.Trial.loop_ok (n := count bits) (o := slot (words bits) 0) (w := words bits) (hsc.congr uwr) ?_ ?_ ?_
      (by omega_using [hw4]) (by omega_using [hw128]) (by simp only [slot, hdrBytes]; omega_using [hZ]) hn.1 hn.2 u23 (fun i hi => ⟨by rw [um]; exact htab i (by omega_using [hn, hi]), ?_⟩) u24)
      fun t ⟨⟨t22, tm⟩, kt⟩ sy => ⟨⟨t22, tm.trans um⟩, fun r hr => (kt.gpr r hr).trans (ug r hr),
        kt.rd.trans urd, kt.wr.trans uwr, kt.sp.trans usp, sy⟩
    · exact (ug _ (by decide)).trans e.h10
    · exact (ug _ (by decide)).trans e.h11
    · rw [um]; exact hc
    · refine ⟨_, by rw [urd]; exact List.mem_append_left _ hTr, ?_⟩
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hn, hi])]; omega_using [hn, hi]

end VG.Proof.Dsa.PPC64LE.Prime

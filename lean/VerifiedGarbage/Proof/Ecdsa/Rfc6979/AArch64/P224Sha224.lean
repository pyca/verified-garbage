import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Tables
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha224
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on AArch64

SHA-224, with any implementation `v` of SHA-256's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract` for 256 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p224_sha224_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224

open VG VG.AArch64
open VG.Proof.Sha256.AArch64 (Compress)

open VG.Proof.Ecdsa.AArch64.P224 (TblHeld p224_combConsts p224_combWords_length satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 28⟩, ⟨s.gpr .x2, 28⟩, ⟨s.syms Impl.Ecdsa.AArch64.p224.tsym, 8 * Impl.Ecdsa.AArch64.p224.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x3, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x1, 28⟩) (og : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x2, 28⟩)
    (oc : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x3, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .x1, 28⟩ ⟨s.gpr .x3, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .x2, 28⟩ ⟨s.gpr .x3, 8192⟩)
    (ko : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x0, 56⟩)
    (kd : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x1, 28⟩)
    (kg : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x2, 28⟩)
    (kc : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x3, 8192⟩)
    (no : (s.gpr .x0).toNat + 56 ≤ 2 ^ 64) (nd : (s.gpr .x1).toNat + 28 ≤ 2 ^ 64)
    (ng : (s.gpr .x2).toNat + 28 ≤ 2 ^ 64) (nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64) (hsp : 256 ≤ s.sp.toNat)
    (ht : TblHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x3, 8192⟩, ⟨s.sp - BitVec.ofNat 64 256, 256⟩]) :
    (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 256).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, below]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (List.mem_append_left _ hr),
    hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩

theorem sat_spec :
    (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 256).pre
      (satState 28 28 satMem 151552) := by
  have hl := p224_combWords_length
  have held : ∀ i < Impl.Ecdsa.AArch64.p224.combWords.length, (satState 28 28 satMem 151552).mem.readW ((satState 28 28 satMem 151552).syms Impl.Ecdsa.AArch64.p224.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = Impl.Ecdsa.AArch64.p224.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.p224 Spec.Ecdsa.Rfc6979.P224Sha224.inst 256).Implies
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 256) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, below] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hstk, ht, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩ := h
    refine ⟨?_, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, hheld, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hdw _ (by rw [hw]; simp [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.P224.inst, Spec.P224.curve])
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p224_combConsts, Abi.withConsts, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p224_combConsts, Abi.withConsts, rfcAArch64, below] at h
    obtain ⟨hsp, hsy, hl, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, hsy⟩
  sat := ⟨satState 28 28 satMem 151552, sat_spec⟩

/-- SHA-224, with the implementation `v` of SHA-256's compression function. -/
def pack (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) (v : Compress) :
    RfcHash where
  R := p224 hL hI hT
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha224.hash v
  ok := Proof.Pbkdf2.Md.AArch64.Sha224.ok v
  C := Proof.Pbkdf2.Md.AArch64.Sha224.coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha224.satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha224.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr (.inr ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI hT v)).sign
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 256) :=
  AArch64.sign_verified (pack hL hI hT v) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224

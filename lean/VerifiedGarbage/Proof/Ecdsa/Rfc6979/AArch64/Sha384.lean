import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P256
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on AArch64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract` for 256 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p256_sha384_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384

open VG VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)

open VG.Proof.Ecdsa.AArch64 (TblHeld p256_combConsts p256_combWords_length satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 48⟩, ⟨s.syms Impl.Ecdsa.AArch64.p256.tsym, 8 * Impl.Ecdsa.AArch64.p256.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x1, 32⟩) (og : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x2, 48⟩)
    (oc : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x3, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .x2, 48⟩ ⟨s.gpr .x3, 8192⟩)
    (ko : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x0, 64⟩)
    (kd : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x1, 32⟩)
    (kg : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x2, 48⟩)
    (kc : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 256, 256⟩ ⟨s.gpr .x3, 8192⟩)
    (no : (s.gpr .x0).toNat + 64 ≤ 2 ^ 64) (nd : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (ng : (s.gpr .x2).toNat + 48 ≤ 2 ^ 64) (nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64) (hsp : 256 ≤ s.sp.toNat)
    (ht : TblHeld s [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, 8192⟩, ⟨s.sp - BitVec.ofNat 64 256, 256⟩]) :
    (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, below]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (List.mem_append_left _ hr),
    hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩

theorem sat_spec :
    (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256).pre
      (satState 32 48 satMem 151552) := by
  have hl := p256_combWords_length
  have held : ∀ i < Impl.Ecdsa.AArch64.p256.combWords.length, (satState 32 48 satMem 151552).mem.readW ((satState 32 48 satMem 151552).syms Impl.Ecdsa.AArch64.p256.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = Impl.Ecdsa.AArch64.p256.combWords.getD i 0 := satMem_held
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
    (rfcAArch64 Impl.Ecdsa.AArch64.p256 Spec.Ecdsa.Rfc6979.P256Sha384.inst 256).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, below] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hstk, ht, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩ := h
    refine ⟨?_, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, hheld, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hdw _ (by rw [hw]; simp [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.P256.inst, Spec.P256.curve])
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, rfcAArch64, below] at h
    obtain ⟨hsp, hsy, hl, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, hsy⟩
  sat := ⟨satState 32 48 satMem 151552, sat_spec⟩

/-- SHA-384, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) (v : Compress) :
    RfcHash where
  R := p256 hL hI hT
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha512.hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name Spec.Sha512.H0_384
  ok := Proof.Pbkdf2.Md.AArch64.Sha512.ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl
    (Or.inl rfl)
  C := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha512.sha384_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI hT v)).sign
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256) :=
  AArch64.sign_verified (pack hL hI hT v) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384

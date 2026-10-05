import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on AArch64

SHA-256, with any implementation `v` of its compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract` for 240 bytes of stack,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p256_sha256_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.Sha256

open VG VG.AArch64
open VG.Proof.Sha256.AArch64 (Compress)

open VG.Impl.Ecdsa.AArch64 (p256)
open VG.Proof.Ecdsa.AArch64 (TblHeld p256_combConsts p256_combWords_length satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x1, 32⟩) (og : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x2, 32⟩)
    (oc : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x3, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, 8192⟩)
    (ko : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .x0, 64⟩)
    (kd : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .x1, 32⟩)
    (kg : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .x2, 32⟩)
    (kc : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .x3, 8192⟩)
    (no : (s.gpr .x0).toNat + 64 ≤ 2 ^ 64) (nd : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (ng : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64) (nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64) (hsp : 240 ≤ s.sp.toNat)
    (ht : TblHeld s [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, 8192⟩, ⟨s.sp - BitVec.ofNat 64 240, 240⟩]) :
    (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (AArch64.abi.withConsts p256.combConsts) 240).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, below]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (List.mem_append_left _ hr),
    hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩

theorem sat_spec :
    (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (AArch64.abi.withConsts p256.combConsts) 240).pre
      (satState 32) := by
  have hl := p256_combWords_length
  have held : ∀ i < p256.combWords.length, (satState 32).mem.readW ((satState 32).syms p256.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p256.combWords.getD i 0 := satMem_held
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
    (rfcAArch64 Spec.Ecdsa.Rfc6979.P256Sha256.inst).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (AArch64.abi.withConsts p256.combConsts) 240) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, below] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hstk, ht, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩ := h
    refine ⟨?_, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, hheld, hfit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p256_combConsts, Abi.withConsts, rfcAArch64, below] at h
    obtain ⟨hsp, hsy, hl, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, hsy⟩
  sat := ⟨satState 32, sat_spec⟩

/-- SHA-256, with the implementation `v` of its compression function. -/
def pack (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (v : Compress) : RfcHash where
  I := Spec.Ecdsa.Rfc6979.P256Sha256.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha256.hash v
  ok := Proof.Pbkdf2.Md.AArch64.Sha256.ok v
  C := Proof.Pbkdf2.Md.AArch64.Sha256.coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha256.satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha256.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inl ⟨rfl, rfl⟩
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  coreX := Proof.Ecdsa.AArch64.sign_a64 hL hT
  coreCT := Proof.Ecdsa.AArch64.sign_ct

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hT v)).sign
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract (AArch64.abi.withConsts p256.combConsts) 240) :=
  AArch64.sign_verified (pack hL hT v) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.Sha256

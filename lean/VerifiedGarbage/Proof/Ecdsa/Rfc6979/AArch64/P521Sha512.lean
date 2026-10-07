import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Tables
import VerifiedGarbage.Proof.Framework.KernelAux
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on AArch64

SHA-512, with any implementation `v` of its compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract` for 400 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p521_sha512_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512

open VG VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)

open VG.Proof.Ecdsa.AArch64.P521 (TblHeld p521_combConsts p521_combWords_length satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 66⟩, ⟨s.gpr .x2, 64⟩, ⟨s.syms Impl.Ecdsa.AArch64.p521.tsym, 8 * Impl.Ecdsa.AArch64.p521.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 132⟩, ⟨s.gpr .x3, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .x0, 132⟩ ⟨s.gpr .x1, 66⟩) (og : Region.Disjoint ⟨s.gpr .x0, 132⟩ ⟨s.gpr .x2, 64⟩)
    (oc : Region.Disjoint ⟨s.gpr .x0, 132⟩ ⟨s.gpr .x3, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .x1, 66⟩ ⟨s.gpr .x3, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .x2, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (ko : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 400, 400⟩ ⟨s.gpr .x0, 132⟩)
    (kd : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 400, 400⟩ ⟨s.gpr .x1, 66⟩)
    (kg : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 400, 400⟩ ⟨s.gpr .x2, 64⟩)
    (kc : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 400, 400⟩ ⟨s.gpr .x3, 8192⟩)
    (no : (s.gpr .x0).toNat + 132 ≤ 2 ^ 64) (nd : (s.gpr .x1).toNat + 66 ≤ 2 ^ 64)
    (ng : (s.gpr .x2).toNat + 64 ≤ 2 ^ 64) (nc : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64) (hsp : 400 ≤ s.sp.toNat)
    (ht : TblHeld s [⟨s.gpr .x0, 132⟩, ⟨s.gpr .x3, 8192⟩, ⟨s.sp - BitVec.ofNat 64 400, 400⟩]) :
    (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 400).pre s := by
  obtain ⟨held, fit, hdw⟩ := ht
  rw [p521_combConsts]
  generalize Impl.Ecdsa.AArch64.p521.combWords = ws at hrd held fit hdw ⊢
  kernel_aux =>
    sig_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, below]
    exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (List.mem_append_left _ hr),
      hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩

theorem sat_spec :
    (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 400).pre
      (satState 66 64 satMem 764928) := by
  have hl := p521_combWords_length
  have held : ∀ i < Impl.Ecdsa.AArch64.p521.combWords.length, (satState 66 64 satMem 764928).mem.readW ((satState 66 64 satMem 764928).syms Impl.Ecdsa.AArch64.p521.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = Impl.Ecdsa.AArch64.p521.combWords.getD i 0 := satMem_held
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
    (rfcAArch64 Impl.Ecdsa.AArch64.p521 Spec.Ecdsa.Rfc6979.P521Sha512.inst 400).Implies
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 400) where
  pre s h := by
    rw [p521_combConsts] at h
    unfold rfcAArch64 TblOk
    generalize Impl.Ecdsa.AArch64.p521.combWords = ws at h ⊢
    kernel_aux =>
      sig_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
        Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
        AArch64.abi, AArch64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
        below] at h
      obtain ⟨hsp, hd, hheld, hfit, hdw, hstk, ht, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc⟩ := h
      refine ⟨?_, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, hheld, hfit, ?_⟩
      · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact hdw _ (by rw [hw]; simp [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.P521.inst, Spec.P521.curve])
        · exact hdw _ (by rw [hw]; simp)
        · exact hstk
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p521_combConsts, Abi.withConsts, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      AArch64.abi, AArch64.argRegs, p521_combConsts, Abi.withConsts, rfcAArch64, below] at h
    obtain ⟨hsp, hsy, hl, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, (List.cons.inj hl).1, hsy⟩
  sat := ⟨satState 66 64 satMem 764928, sat_spec⟩

/-- SHA-512, with the implementation `v` of its compression function. -/
def pack (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (v : Compress) :
    RfcHash where
  R := p521 hL hI hT
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  H := Proof.Pbkdf2.Md.AArch64.Sha512.hash v Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name Spec.Sha512.H0_512
  ok := Proof.Pbkdf2.Md.AArch64.Sha512.ok v rfl
    (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))
  C := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_coreOK
  satI := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_satI
  satF := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr (.inl ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := ⟨rfl, rfl⟩

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) (v : Compress) :
    Verified AArch64.target (cfgOf (pack hL hI hT v)).sign
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 400) :=
  AArch64.sign_verified (pack hL hI hT v) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512

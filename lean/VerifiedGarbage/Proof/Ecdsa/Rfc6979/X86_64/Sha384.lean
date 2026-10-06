import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256Adx
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha384

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-384 on x86-64

SHA-384, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract` for 240 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p256_sha384_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.Sha384

open VG VG.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

open VG.Proof.Ecdsa.X86_64 (TblHeld p256_combConsts p256W_length satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 48⟩, ⟨s.syms "VG_P256_COMB", 8 * VG.Proof.Ecdsa.X86_64.p256W.length⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 32⟩) (og : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 48⟩)
    (oc : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .rdx, 48⟩ ⟨s.gpr .rcx, 8192⟩)
    (ro : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 64⟩) (rd : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (rg : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 48⟩) (rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (ko : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rdi, 64⟩)
    (kd : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rsi, 32⟩)
    (kg : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rdx, 48⟩)
    (kc : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rcx, 8192⟩)
    (no : (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64) (nd : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (ng : (s.gpr .rdx).toNat + 48 ≤ 2 ^ 64) (nc : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (hsp : 240 ≤ (s.gpr .rsp).toNat)
    (ht : TblHeld s [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩,
      ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩]) :
    (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts) 240).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc,
    no, nd, ng, nc⟩

theorem sat_spec : (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts) 240).pre (satState 32 48 satMem [⟨0x100000, 151552⟩]) := by
  have hl := p256W_length
  have held : ∀ i < VG.Proof.Ecdsa.X86_64.p256W.length, (satState 32 48 satMem [⟨0x100000, 151552⟩]).mem.readW
      ((satState 32 48 satMem [⟨0x100000, 151552⟩]).syms "VG_P256_COMB" + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.Ecdsa.X86_64.p256W.getD i 0 :=
    satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : (rfcX86_64 Impl.Ecdsa.X86_64.p256.combConsts Spec.Ecdsa.Rfc6979.P256Sha384.inst 240).Implies (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts) 240) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p256_combConsts, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hdr, hds, ht, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd,
      ng, nc⟩ := h
    refine ⟨hsp, ?_, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, fun c hc => ?_,
      fun T hT => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
      simp only [p256_combConsts, Abi.constRegions, List.map_cons, List.map_nil]
      rfl
    · simp only [p256_combConsts, List.mem_singleton] at hc; subst hc; exact hheld
    · simp only [p256_combConsts, Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at hT
      subst hT
      refine ⟨hfit, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; exact List.mem_cons_self ..)
      · exact hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact hdr
      · exact hds
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p256_combConsts, Abi.withConsts, rfcX86_64]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P256Sha384.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p256_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hsy, hl, h1, h2, h3, h4⟩ := h
    refine ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, fun c hc => ?_⟩
    simp only [p256_combConsts, List.mem_singleton] at hc; subst hc; exact hsy
  sat := ⟨_, sat_spec⟩

/-- SHA-384, with the implementation `v` of SHA-512's compression function, and
P-256's multiplication with BMI2 and ADX (`adx`) or without. -/
def pack (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    RfcHash where
  R := p256Of adx hL hT hI
  I := Spec.Ecdsa.Rfc6979.P256Sha384.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha512.sha384H v
  ok := Proof.Pbkdf2.Md.X86_64.Sha512.sha384OK v
  C := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha512.sha384K v
  satI := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha512.sha384_satF
  ecdsa := by cases adx <;> rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inl ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := by cases adx <;> exact Nat.le_of_ble_eq_true rfl
  updSp := show (Proof.Pbkdf2.Md.X86_64.Sha512.coreH 48).updC.allInstrs _ = true by decide +kernel

theorem sign_verified (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    Verified X86_64.target (cfgOf (pack adx hL hT hI v)).sign
      (Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts) 240) :=
  by cases adx <;> exact X86_64.sign_verified (pack _ hL hT hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.Sha384

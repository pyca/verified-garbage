import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P521
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512

/-!
# Deterministic ECDSA over P-521 with HMAC-SHA-512 on x86-64

SHA-512, with any implementation `v` of SHA-512's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract` for 384 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p521_sha512_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512

open VG VG.X86_64
open VG.Proof.Sha512.X86_64 (Compress)

open VG.Proof.Ecdsa.X86_64.P521 (TblHeld p521_combConsts p521_constRegions satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 66⟩, ⟨s.gpr .rdx, 64⟩, ⟨s.syms "VG_P521_COMB", 764928⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 132⟩, ⟨s.gpr .rcx, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .rdi, 132⟩ ⟨s.gpr .rsi, 66⟩) (og : Region.Disjoint ⟨s.gpr .rdi, 132⟩ ⟨s.gpr .rdx, 64⟩)
    (oc : Region.Disjoint ⟨s.gpr .rdi, 132⟩ ⟨s.gpr .rcx, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .rsi, 66⟩ ⟨s.gpr .rcx, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .rdx, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (ro : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 132⟩) (rd : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 66⟩)
    (rg : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 64⟩) (rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (ko : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 384, 384⟩ ⟨s.gpr .rdi, 132⟩)
    (kd : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 384, 384⟩ ⟨s.gpr .rsi, 66⟩)
    (kg : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 384, 384⟩ ⟨s.gpr .rdx, 64⟩)
    (kc : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 384, 384⟩ ⟨s.gpr .rcx, 8192⟩)
    (no : (s.gpr .rdi).toNat + 132 ≤ 2 ^ 64) (nd : (s.gpr .rsi).toNat + 66 ≤ 2 ^ 64)
    (ng : (s.gpr .rdx).toNat + 64 ≤ 2 ^ 64) (nc : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (hsp : 384 ≤ (s.gpr .rsp).toNat)
    (ht : TblHeld s [⟨s.gpr .rdi, 132⟩, ⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩,
      ⟨s.gpr .rsp - BitVec.ofNat 64 384, 384⟩]) :
    (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 384).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions,
    Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc,
    no, nd, ng, nc⟩

theorem sat_spec : (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 384).pre (satState 66 64 satMem [⟨0x100000, 764928⟩]) := by
  have held : ∀ i < VG.Proof.Ecdsa.X86_64.P521.p521W.length, (satState 66 64 satMem [⟨0x100000, 764928⟩]).mem.readW
      ((satState 66 64 satMem [⟨0x100000, 764928⟩]).syms "VG_P521_COMB" + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.Ecdsa.X86_64.P521.p521W.getD i 0 :=
    satMem_held
  refine spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : (rfcX86_64 Impl.Ecdsa.X86_64.p521.combConsts Spec.Ecdsa.Rfc6979.P521Sha512.inst 384).Implies (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 384) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions,
      Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hdr, hds, ht, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd,
      ng, nc⟩ := h
    refine ⟨hsp, ?_, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, fun c hc => ?_,
      fun T hT => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
      simp only [p521_combConsts, p521_constRegions]
      rfl
    · simp only [p521_combConsts, List.mem_singleton] at hc; subst hc; exact hheld
    · simp only [p521_combConsts, p521_constRegions, List.mem_singleton] at hT
      subst hT
      refine ⟨hfit, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; exact List.mem_cons_self ..)
      · exact hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact hdr
      · exact hds
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p521_combConsts, Abi.withConsts, rfcX86_64]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P521Sha512.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P521.inst, Spec.P521.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p521_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hsy, hl, h1, h2, h3, h4⟩ := h
    refine ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, fun c hc => ?_⟩
    simp only [p521_combConsts, List.mem_singleton] at hc; subst hc; exact hsy
  sat := ⟨_, sat_spec⟩

/-- SHA-512, with the implementation `v` of SHA-512's compression function. -/
def pack (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (v : Compress) :
    RfcHash where
  R := p521 hL hT
  I := Spec.Ecdsa.Rfc6979.P521Sha512.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha512.sha512H v
  ok := Proof.Pbkdf2.Md.X86_64.Sha512.sha512OK v
  C := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha512.sha512K v
  satI := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha512.sha512_satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr ⟨rfl, rfl⟩)
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := ⟨rfl, rfl⟩
  updSp := show (Proof.Pbkdf2.Md.X86_64.Sha512.coreH 64).updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL hT v)).sign
      (Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 384) :=
  X86_64.sign_verified (pack hL hT v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512

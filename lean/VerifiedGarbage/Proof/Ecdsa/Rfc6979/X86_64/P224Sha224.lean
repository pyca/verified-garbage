import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224

/-!
# Deterministic ECDSA over P-224 with HMAC-SHA-224 on x86-64

SHA-224, with any implementation `v` of SHA-256's compression function, as the
proof's hash function (`pack`), and the contract
`Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract` for 240 bytes of stack and
the comb's tables,
which implies the one the proof is written against (`implies`):
`vg_ecdsa_p224_sha224_sign` is verified (`sign_verified`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224

open VG VG.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

open VG.Proof.Ecdsa.X86_64.P224 (TblHeld p224_combConsts p224W_length satMem satMem_held)

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 28⟩, ⟨s.gpr .rdx, 28⟩, ⟨s.syms "VG_P224_COMB", 8 * VG.Proof.Ecdsa.X86_64.P224.p224W.length⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 56⟩, ⟨s.gpr .rcx, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .rdi, 56⟩ ⟨s.gpr .rsi, 28⟩) (og : Region.Disjoint ⟨s.gpr .rdi, 56⟩ ⟨s.gpr .rdx, 28⟩)
    (oc : Region.Disjoint ⟨s.gpr .rdi, 56⟩ ⟨s.gpr .rcx, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .rsi, 28⟩ ⟨s.gpr .rcx, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .rdx, 28⟩ ⟨s.gpr .rcx, 8192⟩)
    (ro : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 56⟩) (rd : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 28⟩)
    (rg : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 28⟩) (rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (ko : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rdi, 56⟩)
    (kd : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rsi, 28⟩)
    (kg : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rdx, 28⟩)
    (kc : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩ ⟨s.gpr .rcx, 8192⟩)
    (no : (s.gpr .rdi).toNat + 56 ≤ 2 ^ 64) (nd : (s.gpr .rsi).toNat + 28 ≤ 2 ^ 64)
    (ng : (s.gpr .rdx).toNat + 28 ≤ 2 ^ 64) (nc : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (hsp : 240 ≤ (s.gpr .rsp).toNat)
    (ht : TblHeld s [⟨s.gpr .rdi, 56⟩, ⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩,
      ⟨s.gpr .rsp - BitVec.ofNat 64 240, 240⟩]) :
    (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts) 240).pre s := by
  sig_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc,
    no, nd, ng, nc⟩

theorem sat_spec : (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts) 240).pre (satState 28 28 satMem [⟨0x100000, 151552⟩]) := by
  have hl := p224W_length
  have held : ∀ i < VG.Proof.Ecdsa.X86_64.P224.p224W.length, (satState 28 28 satMem [⟨0x100000, 151552⟩]).mem.readW
      ((satState 28 28 satMem [⟨0x100000, 151552⟩]).syms "VG_P224_COMB" + BitVec.ofNat 64 (8 * i)) 64 = VG.Proof.Ecdsa.X86_64.P224.p224W.getD i 0 :=
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

theorem implies : (rfcX86_64 Impl.Ecdsa.X86_64.p224.combConsts Spec.Ecdsa.Rfc6979.P224Sha224.inst 240).Implies (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts) 240) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hdr, hds, ht, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd,
      ng, nc⟩ := h
    refine ⟨hsp, ?_, hw, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, fun c hc => ?_,
      fun T hT => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
      simp only [p224_combConsts, Abi.constRegions, List.map_cons, List.map_nil]
      rfl
    · simp only [p224_combConsts, List.mem_singleton] at hc; subst hc; exact hheld
    · simp only [p224_combConsts, Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at hT
      subst hT
      refine ⟨hfit, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; exact List.mem_cons_self ..)
      · exact hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact hdr
      · exact hds
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p224_combConsts, Abi.withConsts, rfcX86_64]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.P224Sha224.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P224.inst, Spec.P224.curve, Spec.Ecdsa.scratchWords,
      X86_64.abi, X86_64.argRegs, p224_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hsy, hl, h1, h2, h3, h4⟩ := h
    refine ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1, fun c hc => ?_⟩
    simp only [p224_combConsts, List.mem_singleton] at hc; subst hc; exact hsy
  sat := ⟨_, sat_spec⟩

/-- SHA-224, with the implementation `v` of SHA-256's compression function. -/
def pack (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    RfcHash where
  R := p224 hL hT hI
  I := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  H := Proof.Pbkdf2.Md.X86_64.Sha224.hash v
  ok := Proof.Pbkdf2.Md.X86_64.Sha224.ok v
  C := Proof.Pbkdf2.Md.X86_64.Sha224.coreOK
  K := Proof.Pbkdf2.Md.X86_64.Sha224.callees v
  satI := Proof.Pbkdf2.Md.X86_64.Sha224.satI
  satF := Proof.Pbkdf2.Md.X86_64.Sha224.satF
  ecdsa := rfl
  hash := rfl
  len := rfl
  tries := rfl
  hDB := .inr (.inr (.inr ⟨rfl, rfl⟩))
  hS := Nat.le_of_ble_eq_true rfl
  hW := Nat.le_of_ble_eq_true rfl
  hWb := Nat.le_of_ble_eq_true rfl
  hQ := Nat.le_of_ble_eq_true rfl
  updSp := show Proof.Pbkdf2.Md.X86_64.Sha224.coreH.updC.allInstrs _ = true by decide +kernel

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (v : Compress) :
    Verified X86_64.target (cfgOf (pack hL hT hI v)).sign
      (Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts) 240) :=
  X86_64.sign_verified (pack hL hT hI v) implies

end VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224

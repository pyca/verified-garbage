module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Contract
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

variable {E : Impl.Ecdsa.AArch64.Cfg} {J : Spec.Ecdsa.Rfc6979.Instance}

theorem tableAddr_of (ht : E.tbl.isEmpty = false) (syms : String → Addr) : tableAddr E syms = syms E.tsym := by
  simp only [tableAddr, ht, Bool.false_eq_true, ite_false]

theorem tableRegions_of (ht : E.tbl.isEmpty = false) (a : Addr) :
    tableRegions E a = [⟨a, 8 * E.combWords.length⟩] := by
  simp only [tableRegions, ht, Bool.false_eq_true, ite_false]

/-- The contract's precondition, from the proof's: for a witness. -/
theorem pre_of (hsw : J.scratchWords = 1024) (ht : E.tbl.isEmpty = false) {s : State}
    (h : (rfcAArch64 E J 512).pre s) : (J.signAnyContract (AArch64.abi.withConsts E.combConsts) 512).pre s := by
  obtain ⟨hk, hlen, hrd, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, held, fit, hdw⟩ := h
  rw [tableAddr_of ht] at held fit hdw
  rw [tableRegions_of ht, tableAddr_of ht] at hrd
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
    AArch64.abi, AArch64.argRegs, Impl.Ecdsa.AArch64.Cfg.combConsts, Abi.withConsts, Abi.constRegions,
    Abi.constsHeld, stackBelow, below]
  simp only [hsw, Nat.reduceMul]
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (List.mem_append_left _ hr),
    hdw _ (by simp), by rw [hrd]; rfl, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hk, hlen⟩

/-- The contract implies the proof's, with the contract's precondition
satisfiable (`hsat`, for each curve). -/
theorem implies_of (hsw : J.scratchWords = 1024) (ht : E.tbl.isEmpty = false)
    (hsat : ∃ s, (rfcAArch64 E J 512).pre s) :
    (rfcAArch64 E J 512).Implies (J.signAnyContract (AArch64.abi.withConsts E.combConsts) 512) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, Impl.Ecdsa.AArch64.Cfg.combConsts, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, below] at h
    simp only [hsw, Nat.reduceMul] at h
    obtain ⟨hsp, hd, hheld, hfit, hdw, hstk, htk, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hk, hlen⟩ :=
      h
    refine ⟨hk, hlen, ?_, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, ?_, ?_, ?_⟩
    · rw [tableRegions_of ht, tableAddr_of ht, ← List.take_append_drop (s.rd.length - 1) s.rd, htk, hd]
    · rw [tableAddr_of ht]; exact hheld
    · rw [tableAddr_of ht]; exact hfit
    · rw [tableAddr_of ht]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hstk
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, Impl.Ecdsa.AArch64.Cfg.combConsts, Abi.withConsts, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, Impl.Ecdsa.AArch64.Cfg.combConsts, Abi.withConsts, rfcAArch64, below] at h
    obtain ⟨hsp, hsy, hl, h0, h1, h2, h3, h4, h5⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, h4, by rw [selOf, selOf, h5], (List.cons.inj hl).1,
      by rw [tableAddr_of ht, tableAddr_of ht, hsy]⟩
  sat := let ⟨s, h⟩ := hsat; ⟨s, pre_of hsw ht h⟩

/-! ## Curves without tables -/

theorem tableRegions_nt (ht : E.tbl.isEmpty = true) (a : Addr) : tableRegions E a = [] := by
  simp only [tableRegions, ht, ite_true]

theorem pre_of_nt (hsw : J.scratchWords = 1024) (ht : E.tbl.isEmpty = true) {s : State}
    (h : (rfcAArch64 E J 512).pre s) : (J.signAnyContract AArch64.abi 512).pre s := by
  obtain ⟨hk, hlen, hrd, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, -⟩ := h
  rw [tableRegions_nt ht, List.append_nil] at hrd
  sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
    AArch64.abi, AArch64.argRegs, stackBelow, below]
  simp only [hsw, Nat.reduceMul]
  exact ⟨hsp, hrd, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hk, hlen⟩

/-- The contract of a curve without tables implies the proof's, with the
contract's precondition satisfiable (`hsat`, for each curve). -/
theorem implies_nt (hsw : J.scratchWords = 1024) (ht : E.tbl.isEmpty = true) (hw₀ : E.combWords = [])
    (hsat : ∃ s, (rfcAArch64 E J 512).pre s) :
    (rfcAArch64 E J 512).Implies (J.signAnyContract AArch64.abi 512) where
  pre s h := by
    sig_pre [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, stackBelow, below] at h
    simp only [hsw, Nat.reduceMul] at h
    obtain ⟨hsp, hrd, hw, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hk, hlen⟩ := h
    refine ⟨hk, hlen, by rw [tableRegions_nt ht, List.append_nil]; exact hrd, hw, od, og, oc, dc, gc, ko, kd, kg,
      kc, no, nd, ng, nc, hsp, ?_, ?_, ?_⟩
    · rw [hw₀]; exact fun i hi => absurd hi (Nat.not_lt_zero _)
    · rw [hw₀, tableAddr, ht]; exact Nat.zero_le _
    · rw [hw₀]
      intro r _ x hx
      simp only [Region.Contains, List.length_nil, Nat.mul_zero] at hx
      omega
  post := by
    sig_implies_post [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, rfcAArch64, below]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.Rfc6979.Instance.signAnyContract, Spec.Ecdsa.Rfc6979.Instance.signAnySig, hsw,
      AArch64.abi, AArch64.argRegs, rfcAArch64, below] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5⟩ := h
    exact ⟨hsp, h0, h1, h2, h3, h4, by rw [selOf, selOf, h5], (List.cons.inj hl).1,
      by simp only [tableAddr, ht, ite_true]⟩
  sat := let ⟨s, h⟩ := hsat; ⟨s, pre_of_nt hsw ht h⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

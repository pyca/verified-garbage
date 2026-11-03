module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.CTPost
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Correct
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPss.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMgf
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Hashes
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Spec.RsaPss.Precomputed

/-!
# RSASSA-PSS verification on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Verified.lean`, `Inst.lean`): constant time
(`code_constantTime`, from `code_ct`, with the contract's public data as
`PubP`); a state meeting the precondition for each hash function the other
targets verify with (`verify_sat`); MD5's streaming functions constant time
for the contracts the proofs call them by (`md5CT`), as SHA-1's and the SHA-2
family's are (`Proof/RsaOaep/RISCV64/Hashes.lean`); and a hash function's
streaming functions with what the proofs need of them (`Link`), for which
`link_verified` is verification, which the registration files bind.
-/

@[expose] public section

/-!
# RSASSA-PSS verification on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/CTPub.lean`, `CTMain.lean`): the public data of an
entry state (`PubP`: the pointers, the lengths, the salt-length mode, the
modulus, `e` and `pre`) fixes what `Base` fixes (`pssOk`) and `c`,
`salt_len` and the mode (`PubP.agreeP`). Two runs from entry states with
the same public data leak alike (`code_ct`): the checks (`checks_ct`)
branch on public values, the call of the public operation leaks what it
leaks for its public arguments (`call_ct`), and the code after it is
`post_ct`.
-/


namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off fx kR Agree Ok B pins_of two_seq HashCT words_entry bytes_entry
  restore_taint Saves fb stackBytes)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Two Pins two_post two_ite two_alloc eval_zero eval_nonzero pdCallCT)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubP (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s.gpr r = a.gpr r
  a0 : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32
  args : ∀ i, 1 ≤ i → i < 5 → stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s) = Spec.Rsa.bytesAt a.mem (a.gpr .a0) (kk a)
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    a = c ∧ b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).1, (List.append_inj hi ha).2,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubP_of {H : Spec.Mgf1.Hash} {s₁ s₂ : State}
    (h : (Spec.RsaPss.verifyPrecomputedContract H H abi stackBytes).pub s₁ s₂) : PubP s₁ s₂ := by
  sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨hn, he, hw⟩ := leak_eq3 (by simp [bytesAt_length, h1]) (by simp [bytesAt_length, h3]) hl
  refine ⟨hsp.symm, fun r hr => ?_, a0.symm, fun i h1 hi => ?_, hn.symm, he.symm, hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    exacts [a1.symm, a2.symm, a3.symm, a4.symm]

section
variable {a s : State} (p : PubP a s)
include p

theorem PubP.pKk : kk s = kk a := by rw [kk, kk, p.g .a1 (by decide)]

theorem PubP.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .a0) = a.mem (a.gpr .a0) := by
  have e1 : kk s = kk a := p.pKk
  have := congrArg (·.getD 0 0) p.n
  rwa [bytesAt_getD _ _ hk, bytesAt_getD _ _ (by omega), BitVec.add_zero, BitVec.add_zero] at this

theorem PubP.pAny : anyL s = anyL a := by
  have e : ∀ x : BitVec 64, x <<< 32 >>> 32 = (x.setWidth 32).setWidth 64 := fun x => by
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  unfold anyL; rw [e, e, p.a0]

theorem PubP.pN0 (hk : 1 ≤ kk s) : n0 s = n0 a := by rw [n0, n0, p.byte hk]

theorem PubP.pLo (hk : 1 ≤ kk s) : lo s = lo a := by simp only [lo, smear, p.pN0 hk]

theorem PubP.pCm (hk : 1 ≤ kk s) : cm s = cm a := by rw [cm, cm, p.pLo hk]; simp only [smear, p.pN0 hk]

theorem PubP.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubP.pSp : Sp s = Sp a := p.args 1 (by decide) (by decide)

theorem PubP.agree {D : Nat} (hk : 1 ≤ kk s) : Agree Sp (vP D) a s := ⟨p.sp, p.pSp, fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [vP]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk
  · rw [dbLen, dbLen, p.pLo hk, p.g .a1 (by decide)]⟩

theorem PubP.agreeP {D : Nat} (hk : 1 ≤ kk s) : AgreeP D a s :=
  ⟨p.agree hk, p.pCm hk, p.g .a7 (by decide), p.pAny⟩

end

/-- `PubP`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubP a s ∧ 1 ≤ kk s

/-- `PubK` gives what the shared code needs. -/
theorem pssOk (D : Nat) : Ok Sp (vP D) (PreP D) PubK where
  fits P := P.fits
  agree p := p.1.agree p.2

/-! ## The call -/

section
variable {D : Nat}

/-- An entry state with the anchor's public data, and `Base` from it. -/
theorem pk_pins {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → ∃ s, PreP D s ∧ PubK (an x) s ∧ Base Sp (vP D) s t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ Reg.s0 :: fx := by decide) : Pins Φ rs :=
  pins_of (pssOk D) h rs hrs

theorem call_ct : RelCT isa (Two fun a t => ∃ s, PreP D s ∧ PubK a s ∧ AtCall D s t)
    Impl.RsaPkcs1Sig.RISCV64.pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩ => ⟨pdOk_of P₁ c₁, pdOk_of P₂ c₂,
    ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.base.sv.sp, c₂.base.sv.sp, fb, fb, p₁.1.sp, p₂.1.sp]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g0, c₂.g0, p₁.1.pSp, p₂.1.pSp]
    · rw [c₁.g1, c₂.g1, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g2, c₂.g2, p₁.1.args 3 (by decide) (by decide), p₂.1.args 3 (by decide) (by decide)]
    · rw [c₁.g3, c₂.g3, p₁.1.args 4 (by decide) (by decide), p₂.1.args 4 (by decide) (by decide)]
    · rw [c₁.g4, c₂.g4, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g5, c₂.g5, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g6, c₂.g6, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
    · rw [c₁.g7, c₂.g7, p₁.1.g _ (by decide), p₂.1.g _ (by decide)]
  · rw [c₁.a0, c₂.a0, p₁.1.pSp, p₂.1.pSp]
  · rw [c₁.a1, c₂.a1, p₁.1.args 2 (by decide) (by decide), p₂.1.args 2 (by decide) (by decide)]
  · rw [c₁.g2, c₂.g2, c₁.g3, c₂.g3, words_entry c₁.base.mem P₁.kp ((P₁.sp).sub_left (sc_sub P₁)) P₁.wp,
      words_entry c₂.base.mem P₂.kp ((P₂.sp).sub_left (sc_sub P₂)) P₂.wp, p₁.1.w, p₂.1.w]
  · rw [c₁.g4, c₂.g4, c₁.g5, c₂.g5,
      bytes_entry c₁.base.mem P₁.ke ((P₁.es.symm).sub_left (sc_sub P₁)) (by have := P₁.we; omega),
      bytes_entry c₂.base.mem P₂.ke ((P₂.es.symm).sub_left (sc_sub P₂)) (by have := P₂.we; omega), p₁.1.e, p₂.1.e]

end

/-! ## The function -/

/-- The checks passed, for an entry state. -/
structure Ck (D : Nat) (s : State) : Prop where
  h0 : s.mem (s.gpr .a0) ≠ 0
  em : D + 2 ≤ kk s - loN s
  fit : anyL s = 0 → (s.gpr .a7).toNat + 1 ≤ kk s - loN s - D - 1

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)

include hH hGl in
/-- After the call, from an entry state that passed the checks. -/
theorem bl_after {a s t : State} (P : PreP Gs.len s) (p : PubK a s) (c : AfterCall Gs.len s t)
    (C : Ck Gs.len s) : BL Gs.len a t ∧ Xa a t ∧ Fit Gs.len a := by
  have L := lay_reE P hH hGl c.mem C.h0 C.em
  have g := p.1.agreeP (D := Gs.len) p.2
  have hany : anyL (reE s t.mem) = anyL s := by unfold anyL; rw [reE_args P c.mem 0 (by decide)]
  have g' : AgreeP Gs.len a (reE s t.mem) :=
    ⟨⟨(reE_sp _ _).trans p.1.sp, (reE_Sp P c.mem).trans p.1.pSp, fun r hr => by
      rw [reE_vP P c.mem]; exact g.ag.v r hr⟩, (cm_reE P c.mem).trans g.cm, g.sl, hany.trans g.any⟩
  refine ⟨⟨reE s t.mem, L.canon, g', c.base⟩, c.xs.xa g', fun ha => ?_⟩
  have hk2 : kk s ≤ 1024 := P.k2
  have e4 : dbLen Gs.len s = dbLen Gs.len a := g.ag.v .s4 (by decide)
  have hdb : (dbLen Gs.len (reE s t.mem)).toNat = kk s - loN s - Gs.len - 1 := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e : dbLen Gs.len (reE s t.mem) = dbLen Gs.len s := by
    unfold dbLen; rw [reE_lo P c.mem]; rfl
  rw [← e4, ← e, hdb, ← p.1.g .a7 (by decide)]
  exact C.fit (by rw [p.1.pAny]; exact ha)

include hH cH hF hGh hGl hGv in
theorem main_ct : RelCT isa (Two fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Before Gs.len s t ∧ Ck Gs.len s)
    (verifyMain H) fun _ _ => True := by
  refine two_seq (Ψ := fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ AtCall Gs.len s t ∧ Ck Gs.len s)
    (pubArgs_taint (pk_pins (fun _ _ ⟨s, P, p, B, _⟩ => ⟨s, P, p, B.base⟩) []))
    (fun a t ⟨s, P, p, B, C⟩ => WP.mono (pubArgs_ok P B) fun t' c => ⟨s, P, p, c, C⟩) ?_
  refine two_seq (Ψ := fun a t => BL Gs.len a t ∧ Xa a t ∧ Fit Gs.len a)
    (call_ct.mono (fun _ _ ⟨a, ⟨s₁, P₁, p₁, c₁, _⟩, ⟨s₂, P₂, p₂, c₂, _⟩⟩ =>
      ⟨a, ⟨s₁, P₁, p₁, c₁⟩, ⟨s₂, P₂, p₂, c₂⟩⟩) fun _ _ h => h)
    (fun a t ⟨s, P, p, c, C⟩ => WP.mono (call_ok P c) fun t' c' => bl_after hH hGl P p c' C) ?_
  exact post_ct hH cH hF hGl.symm hGh hGl hGv

/-- After the entry, from an entry state with the anchor's public data. -/
abbrev En (D : Nat) (a t : State) : Prop := ∃ s, PreP D s ∧ PubK a s ∧ Entered D s t

include hH cH hF hGh hGl hGv in
theorem checks_ct : RelCT isa (Two (En Gs.len)) (checks H) fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have pin : ∀ {Φ : State → State → Prop}, (∀ a t, Φ a t → En Gs.len a t) → Pins Φ [] := fun h =>
    pk_pins (an := id) (fun a t hp => let ⟨s, P, p, E⟩ := h a t hp; ⟨s, P, p, E.base⟩) []
  -- The modulus' first byte.
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, p₁, E₁⟩ ⟨s₂, _, p₂, E₂⟩ => by
      rw [eval_zero, eval_zero, E₁.t1, E₂.t1, p₁.1.pN0 p₁.2, p₂.1.pN0 p₂.2])
    (fail_taint (pin fun _ _ h => h.1)) ?_
  let E1 := fun (a t : State) => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Entered Gs.len s t ∧ s.mem (s.gpr .a0) ≠ 0
  -- `emLen < hLen + 2`.
  refine two_seq (Ψ := fun a t => E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Gs.len + 2))
    (chkEm_taint H (pin fun _ _ h => h.1)) (fun a t ⟨⟨s, P, p, E⟩, hz⟩ => ?_) ?_
  · have h0 := n0_ne E (by rw [eval_zero] at hz; exact Option.some.inj hz)
    exact WP.mono (chkEm_ok P hGl hD64 E h0) fun t' ⟨E', r3⟩ =>
      ⟨⟨s, P, p, E', h0⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2]⟩
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩)) ?_
  let E2 := fun (a t : State) => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Entered Gs.len s t ∧
    s.mem (s.gpr .a0) ≠ 0 ∧ Gs.len + 2 ≤ kk s - loN s
  have e2 : ∀ {a t : State}, (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Gs.len + 2)) ∧
      isa.eval (.nonzero .a0) t = some false → E2 a t := fun {a t} ⟨⟨⟨s, P, p, E, h0⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have : ¬ kk a - loN a < Gs.len + 2 := by simpa using hc
    exact ⟨s, P, p, E, h0, by rw [p.1.pKk, p.1.pLoN p.2]; omega⟩
  -- The salt length expected.
  let E3 := fun (a t : State) => E2 a t ∧ t.gpr .a1 = if anyL a = 0 then a.gpr .a7 else 0
  have pin7 : Pins (fun (a t : State) => (E1 a t ∧ (t.gpr .a0 != 0) = decide (kk a - loN a < Gs.len + 2)) ∧
      isa.eval (.nonzero .a0) t = some false) [.s7] := fun a t₁ t₂ h₁ h₂ => by
    obtain ⟨s₁, P₁, p₁, E₁, -⟩ := e2 h₁
    obtain ⟨s₂, P₂, p₂, E₂, -⟩ := e2 h₂
    refine ⟨by rw [E₁.base.sv.sp, E₂.base.sv.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun r hr => ?_⟩
    rw [List.mem_singleton.mp hr, E₁.xs.s7, E₂.xs.s7, p₁.1.pAny, p₂.1.pAny]
  refine two_seq (Ψ := E3) (expLen_taint pin7) (fun a t h => ?_) ?_
  · obtain ⟨s, P, p, E, h0, hem⟩ := e2 h
    exact WP.mono (expLen_ok E.xs) fun t' ⟨o, e⟩ =>
      ⟨⟨s, P, p, E.only P o, h0, hem⟩, by rw [e, p.1.pAny, p.1.g .a7 (by decide)]⟩
  refine two_seq (Ψ := fun a t => E2 a t ∧ (t.gpr .a0 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .a7 else 0).toNat))
    (chkSalt_taint H (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1; ⟨s, P, p, E⟩))
    (fun a t ⟨⟨s, P, p, E, h0, hem⟩, h1⟩ => WP.mono (chkSalt_ok P hGl hD64 E h0 hem
      (by rw [h1, p.1.pAny, p.1.g .a7 (by decide)])) fun t' ⟨E', r3⟩ =>
        ⟨⟨s, P, p, E', h0, hem⟩, by rw [r3, p.1.pKk, p.1.pLoN p.2, p.1.pAny, p.1.g .a7 (by decide)]⟩) ?_
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (fail_taint (pin fun _ _ h => let ⟨s, P, p, E, _⟩ := h.1.1; ⟨s, P, p, E⟩)) ?_
  have e4 : ∀ {a t : State}, (E2 a t ∧ (t.gpr .a0 != 0) =
      decide (kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .a7 else 0).toNat)) ∧
      isa.eval (.nonzero .a0) t = some false →
      ∃ s, PreP Gs.len s ∧ PubK a s ∧ Before Gs.len s t ∧ Ck Gs.len s :=
    fun {a t} ⟨⟨⟨s, P, p, E, h0, hem⟩, c⟩, hc⟩ => by
    rw [eval_nonzero, c] at hc
    have hn : ¬ kk a - loN a - (Gs.len + 2) < (if anyL a = 0 then a.gpr .a7 else 0).toNat := by simpa using hc
    refine ⟨s, P, p, E.before, h0, hem, fun ha => ?_⟩
    rw [← p.1.pAny, ifp ha, ← p.1.g .a7 (by decide), ← p.1.pKk, ← p.1.pLoN p.2] at hn
    omega
  exact (main_ct hH cH hF hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, e4 h₁, e4 h₂⟩) fun _ _ h => h

include hH cH hF hGh hGl hGv in
/-- Two runs of `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` from entry states
with the same public data leak alike. -/
theorem code_ct : RelCT isa (Two fun a s => PreP Gs.len s ∧ PubK a s) (verifyPrecomputed H)
    fun _ _ => True := by
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine two_alloc (R := fun _ _ => True) ?_
  refine two_seq (Ψ := En Gs.len)
    (entry_taint H fun a u₁ u₂ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocd, h₁.2.1.sp,
      h₂.2.1.sp], fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]
        show (allocd _ s₁).gpr .a0 = (allocd _ s₂).gpr .a0
        simp only [allocd]
        exact (h₁.2.1.g .a0 (by decide)).trans (h₂.2.1.g .a0 (by decide)).symm⟩)
    (fun a u ⟨s, ⟨P, p⟩, e⟩ => by subst e; exact WP.mono (entry_ok P hGl.symm hD64) fun t E => ⟨s, P, p, E⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, PreP Gs.len s ∧ PubK a s ∧ Saves s t)
    (checks_ct hH cH hF hGh hGl hGv) fun a t ⟨s, P, p, E⟩ =>
      WP.mono (checks_done P hH hF hGh hGl hGv E) fun t' d => ⟨s, P, p, d.1⟩) ?_
  exact restore_taint fun a t₁ t₂ ⟨s₁, _, p₁, v₁⟩ ⟨s₂, _, p₂, v₂⟩ =>
    ⟨by rw [v₁.sp, v₂.sp, fb, fb, p₁.1.sp, p₂.1.sp], fun _ h => nomatch h⟩

end

end VG.Proof.RsaPss.RISCV64


namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64
open VG.Proof.RsaOaep.RISCV64 (HashCT FitsF stackBytes ct_mono sha1CT sha224CT sha256CT sha384CT sha512CT
  sha512_224CT sha512_256CT)

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include cH hF hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pre
      (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pub (verifyPrecomputed H) :=
  RelCT.constantTime ((code_ct hH cH hF hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preP_of h₁, pubP_refl s₁, by have := (preP_of h₁).k1; exact Nat.le_trans (by decide) this⟩,
      preP_of h₂, pubP_of hp, by have := (preP_of h₂).k1; exact Nat.le_trans (by decide) this⟩) fun _ _ h => h)

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` against its shared contract,
given a state meeting it. -/
theorem verify_verified (hsat : ∃ s, (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes).pre s) :
    Verified RISCV64.target (verifyPrecomputed H) (Spec.RsaPss.verifyPrecomputedContract Gs Gs abi stackBytes) :=
  ⟨code_correct hH hF hGh hGl hGv, code_constantTime hH cH hF hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting verification's contract for `H`: a 512-bit modulus, a
one-byte `e`, `H`'s digest, a 64-byte signature, a working space of 2080
words, 16 words of `pre` at `0x5000`, and the stack arguments at `sp`. -/
def verifySatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 64 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x4200 | .a5 => 0x4000 | .a6 => 64
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x1000A then 0x02
    else bif Nat.beq a.toNat 0x10010 then 0x20 else bif Nat.beq a.toNat 0x10011 then 0x08
    else bif Nat.beq a.toNat 0x10019 then 0x50 else bif Nat.beq a.toNat 0x10020 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, H.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10000, 40⟩]
  wr := [⟨0x20000, 16640⟩]

/-- The hash functions verification uses, as on the other targets. -/
def pssHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.md5, Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512,
    Spec.Mgf1.sha512_224, Spec.Mgf1.sha512_256]

theorem verify_sat {H : Spec.Mgf1.Hash} (hH : H ∈ pssHashes) :
    ∃ s, (Spec.RsaPss.verifyPrecomputedContract H H abi stackBytes).pre s := by
  simp only [pssHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi,
      argRegs, stackArgs_five, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.publicScratchWords,
      Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords, Spec.Rsa.precomputedWords, stackBytes]
      [verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySatState Spec.Mgf1.sha512_256

/-! ## The hash functions -/

theorem md5CT : HashCT Md5.ok where
  init := ct_mono Proof.Md5.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  upd := ct_mono Proof.Md5.RISCV64.Stream.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
  fin := ct_mono Proof.Md5.RISCV64.Stream.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

/-- A hash function's streaming functions, with what the proofs need. -/
structure Link (H : Hash) where
  ok : HashOK H
  ct : HashCT ok
  fits : FitsF H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  len : G.len = H.D
  mem : G ∈ pssHashes

theorem Link.valid {H : Hash} (l : Link H) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact l.ok.hD0, fun x => by rw [l.hash, l.ok.hashLen, l.len]⟩

def md5L : Link Md5.hash :=
  ⟨Md5.ok, md5CT, by decide, Spec.Mgf1.md5, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha1L : Link Sha1.hash :=
  ⟨Sha1.ok, sha1CT, by decide, Spec.Mgf1.sha1, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha224L : Link Sha256Family.hash224 :=
  ⟨Sha256Family.ok224, sha224CT, by decide, Spec.Mgf1.sha224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha256L : Link Sha256Family.hash256 :=
  ⟨Sha256Family.ok256, sha256CT, by decide, Spec.Mgf1.sha256, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha384L : Link Sha384.hash :=
  ⟨Sha384.ok, sha384CT, by decide, Spec.Mgf1.sha384, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512L : Link Sha512.hash :=
  ⟨Sha512.ok, sha512CT, by decide, Spec.Mgf1.sha512, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_224L : Link Sha512_224.hash :=
  ⟨Sha512_224.ok, sha512_224CT, by decide, Spec.Mgf1.sha512_224, fun _ => rfl, rfl, by simp [pssHashes]⟩
def sha512_256L : Link Sha512_256.hash :=
  ⟨Sha512_256.ok, sha512_256CT, by decide, Spec.Mgf1.sha512_256, fun _ => rfl, rfl, by simp [pssHashes]⟩

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed` for a linked hash function. -/
theorem link_verified {H : Hash} (l : Link H) :
    Verified RISCV64.target (Impl.RsaPss.RISCV64.verifyPrecomputed H)
      (Spec.RsaPss.verifyPrecomputedContract l.G l.G abi stackBytes) :=
  verify_verified l.ok l.ct l.fits l.hash l.len l.valid (verify_sat l.mem)

end VG.Proof.RsaPss.RISCV64

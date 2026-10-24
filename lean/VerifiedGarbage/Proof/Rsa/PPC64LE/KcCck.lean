module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBody
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkPre
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCk
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckCrtKey
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcChecks
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# `vg_rsa_check_crt_key` on PPC64LE: the checks of a valid public key

As `KcCk.lean`, without `d`. `CckRegs s0 t`: the pointers and lengths the
entry keeps. `cck_valid`: for a valid modulus and exponent, the arrays set
up, the numbers read and checked, and `checkCrtKey`'s bit returned in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)
open VG.Proof.Bignum.PPC64LE.Pub (sat)

/-- The pointers and lengths of `vg_rsa_check_crt_key`, kept by the entry. -/
structure CckRegs (s0 t : State) : Prop where
  r14 : t.gpr .r14 = s0.gpr .r3
  r15 : t.gpr .r15 = s0.gpr .r4
  r18 : t.gpr .r18 = s0.gpr .r7
  r19 : t.gpr .r19 = s0.gpr .r8
  r20 : t.gpr .r20 = s0.gpr .r9
  r21 : t.gpr .r21 = s0.gpr .r10
  r22 : t.gpr .r22 = PPC64LE.stackArg s0 0
  r23 : t.gpr .r23 = PPC64LE.stackArg s0 2
  r26 : t.gpr .r26 = PPC64LE.stackArg s0 4

/-- The registers `CckRegs` is about. -/
abbrev cckRegs : List Reg := [.r14, .r15, .r18, .r19, .r20, .r21, .r22, .r23, .r26]

theorem CckRegs.of_keep {s0 t u : State} (h : CckRegs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ cckRegs, r ∉ rs := by decide) : CckRegs s0 u := by
  have e : ∀ r ∈ cckRegs, u.gpr r = t.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r14, (e _ (by decide)).trans h.r15, (e _ (by decide)).trans h.r18,
    (e _ (by decide)).trans h.r19, (e _ (by decide)).trans h.r20, (e _ (by decide)).trans h.r21,
    (e _ (by decide)).trans h.r22, (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r26⟩

/-- `checkCrtKey` of the arguments. -/
abbrev cckOk (s0 : State) : Bool :=
  Spec.Rsa.checkCrtKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (s0.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (s0.gpr .r8).toNat)

theorem cck_valid {s0 s : State} (h0 : cckP.pre s0) (hb : KBase (cckB s0) (cckZ s0) s0 s) (hr : CckRegs s0 s)
    (h24 : s.gpr .r24 = BitVec.ofNat 64
      (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))) <<< 31)
    (hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))) (kK s0) = true)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))
      = true) :
    WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.PPC64LE.CheckCrtKey.loads ++
        (start ++ crtChecks) ++ ([.block ret] : List (Prog isa)))) s fun t =>
      KBase (cckB s0) (cckZ s0) s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (if cckOk s0 then 1 else 0) ∧
        Keep validRegs s t := by
  have hp := cck_kpre h0
  obtain ⟨-, hrd, -, dn, -, dpp, dq, ddp, ddq, dqi, -, wn, -, wp, wq, wdp, wdq, wqi, -, -, -, -,
    p1, p2, q1, q2, edp, eqi, edq, -⟩ := id h0
  obtain ⟨-, hw16, -, hkw⟩ := hp.ws
  have hK : (s0.gpr .r4).toNat = kK s0 := rfl
  rw [edp] at ddp wdp
  rw [eqi] at dqi wqi
  rw [edq] at ddq wdq
  have he' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat) < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hev; exact hev.2
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat) := by
    unfold sat; omega
  rw [hsat] at h24
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine prep_ok hp hb (by rw [hr.r15]; exact CrtValues.ofNat_toNat64 _) h24 he'
    (by simp [VG.Impl.Rsa.PPC64LE.CheckCrtKey.loads]) fun t0 l0 k0 => ?_
  have R0 := hr.of_keep k0
  simp only [VG.Impl.Rsa.PPC64LE.CheckCrtKey.loads, List.append_assoc]
  have hl : ∀ (a b : Reg) (j : Nat) (r : List (Prog isa)), r ≠ [] → ∀ {u : State} {Q : State → Prop},
      WP isa (seqs (loadR a b j)) u (fun t => WP isa (seqs r) t Q) → WP isa (seqs (loadR a b j ++ r)) u Q :=
    fun a b j r hr _ _ h => (wp_seqs_append (by simp [loadR]) hr).mpr h
  -- `n`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l0 (j := aN) (by decide) rfl (rP := .r14) (rL := .r15)
    (by decide) (by decide) (by decide) R0.r14 (by rw [R0.r15]; exact CrtValues.ofNat_toNat64 _)
    (by omega) (by omega) (by rw [hrd]; simp) dn wn) fun t1 ⟨l1, k1⟩ => ?_)
  have R1 := R0.of_keep k1
  -- `p`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l1 (j := aP) (by decide) rfl (rP := .r18) (rL := .r19)
    (by decide) (by decide) (by decide) R1.r18 (by rw [R1.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega) (by rw [hrd]; simp) dpp wp) fun t3 ⟨l3, k3⟩ => ?_)
  have R3 := R1.of_keep k3
  -- `q`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l3 (j := aQ) (by decide) rfl (rP := .r20) (rL := .r21)
    (by decide) (by decide) (by decide) R3.r20 (by rw [R3.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega) (by rw [hrd]; simp) dq wq) fun t4 ⟨l4, k4⟩ => ?_)
  have R4 := R3.of_keep k4
  -- `dP`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l4 (j := aDP) (by decide) rfl (rP := .r22) (rL := .r19)
    (by decide) (by decide) (by decide) R4.r22 (by rw [R4.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega) (by rw [hrd, edp]; simp) ddp wdp) fun t5 ⟨l5, k5⟩ => ?_)
  have R5 := R4.of_keep k5
  -- `dQ`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l5 (j := aDQ) (by decide) rfl (rP := .r23) (rL := .r21)
    (by decide) (by decide) (by decide) R5.r23 (by rw [R5.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega) (by rw [hrd, edq]; simp) ddq wdq) fun t6 ⟨l6, k6⟩ => ?_)
  have R6 := R5.of_keep k6
  -- `qInv`.
  refine hl _ _ _ _ (by simp [start]) (WP.mono (ldStep_ok l6 (j := aQI) (by decide) rfl (rP := .r26)
    (rL := .r19) (by decide) (by decide) (by decide) R6.r26 (by rw [R6.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega) (by rw [hrd, eqi]; simp) dqi wqi) fun t7 ⟨l7, k7⟩ => ?_)
  -- The checks.
  let g : Geo := ⟨cckB s0, cckZ s0, kK s0⟩
  let v : Vals := ⟨Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (s0.gpr .r8).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (s0.gpr .r8).toNat), 0⟩
  have a7 : Arrs t7.mem g.B g.w (vals v) live0 := fun j hj => by
    rw [l7.arrs.get (List.mem_range.mpr (by revert hj; revert j; decide))]
    simp only [live0, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [wp_seqs_append (by simp [start]) (by simp [crtChecks, eqA])]
  refine WP.mono (start_ok (g := g) (v := v) l7.ws a7 (l7.top _ (by decide))) fun t8 ⟨X₁, X₂, hX, g8⟩ => ?_
  rw [wp_seqs_append (by simp [crtChecks, eqA]) (by simp)]
  refine WP.mono (crtChecks_ok g8) fun t9 ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, g9⟩ => ?_
  rw [show seqs [.block ret] = .block ret from rfl]
  refine WP.mono (ret_ok g9) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · exact (g9.base l7.base hp.nowrap).of_regs kt tm
  · rw [t3]
    congr 2
    have e := cck_bits (k := kK s0) (w := g.w) hmv hev
      (lt_pow_of_len _ (by rw [len_bytes]; exact p2)) (lt_pow_of_len _ (by rw [len_bytes]; exact q2))
      (by omega) (pow_kw _) hX hR₁ hR₂ hR₃
    rw [show cckOk s0 = Spec.Rsa.crtKeyValid (kK s0) _ _ _ _ _ _ _ by
      simp only [cckOk, Spec.Rsa.checkCrtKey, len_bytes]; rfl, e]
  · exact ((((((((k0.trans k1).trans k3).trans k4).trans k5).trans k6).trans k7).trans
      g9.regs).trans kt).mono

end VG.Proof.Rsa.PPC64LE.KeyCheck

module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBody
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkPre
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcChecks
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# `vg_rsa_check_key` on PPC64LE: the checks of a valid public key

`CkRegs s0 t`: the pointers and lengths the entry keeps in `r14`–`r26`.
`ck_valid`: for a valid modulus and exponent, the arrays set up, the numbers
read and checked, and `checkKey`'s bit returned in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)
open VG.Proof.Bignum.PPC64LE.Pub (sat)

/-- The pointers and lengths of `vg_rsa_check_key`, kept by the entry. -/
structure CkRegs (s0 t : State) : Prop where
  r14 : t.gpr .r14 = s0.gpr .r3
  r15 : t.gpr .r15 = s0.gpr .r4
  r16 : t.gpr .r16 = s0.gpr .r7
  r17 : t.gpr .r17 = s0.gpr .r8
  r18 : t.gpr .r18 = s0.gpr .r9
  r19 : t.gpr .r19 = s0.gpr .r10
  r20 : t.gpr .r20 = PPC64LE.stackArg s0 0
  r21 : t.gpr .r21 = PPC64LE.stackArg s0 1
  r22 : t.gpr .r22 = PPC64LE.stackArg s0 2
  r23 : t.gpr .r23 = PPC64LE.stackArg s0 4
  r26 : t.gpr .r26 = PPC64LE.stackArg s0 6

/-- The registers `CkRegs` is about. -/
abbrev ckRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r26]

theorem CkRegs.of_keep {s0 t u : State} (h : CkRegs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ ckRegs, r ∉ rs := by decide) : CkRegs s0 u := by
  have e : ∀ r ∈ ckRegs, u.gpr r = t.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r14, (e _ (by decide)).trans h.r15, (e _ (by decide)).trans h.r16,
    (e _ (by decide)).trans h.r17, (e _ (by decide)).trans h.r18, (e _ (by decide)).trans h.r19,
    (e _ (by decide)).trans h.r20, (e _ (by decide)).trans h.r21, (e _ (by decide)).trans h.r22,
    (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r26⟩

/-- The registers the valid branch may change. -/
abbrev validRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r29, .r30]

/-- The numbers of `vg_rsa_check_key`'s arguments. -/
abbrev ckBytes (s0 : State) : List (List Byte) :=
  [Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat, Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat,
    Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat, Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat,
    Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat,
    Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat,
    Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 1).toNat,
    Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (s0.gpr .r10).toNat]

/-- `checkKey` of the arguments. -/
abbrev ckOk (s0 : State) : Bool :=
  Spec.Rsa.checkKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 1).toNat)
    (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (s0.gpr .r10).toNat)

theorem len_bytes (m : Mem) (p : Addr) (L : Nat) : (Spec.Rsa.bytesAt m p L).length = L := by
  simp [Spec.Rsa.bytesAt]

theorem ck_valid {s0 s : State} (h0 : ckP.pre s0) (hb : KBase (ckB s0) (ckZ s0) s0 s) (hr : CkRegs s0 s)
    (h24 : s.gpr .r24 = BitVec.ofNat 64
      (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))) <<< 31)
    (hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))) (kK s0) = true)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))
      = true) :
    WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.PPC64LE.CheckKey.loads ++
        (start ++ crtChecks ++ dChecks) ++ ([.block ret] : List (Prog isa)))) s fun t =>
      KBase (ckB s0) (ckZ s0) s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (if ckOk s0 then 1 else 0) ∧
        Keep validRegs s t := by
  have hp := ck_kpre h0
  obtain ⟨-, hrd, -, dn, -, dd, dpp, dq, ddp, ddq, dqi, -, wn, -, wd, wp, wq, wdp, wdq, wqi, -, -, -, -, d1, d2,
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
    unfold sat; omega_arith
  rw [hsat] at h24
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine prep_ok hp hb (by rw [hr.r15]; exact CrtValues.ofNat_toNat64 _) h24 he'
    (by simp [VG.Impl.Rsa.PPC64LE.CheckKey.loads]) fun t0 l0 k0 => ?_
  have R0 := hr.of_keep k0
  simp only [VG.Impl.Rsa.PPC64LE.CheckKey.loads, List.append_assoc]
  have hl : ∀ (a b : Reg) (j : Nat) (r : List (Prog isa)), r ≠ [] → ∀ {u : State} {Q : State → Prop},
      WP isa (seqs (loadR a b j)) u (fun t => WP isa (seqs r) t Q) → WP isa (seqs (loadR a b j ++ r)) u Q :=
    fun a b j r hr _ _ h => (wp_seqs_append (by simp [loadR]) hr).mpr h
  -- `n`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l0 (j := aN) (by decide) rfl (rP := .r14) (rL := .r15)
    (by decide) (by decide) (by decide) R0.r14 (by rw [R0.r15]; exact CrtValues.ofNat_toNat64 _)
    (by omega_arith) (by omega_arith) (by rw [hrd]; simp) dn wn) fun t1 ⟨l1, k1⟩ => ?_)
  have R1 := R0.of_keep k1
  -- `d`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l1 (j := aD) (by decide) rfl (rP := .r16) (rL := .r17)
    (by decide) (by decide) (by decide) R1.r16 (by rw [R1.r17]; exact CrtValues.ofNat_toNat64 _)
    d1 (by omega_arith) (by rw [hrd]; simp) dd wd) fun t2 ⟨l2, k2⟩ => ?_)
  have R2 := R1.of_keep k2
  -- `p`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l2 (j := aP) (by decide) rfl (rP := .r18) (rL := .r19)
    (by decide) (by decide) (by decide) R2.r18 (by rw [R2.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd]; simp) dpp wp) fun t3 ⟨l3, k3⟩ => ?_)
  have R3 := R2.of_keep k3
  -- `q`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l3 (j := aQ) (by decide) rfl (rP := .r20) (rL := .r21)
    (by decide) (by decide) (by decide) R3.r20 (by rw [R3.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega_arith) (by rw [hrd]; simp) dq wq) fun t4 ⟨l4, k4⟩ => ?_)
  have R4 := R3.of_keep k4
  -- `dP`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l4 (j := aDP) (by decide) rfl (rP := .r22) (rL := .r19)
    (by decide) (by decide) (by decide) R4.r22 (by rw [R4.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd, edp]; simp) ddp wdp) fun t5 ⟨l5, k5⟩ => ?_)
  have R5 := R4.of_keep k5
  -- `dQ`.
  refine hl _ _ _ _ (by simp) (WP.mono (ldStep_ok l5 (j := aDQ) (by decide) rfl (rP := .r23) (rL := .r21)
    (by decide) (by decide) (by decide) R5.r23 (by rw [R5.r21]; exact CrtValues.ofNat_toNat64 _)
    q1 (by omega_arith) (by rw [hrd, edq]; simp) ddq wdq) fun t6 ⟨l6, k6⟩ => ?_)
  have R6 := R5.of_keep k6
  -- `qInv`.
  refine hl _ _ _ _ (by simp [start]) (WP.mono (ldStep_ok l6 (j := aQI) (by decide) rfl (rP := .r26)
    (rL := .r19) (by decide) (by decide) (by decide) R6.r26 (by rw [R6.r19]; exact CrtValues.ofNat_toNat64 _)
    p1 (by omega_arith) (by rw [hrd, eqi]; simp) dqi wqi) fun t7 ⟨l7, k7⟩ => ?_)
  -- The checks.
  let g : Geo := ⟨ckB s0, ckZ s0, kK s0⟩
  let v : Vals := ⟨Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (s0.gpr .r4).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (s0.gpr .r10).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (s0.gpr .r8).toNat)⟩
  have a7 : Arrs t7.mem g.B g.w (vals v) live0 := l7.arrs.sub (by decide)
  rw [wp_seqs_append (by simp [start]) (by simp [crtChecks, eqA])]
  refine WP.mono (start_ok (g := g) (v := v) l7.ws a7 (l7.top _ (by decide))) fun t8 ⟨X₁, X₂, hX, g8⟩ => ?_
  rw [wp_seqs_append (by simp [crtChecks, eqA]) (by simp [dChecks, ltA])]
  have wl : (kK s0 + 3) / 4 ≤ 1024 := g8.ws.wle
  refine WP.mono (crtChecks_ok g8 ⟨(PPC64LE.stackArg s0 1).toNat, q1, by omega_arith, lt_pow8_of_len _ (len_bytes _ _ _),
    ((R6.of_keep k7).r21).trans (CrtValues.ofNat_toNat64 _)⟩) fun t9 ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, g9⟩ => ?_
  rw [wp_seqs_append (by simp [dChecks, ltA]) (by simp)]
  refine WP.mono (dChecks_ok g9) fun t10 ⟨Y₁, Y₂, hY₁, hY₂, A, live, g10⟩ => ?_
  rw [show seqs [.block ret] = .block ret from rfl]
  refine WP.mono (ret_ok g10) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · exact (g10.base l7.base hp.nowrap).of_regs kt tm
  · rw [t3]
    congr 2
    have e := ck_bits (k := kK s0) (w := g.w) hmv hev
      (lt_pow_of_len _ (by rw [len_bytes]; exact p2)) (lt_pow_of_len _ (by rw [len_bytes]; exact q2))
      (by omega_arith) (pow_kw _) hX hR₁ hR₂ hR₃ hY₁ hY₂
    rw [show ckOk s0 = Spec.Rsa.keyValid (kK s0) _ _ _ _ _ _ _ _ by
      simp only [ckOk, Spec.Rsa.checkKey, len_bytes]; rfl, e]
    rfl
  · exact (((((((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
      g10.regs).trans kt).mono

end VG.Proof.Rsa.PPC64LE.KeyCheck

module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreR2
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with the CRT on x86-64, with the key's precomputed values: correctness

`Crt.codeP` is `Crt.code` with `R² mod n` copied from the key's precomputed
values `pre` (`r2Pre`) and without the check of `p q = n` (`checksP`),
which `crtContractP` requires `pre` to be `privatePrecompute`'s, and so
implies: from a state that contract allows, it writes
`privateCrt` of its inputs, as `Crt.code` does (`crtCodeP_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## `main` -/

theorem nSetupP_eq (M : Mont) : nSetupP M.mm =
    (loadSteps ++ restSteps) ++ ([r2Pre] ++ [M.mm Public.aXm Public.aX Public.aR2]) := rfl

/-- `n`'s setup with `R² mod n` from `pre`, for a valid modulus. -/
theorem nPartP_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hp : PreR2 s B Z ((k + 7) / 8) (Spec.Rsa.os2ip nb)) :
    WP isa (seqs (nSetupP M.mm)) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  rw [nSetupP_eq]
  exact nPartWith_ok M _ h hv fun t₁ minv so hi k₁ =>
    r2Pre_ok so.good hZ (by omega_arith) (by omega_arith) so.r12 (by omega_arith)
      (hp.congr hi (k₁.gpr (by decide)) k₁.2.1 k₁.2.2)

/-- Up to the checks, for a valid modulus, with `R² mod n` from `pre`. -/
theorem frontP_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hp : PreR2 s B Z ((k + 7) / 8) (Spec.Rsa.os2ip nb))
    (hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    WP isa (seqs (nSetupP M.mm ++ primesSetup ++ checksP)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetupP]) (by simp [checksP]) (wp_seqs_append (by simp [nSetupP])
    (by simp [primesSetup]) (WP.mono (nPartP_ok M h hv hp) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPartP_ok h hv hr' hpq) fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

theorem crtMainP_eq (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) :
    Crt.mainP mul ex = seqs ((nSetupP mul ++ primesSetup ++ checksP) ++ (qPhase mul ex ++ pPhase mul ex ++ finish)) := by
  simp only [Crt.mainP, List.append_assoc]

/-- `mainP`, for a valid modulus: as `crtMain_ok`. -/
theorem crtMainP_ok (M : Mont) (E : CrtExpL M) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hp : PreR2 s B Z ((k + 7) / 8) (Spec.Rsa.os2ip nb))
    (hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    WP isa (Crt.mainP M.mm E.code) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  rw [crtMainP_eq]
  refine wp_seqs_append (by simp [nSetupP]) (by simp [qPhase]) (WP.mono (frontP_ok M h hv hp hpq)
    fun t₀ ⟨minv, mp, mq, hr⟩ => WP.mono (back_ok M E h hv hr rfl) fun t ht => ⟨_, ht, ?_⟩)
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## The precondition -/

/-- What `Crt.codeP` uses of its contract's precondition: `Crt.code`'s
(`CrtCtx`), and `R² mod n` in `pre` (`PreR2`), for a valid modulus. -/
theorem crtCtxP_of {s : State} (h : crtContractP.pre s) :
    CrtCtx s ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = true ∧
    PreR2 s (stackArg s 10) ((stackArg s 11).toNat * 8) (((s.gpr .rcx).toNat + 7) / 8)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) ∧
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) *
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) := by
  simp only [crtContractP] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOpr dOs dOa dns dis dps dqs ddps ddqs dqis dprs dsa
    dRo dRn dRi dRp dRq dRdp dRdq dRqi dRpr dRs dRa wO wN wI wP wQ wDp wDq wQi wS wPr hk hol hil hpl1 hpl2
    hql1 hql2 hdpl hqil hdql hsl hprl
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 10) ((stackArg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 112⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have hpre : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have hpq := VG.Proof.Rsa.privatePrecompute_mul h
  have hpub := VG.Proof.Rsa.privatePrecompute_public h
  rw [bytesAt_length, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hpub
  obtain ⟨hv, -, hval⟩ := pre_of_some (bytesAt_length _ _ _) hk1 hpub
  have hw2 : 2 * (((s.gpr .rcx).toNat + 7) / 8) ≤ (stackArg s 13).toNat := by
    rw [hprl]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega
  have hoff : ∀ d b : Nat, off (stackArg s 12) d + BitVec.ofNat 64 b = stackArg s 12 + BitVec.ofNat 64 (d + b) := by
    intro d b; simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by omega_arith, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 112) (by omega_arith) (by omega_arith))
      rw [← stackArgAddr_add s j b] at this; omega_arith)),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega_arith) (by rw [← hil]; exact dis),
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    src_of_region (by rw [hrd, ← hdpl]; simp) (by omega_arith) (by rw [← hdpl]; exact ddps),
    src_of_region (by rw [hrd, ← hdql]; simp) (by omega_arith) (by rw [← hdql]; exact ddqs),
    src_of_region (by rw [hrd, ← hqil]; simp) (by omega_arith) (by rw [← hqil]; exact dqis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ (by omega_arith) (by omega_arith)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega_arith) (by omega_arith)), fun b hb => ?_⟩, hv,
    ⟨⟨_, hargs, by rw [stackArgAddr_eq s 12]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun b hb => by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * 12 + b) (len := 112) (by omega_arith) (by omega_arith))
      rw [← stackArgAddr_add s 12 b] at this; exact this,
    fun j hj => ⟨_, hpre, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj b hb => by
      rw [hoff]; exact out_scr dprs (contains_byte _ (by omega_arith) (by omega_arith)),
    by rw [hval]⟩, hpq⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega_arith) (by omega_arith)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega_arith) (by omega_arith))⟩

/-- `wordsAt`'s words, `toWords V n`, as the number `V`. -/
theorem wv_of_toWords {m : Mem} {p : Addr} {c n V : Nat}
    (h : Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * c)) n = Spec.Rsa.toWords V n) (hV : V < 2 ^ (64 * n)) :
    wv m p (8 * c) n = V := by
  rw [← Nat.mod_eq_of_lt hV]
  refine wv_of_words fun i hi => ?_
  have := congrArg (fun l => l[i]?) h
  simp only [Spec.Rsa.wordsAt, Spec.Rsa.toWords, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  show (m.readW (p + BitVec.ofNat 64 (8 * c + 8 * i)) 64).toNat = _
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, this, BitVec.toNat_ofNat]

/-- `n` words of `pre` from `k`, of the `L` it has, outside the working space. -/
theorem preW_of {s : State} {B : Addr} {Z k n V L : Nat}
    (hargs : (⟨stackArgAddr s 0, 112⟩ : Region) ∈ s.rd ++ s.wr)
    (hpre : (⟨stackArg s 12, L * 8⟩ : Region) ∈ s.rd ++ s.wr) (wPr : (stackArg s 12).toNat + L * 8 ≤ 2 ^ 64)
    (hkn : k + n ≤ L) (dprs : (⟨stackArg s 12, L * 8⟩ : Region).Disjoint ⟨B, Z⟩)
    (dsa : (⟨B, Z⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩)
    (hv : wv s.mem (stackArg s 12) (8 * k) n = V) : PreW s B Z k n V := by
  have hoff : ∀ d b : Nat, off (stackArg s 12) d + BitVec.ofNat 64 b = stackArg s 12 + BitVec.ofNat 64 (d + b) := by
    intro d b; simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨⟨_, hargs, by rw [stackArgAddr_eq s 12]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun b hb => ?_, fun j hj => ⟨_, hpre, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun j hj b hb => by rw [hoff]; exact out_scr dprs (contains_byte _ (by omega_arith) (by omega_arith)), hv⟩
  have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * 12 + b) (len := 112) (by omega_arith) (by omega_arith))
  rw [← stackArgAddr_add s 12 b] at this; exact this

/-- `R_p² mod p` and `R_q² mod q` in `pre`, after the modulus' values (`PreW`). -/
theorem crtPrimes_of {s : State} (h : crtContractP.pre s) :
    PreW s (stackArg s 10) ((stackArg s 11).toNat * 8) (2 * (((s.gpr .rcx).toNat + 7) / 8))
      (Spec.Rsa.primeWords (stackArg s 1).toNat)
      (2 ^ (128 * Spec.Rsa.primeWords (stackArg s 1).toNat) %
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) ∧
    PreW s (stackArg s 10) ((stackArg s 11).toNat * 8)
      (2 * (((s.gpr .rcx).toNat + 7) / 8) + Spec.Rsa.primeWords (stackArg s 1).toNat)
      (Spec.Rsa.primeWords (stackArg s 3).toNat)
      (2 ^ (128 * Spec.Rsa.primeWords (stackArg s 3).toNat) %
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)) := by
  obtain ⟨c, hv, -, hpq⟩ := crtCtxP_of h
  have hk1 := c.hk1
  simp only [crtContractP] at h
  sig_split h
  rename_i hsp hrd hwr dOn dOi dOp dOq dOdp dOdq dOqi dOpr dOs dOa dns dis dps dqs ddps ddqs dqis dprs dsa
    dRo dRn dRi dRp dRq dRdp dRdq dRqi dRpr dRs dRa wO wN wI wP wQ wDp wDq wQi wS wPr hk hol hil hpl1 hpl2
    hql1 hql2 hdpl hqil hdql hsl hprl
  have hargs : (⟨stackArgAddr s 0, 112⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have hpre : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain ⟨eP, eQ⟩ := VG.Proof.Rsa.privatePrecompute_primes (m := s.mem) (pre := stackArg s 12)
    (nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (pB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (qB := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (by rw [bytesAt_length, bytesAt_length, bytesAt_length, ← hprl]; exact h)
  unfold Spec.Rsa.primeR2 at eP eQ
  rw [bytesAt_length, bytesAt_length, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at eP eQ
  rw [bytesAt_length] at eQ
  have hw : (stackArg s 13).toNat = 2 * (((s.gpr .rcx).toNat + 7) / 8) + Spec.Rsa.primeWords (stackArg s 1).toNat +
      Spec.Rsa.primeWords (stackArg s 3).toNat := by
    rw [hprl]; unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; rfl
  have hN0 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ≠ 0 := by
    have := (valid_facts hv hk1).2.1; omega_arith
  clear dOn dOi dOp dOq dOdp dOdq dOqi dOpr dOs dOa dns dis dps dqs ddps ddqs dqis
    dRo dRn dRi dRp dRq dRdp dRdq dRqi dRpr dRs dRa wO wN wI wP wQ wDp wDq wQi wS hk hol hil hpl1
    hql1 hdpl hqil hdql hsl hprl h c
  have hlt : ∀ {l : Nat} (pa : Addr), l < (s.gpr .rcx).toNat → 0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem pa l) →
      2 ^ (128 * Spec.Rsa.primeWords l) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem pa l) <
        2 ^ (64 * Spec.Rsa.primeWords l) := fun {l} pa _ h0 => by
    refine Nat.lt_of_lt_of_le (Nat.mod_lt _ h0) (Nat.le_trans
      (Nat.le_of_lt (show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem pa l) < 2 ^ (8 * l) from ?_))
      (Nat.pow_le_pow_right (by decide) (by unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega)))
    have := os2ip_lt (Spec.Rsa.bytesAt s.mem pa l)
    rwa [bytesAt_length, pow256_eq] at this
  rw [hw] at hpre dprs wPr
  refine ⟨preW_of hargs hpre wPr (by omega) dprs dsa (wv_of_toWords eP (hlt _ hpl2 ?_)),
    preW_of hargs hpre wPr (by omega) dprs dsa (wv_of_toWords eQ (hlt _ hql2 ?_))⟩
  · exact Nat.pos_of_ne_zero fun h0 => hN0 (by rw [← hpq, h0, Nat.zero_mul])
  · exact Nat.pos_of_ne_zero fun h0 => hN0 (by rw [← hpq, h0, Nat.mul_zero])

/-! ## The code -/

/-- `vg_rsa_private_crt_precomputed` with Montgomery multiplication `M`,
given that its code never loads MXCSR (which the registration file
evaluates). -/
theorem crtCodeP_correct (M : Mont) (E : CrtExpL M)
    (hmx : (Crt.codeP M.mm E.code).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContractP.pre s) :
    ∃ t s', Exec isa (Crt.codeP M.mm E.code) s t s' ∧ abiPreserved s s' ∧ crtContractP.post s s' := by
  obtain ⟨c, hv, hp, hpq⟩ := crtCtxP_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (Crt.codeP M.mm E.code) s fun s' => gprPreserved s s' ∧ crtContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Crt.codeP
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (crtHead_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := crtPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  have hp₂ := hp.congr (by rw [hm₂]; exact h₁.inScr) (kk.gpr (by decide)) kk.2.1 kk.2.2
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun _ => ?_)
  · exact absurd hb (by rw [hv]; decide)
  · exact WP.mono (crtMainP_ok M E hpre hv hp₂ hpq) fun t ⟨Mk, hp, hiff⟩ => crtCode_fin c h₁ hm₂ k₂ hp
      (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64

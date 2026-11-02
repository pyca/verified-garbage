module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignBody
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Fn.lean`). `sign_correct`:
`vg_dsa_sign` meets `sContract`. After `entry` (`sfront_ok`), `checkSignKey`
(`checkSignKey_ok`: the domain's checks and `1 < y < p`) either runs `body`
(`sbody_ok`) or `zeroOut` (`szero_ok`), and `restore` gives back the
callee-saved registers (`sfinish_ok`); the result is the specification's by
`Proof/Dsa/Accepted.lean`'s `signBytes_compute`. The specification's
`y^q mod p = 1` needs no check of its own: with the domain's `g^q mod p = 1`
it follows from `g^x mod p = y`, which `body` checks (`signChecks_iff`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)

/-- `y^q mod p = 1` from `g^q mod p = 1` and `g^x mod p = y`. -/
theorem pow_order_of_gen {p q g x y : Nat} (hp : 1 < p) (hg : g ^ q % p = 1) (hy : g ^ x % p = y) :
    y ^ q % p = 1 := by
  subst hy
  rw [← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, hg, Nat.one_pow,
    Nat.mod_eq_of_lt hp]

/-- With the domain's checks and `1 < y < p`, the public key's checks hold
whenever signing's do: `y^q mod p = 1` follows from `g^x mod p = y`. -/
theorem signChecks_iff {p q g y x k z : Nat} (hg : 1 < g ∧ g < p) (hd : (p - 1) % q = 0)
    (hgq : g ^ q % p = 1) (hy : 1 < y ∧ y < p) :
    (VG.Proof.Dsa.publicChecks p q g y ∧ SignOk p q g y x k z) ↔ SignOk p q g y x k z :=
  ⟨fun h => h.2, fun h => ⟨⟨⟨hg, hy⟩, hd, hgq, pow_order_of_gen (by omega) hgq h.2.2.1⟩, h⟩⟩

/-- The domain passes its checks and `1 < y < p`: what `checkSignKey`
checks. -/
abbrev SignKeyOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  ParamsOk m L key ∧ (1 < yOf m L key ∧ yOf m L key < pOf m L key)

/-- `Sign.checkSignKey rest fail` runs `rest` exactly when the domain passes
the specification's checks and `1 < y < p` (`SignKeyOk`), leaving what
`checkKey` leaves (`Checked`); else `fail`. -/
theorem checkSignKey_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, SignKeyOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ SignKeyOk s.mem L key → Kept L s.mem t.mem → Regs t L key sig → ScrL t L →
      Keep ckRegs s t → WP isa fail t Q) :
    WP isa (Sign.checkSignKey rest fail) s Q := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  have hqZ : L.qOff ≤ L.Z := by have := hbuf; simp only [Lay.bOff] at this; omega
  have e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold Sign.checkSignKey
  refine checkParams_ok hL hs hr hlen hd (hk.take (by omega)) (fun t hP hc hb kc => ?_)
    (fun t hn hb hrt hst kc => hfail t (fun hK => hn hK.1) hb hrt hst (keepPre (keepPre kc)))
  have hpo : pOf s.mem L key % 2 = 1 := hP.1.2.2
  have hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hP.1.1).1
  unfold andThen
  refine WP.seq (WP.seq (WP.mono (ptrY_ok hc.scr hL hc.regs) fun t₇ ⟨⟨b7, b8, m₇⟩, k₇⟩ => ?_))
  have k₀₇ := kc.trans k₇
  have hk₇ := hk.keep k₀₇.2.1 k₀₇.2.2
  have C₇ : Checked s t₇ L key sig d := hc.elem hL k₇ (by decide) (k₇.gpr (by decide)) (hc.inp.keep k₇)
    (by rw [m₇]; exact Outside.refl _ _ _ _)
  have he := hk₇.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)
  have en := C₇.inp.env
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := off key (2 * L.pl + L.ql)) (by decide)
      (by rw [b7]; exact (BitVec.add_zero _).symm) b8 (by omega) (by omega) he.rd
      (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx hqZ)))
    fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  have e1' : Env s₁ L.S L.qOff L.wp :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, en.w48,
      en.hZ⟩
  have A0 : wordsVal s₁.mem L.S (slot L.wp 0) L.wp = pOf s.mem L key := by
    rw [o1.wordsVal (by omega) (by omega_arith)]; exact C₇.p0
  refine WP.mono (elemRange_ok e1' top4) fun t₈ ⟨⟨r0, _, o2, e2⟩, k2⟩ => ?_
  have K₇ : Kept L s.mem t₇.mem := by rw [m₇]; exact hb
  have ey : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₇.mem (off key (2 * L.pl + L.ql)) L.pl) = yOf s.mem L key :=
    y_kept hk K₇
  rw [v4, A0, ey] at r0
  have o12 := p_elem2 o1 o2
  have k12 := k1.trans k2
  have ip₈ : InP t₈ L := ⟨e2, (k12.gpr (by decide)).trans C₇.inp.s6⟩
  have C₈ : Checked s t₈ L key sig d := C₇.elem hL k12 (by decide) (k12.gpr (by decide)) ip₈ o12
  have K₈ := K₇.trans (Kept.ofBody hL (p_arrays_body hL o12))
  have k₀₈ : Keep ckRegs s t₈ := (k₀₇.trans k12).mono fun r h => by
    simp only [ckRegs, elemRegs, List.mem_append] at h ⊢
    rcases h with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb₈ => ?_) (fun hb₈ => hfail t₈ (fun hK => by
      rw [r0.mpr hK.2] at hb₈
      exact absurd hb₈ (by decide)) K₈ C₈.regs C₈.scr k₀₈)
  exact hrest t₈ ⟨hP, r0.mp (beq_iff_eq.mp hb₈)⟩ C₈ K₈ k₀₈

/-- The registers `Sign.zeroOut` writes. -/
def szeroRegs : List Reg := [.t4, .t5, .s0] ++ zeroLoopRegs ++ [.a0]

/-- `zeroOut`: `out`'s `2 q_len` octets (`out` from the header's `Sign.hOut`)
:= 0, and `a0 := 0`. -/
theorem szero_ok {s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key x)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64) :
    WP isa Sign.zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) = List.replicate (2 * L.ql) 0 ∧
        Outside out 0 (2 * L.ql) s.mem t.mem ∧ t.gpr .a0 = 0) ∧ Keep szeroRegs s t := by
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  obtain ⟨hin24, hal24⟩ := ScrL.hdr hs hL (d := 24) (by decide) (by decide)
  unfold Sign.zeroOut
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = out ∧ u.mem = s.mem)
    (by brun [Sign.hOut, hr.s6, hin24, hal24]; exact hw) (by decide) (by rfl)) fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun v ⟨⟨b5, mv⟩, kv⟩ => ?_
  refine WP.mono (WP.keep [.t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (2 * L.ql) ∧
      u.gpr .s0 = 0 ∧ u.mem = v.mem)
    (by
      brun [b5, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, a0, m1'⟩, k1'⟩ => ?_
  have k1 := (ku.trans kv).trans k1'
  have m1 : s₁.mem = s.mem := by rw [m1', mv, mu]
  have a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans k1') |>.gpr (by decide)]; exact a4
  refine WP.seq (WP.mono (zeroLoop_ok (N := 2 * L.ql) (by omega) (by omega)
      (fun i hi => by rw [k1.2.2]; exact hout i hi) hno a0 a4₁ a5)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl))
    fun u ⟨⟨u0, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m1]; exact tout, u0⟩,
      ((k1.trans tk).trans ku).mono (by decide)⟩

theorem sign_correct (s : State) (h : sContract.pre s) :
    ∃ tr t, Exec isa Sign.sign s tr t ∧ abiPreserved s t ∧ sContract.post s t := by
  show WP isa Sign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  suffices main : WP isa Sign.sign s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ sContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hnwS := hL.nowrap
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -, -, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .a2) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .a3).isLt (by omega)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      Src t (slayOf s) (s.gpr .a2) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega)
  have srcN := mkSrc (A := s.gpr .a5) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .a6).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .a7) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .a0) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .a1).isLt (by omega)
  have hno : (s.gpr .a0).toNat + 2 * (slayOf s).ql ≤ 2 ^ 64 := by rw [← h1]; exact nwO
  have hout : ∀ t : State, t.wr = s.wr → ∀ i < 2 * (slayOf s).ql, InRegions t.wr (off (s.gpr .a0) i) 1 :=
    fun t ht i hi => ⟨_, by rw [ht, hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  -- A change in `out` keeps `scratch`'s header.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .a0) 0 (2 * (slayOf s).ql) m m' →
      ∀ {d : Nat}, d + 8 ≤ 256 → word m' (slayOf s).S d = word m (slayOf s).S d := fun ho d hd =>
    in_word (out_in (o := 0) (N := 2 * (slayOf s).ql)
      (by simpa only [off, BitVec.add_zero] using ho) (by omega) (by omega) (srcO s rfl rfl).sep)
      (by omega) (by omega)
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .a2), qOf s.mem (slayOf s) (s.gpr .a2), gOf s.mem (slayOf s) (s.gpr .a2)⟩,
        yOf s.mem (slayOf s) (s.gpr .a2), some (xOf s.mem (slayOf s) (s.gpr .a2))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega)]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2))
            (xOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .a2))
              (qOf s.mem (slayOf s) (s.gpr .a2)) (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .a2)) (xOf s.mem (slayOf s) (s.gpr .a2))
              (kOf s.mem (slayOf s) (s.gpr .a5))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
                (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5)))))
        else none := fun {n} hs hq8 => by
    have hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .a5))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h3) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  unfold Sign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 13, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
  have hal' : ∀ i < 13, (off (savW (stackArg s 1)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact F.scr.al8 (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  have hsav' : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (stackArg s 1) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have hwo : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S Sign.hOut = s.gpr .a0 :=
    fun u hu => (hu.word (Or.inr ⟨by simp only [Sign.hOut, hLens]; omega, by simp only [Sign.hOut]; omega⟩)).trans F.outw
  have hwd : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S hDigest = s.gpr .a7 :=
    fun u hu => (hu.word (Or.inl (by simp only [hDigest, hLens]; omega))).trans F.dig
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept (srcK3 s rfl rfl) Out₁
  have hKs : SignKeyOk s₁.mem (slayOf s) (s.gpr .a2) ↔ SignKeyOk s.mem (slayOf s) (s.gpr .a2) := by
    simp only [SignKeyOk, ParamsOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (checkSignKey_ok hL F.scr F.regs F.lens (by omega) (srcK3 s₁ k₁.2.1 k₁.2.2)
    (fun t hK hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have hKt := hKs.mp hK
    have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
    have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) =
        8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) := by
      have := hKt.1.1.1; unfold Spec.Dsa.supportedSizes at this; omega
    refine WP.mono (sbody_ok hL hK.1 hc Kd (srcK t kt.2.1 kt.2.2) (srcN t kt.2.1 kt.2.2) (by omega)
      ((srcD t kt.2.1 kt.2.2).take (Nat.min_le_left _ _)) (hwd t Kd) (hwo t Kd) (hout t kt.2.2) hno
      (srcO t kt.2.1 kt.2.2)) fun u ⟨⟨ob, r0u, ⟨m, Km, Om⟩, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h6u (hwr' u scru) hal'
      (fun i hi => (outSep Om (by simp only [saveOff]; omega)).trans
        ((Km.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)).trans (hsav' t Kd i hi))))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    have ex : xOf t.mem (slayOf s) (s.gpr .a2) = xOf s.mem (slayOf s) (s.gpr .a2) := by
      simp only [xOf]
      rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega)).bytes Ot
        (by omega)]
    have ek : kOf t.mem (slayOf s) (s.gpr .a5) = kOf s.mem (slayOf s) (s.gpr .a5) := by
      simp only [kOf]; rw [(srcN s rfl rfl).bytes Ot (by omega)]
    rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r0u
    have ed : Spec.Rsa.bytesAt t.mem (s.gpr .a7)
        (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) =
        Spec.Rsa.bytesAt s.mem (s.gpr .a7)
          (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) := by
      have := hKt.1.1.1; unfold Spec.Dsa.supportedSizes at this
      rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) =
        min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) by omega]
      exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).bytes Ot (by omega)
    rw [ed] at ob r0u
    have hres := hspec hKt.1.1 hq8
    simp only [signChecks_iff hKt.1.2.1 hKt.1.2.2.1 hKt.1.2.2.2 hKt.2] at hres
    refine ⟨?_, ?_⟩
    · rw [w0, r0u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h1, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    refine WP.mono (szero_ok hL scrt hrt (hwo t Kd) (hout t kt.2.2) hno) fun u ⟨⟨ub, uo, u0⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2)) hal'
      (fun i hi => (outSep uo (by simp only [saveOff]; omega)).trans (hsav' t Kd i hi)))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    have hn' : ¬ SignKeyOk s.mem (slayOf s) (s.gpr .a2) := fun hx => hn (hKs.mpr hx)
    have hres : sRes s = none := by
      by_cases hs : VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
      · have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) =
            8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) := by
          have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega
        rw [hspec hs hq8]
        split
        · rename_i hx
          exact absurd ⟨⟨hs, hx.1.1.1, hx.1.2.1, hx.1.2.2.1⟩, hx.1.1.2⟩ hn'
        · rfl
      · exact VG.Proof.Dsa.signBytes_invalid_shape (by rw [hkey]; exact hs)
    refine ⟨?_, ?_⟩
    · rw [w0, u0, hres]; rfl
    · rw [wm, h1, ub, hres]; rfl

end VG.Proof.Dsa.RISCV64

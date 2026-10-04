import VerifiedGarbage.Proof.Bignum.X86_64.IfmaBranch
import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain

/-!
# RSA with AVX512_IFMA on x86-64: the computation for a valid modulus

`main`: `vg_rsa_private_crt`'s front, then the IFMA branch for a modulus of
32 words and primes of 16 (`sizes`), the CRT one otherwise, and its finish.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem ofNat_eq_iff {n v : Nat} (hn : n < 2 ^ 64) (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 n = BitVec.ofNat 64 v ↔ n = v :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hv] at this,
   fun h => h ▸ rfl⟩

/-- `(len + 7) / 8 = 16`, for the workspace of a prime of `len` bytes. -/
theorem sz_iff {l : Nat} (hl : l < 2 ^ 60) :
    ((BitVec.ofNat 64 l + 7) >>> 3 ^^^ 16 = 0#64) ↔ wsWords l = 16 := by
  rw [BitVec.xor_eq_zero_iff, BitVec.toNat_inj.symm, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  unfold wsWords
  simp only [show (7 : BitVec 64).toNat = 7 from rfl, show (16 : BitVec 64).toNat = 16 from rfl]
  rw [Nat.mod_eq_of_lt (a := l) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `sizes`: ZF exactly if `n` has 32 words and `p` and `q` 16. -/
theorem sizes_ok {t : State} {B : Addr} {Z w pl ql : Nat} {minv : BitVec 64}
    (hg : Good t B Z w minv) (hpl : word t.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hZ : 8 * 32 ≤ Z) (hw : w < 2 ^ 64)
    (hpl' : pl < 2 ^ 60) (hql' : ql < 2 ^ 60) :
    WP isa (.block CrtIfma.sizes) t fun t' =>
      t'.zf = some (decide (w = 32 ∧ wsWords pl = 16 ∧ wsWords ql = 16)) ∧ t'.mem = t.mem ∧
        Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.zf = some (decide (w = 32 ∧ wsWords pl = 16 ∧ wsWords ql = 16)) ∧ t'.mem = t.mem) (by
      xrun [CrtIfma.sizes, State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl sPlen (by decide),
        hl sQlen (by decide), hg.hdr.hw, hpl, hql]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
        show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ofNat_eq_iff hw (by decide), sx7, sz_iff hpl',
        sz_iff hql', and_assoc]) rfl) fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

theorem mx_ffff (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_and]
  have : (0xFFFF : BitVec 32).getLsbD (6 + i) = true := by
    rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; omega
  rw [this, Bool.and_true]

/-- The checks' state, across a change of `rax` and `rdx` only. -/
theorem CrtReady.of_regs {s t t' : State} {B : Addr} {Z w pl ql : Nat} {minv mp mq : BitVec 64} {N C P Q : Nat}
    {M : Bool} (h : CrtReady s t B Z w pl ql minv mp mq N C P Q M) (hm : t'.mem = t.mem)
    (k : Keep [.rax, .rdx] t t') : CrtReady s t' B Z w pl ql minv mp mq N C P Q M := by
  have hx : ∀ {X : Nat} {o wx : Nat} {mx : BitVec 64}, XVals t B o wx mx X → XVals t' B o wx mx X :=
    fun hx => by rw [show t' = { t' with mem := t.mem } by rw [← hm]]; exact ⟨hx.n, hx.inv, hx.one⟩
  have hN : NVals t' B w minv N := by
    rw [show t' = { t' with mem := t.mem } by rw [← hm]]
    exact ⟨h.nv.n, h.nv.inv, h.nv.r2, h.nv.r2lt, h.nv.one⟩
  exact ⟨⟨h.good.scr.congr k.2.2, (k.gpr (by decide)).trans h.good.rdi, hm ▸ h.good.hdr⟩, hN, hm ▸ h.xm,
    hm ▸ h.msk, hm ▸ h.wsP, hm ▸ h.wsQ, hm ▸ h.pws, hx h.pxv, hm ▸ h.pmask, hm ▸ h.qws, hx h.qxv,
    hm ▸ h.hfix, hm ▸ h.iscr, (h.keep.trans k).mono (by simp [mmRegs])⟩

theorem ifmaMain_eq (mul : Nat → Nat → Nat → Prog isa) : CrtIfma.main mul =
    seqs ((nSetup mul ++ primesSetup ++ checks) ++ (([.block CrtIfma.sizes,
      .ite .e (seqs (CrtIfma.pre mul ++ CrtIfma.ifma ++ CrtIfma.post mul)) (seqs (qPhase mul ++ pPhase mul))] :
        List (Prog isa)) ++ finish)) := by
  simp only [CrtIfma.main, List.append_assoc]

/-- The IFMA area fits in the working space the contract asks for. -/
theorem ifmaZ_of {Z k pl : Nat} (hzk : 128 * k ≤ Z) (hw : (k + 7) / 8 = 32) (hp : wsWords pl = 16) : offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16 + 2 * CrtIfma.D + 8 ≤ Z := by
  unfold offQ slot wsWords hdrBytes tabBytes CrtIfma.D at *; omega

/-- `main`, for a valid modulus: `privateCrt`'s result as `vg_rsa_private_crt`
leaves it, and MXCSR's control bits. -/
theorem ifmaMain_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfma.main M.mm) s fun t => (∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  rw [ifmaMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp) (WP.mono_mx hfront (front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => ?_)
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hql8 := hdr_lt_slot (wsWords ql) 8 (show 31 < 32 by decide)
  refine wp_seqs_append (by simp) (by simp [finish]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono_mx (by decide) (sizes_ok (pl := pl) (ql := ql) hr.good
    (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
    (by unfold offQ at hZq; omega) (by omega) (by omega) (by omega))
    fun t₁ ⟨zf, me, k₁⟩ mx₁ => ?_)
  have hr₁ := hr.of_regs me k₁
  refine WP.mono (Q := fun (t : State) => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10)
    (WP.ite _ zf (fun hb => ?_) (fun hb => ?_)) fun t₂ ⟨hp, mx₂⟩ => ?_
  · simp only [decide_eq_true_eq] at hb
    obtain ⟨hw, hp, hq⟩ := hb
    exact wp_seqs_append (by simp [CrtIfma.pre, Crt.gPow]) (by simp [CrtIfma.post, copyArr])
      (WP.mono (branchA_ok M h hv hr₁ rfl hw hp hq (ifmaZ_of h.zk hw hp) hpre) fun t ⟨hd, mxa⟩ =>
        WP.mono (branchB_ok M h hv hd rfl hw hp hq hpost) fun t' ⟨hd', mxb⟩ =>
          ⟨hd', by rw [mxb, mxa, mx_ffff, mx₁, mx₀]⟩)
  · exact WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) (WP.mono (qPart_ok M h hv hr₁ rfl)
      fun _ hq => pPart_ok M h hv hq rfl)) fun t hp' mxc => ⟨hp', by rw [mxc, mx₁, mx₀]⟩
  · refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.X86_64

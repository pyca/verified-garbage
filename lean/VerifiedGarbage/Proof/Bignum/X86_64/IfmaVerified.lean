import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPre
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaMain`. -/
section

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
    (hg : Good t B Z w minv) (hpl : VG.Proof.Bignum.X86_64.word t.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : VG.Proof.Bignum.X86_64.word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hZ : 8 * 32 ≤ Z) (hw : w < 2 ^ 64)
    (hpl' : pl < 2 ^ 60) (hql' : ql < 2 ^ 60) :
    WP isa (.block CrtIfma.sizes) t fun t' =>
      t'.zf = some (decide (w = 32 ∧ wsWords pl = 16 ∧ wsWords ql = 16)) ∧ t'.mem = t.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.zf = some (decide (w = 32 ∧ wsWords pl = 16 ∧ wsWords ql = 16)) ∧ t'.mem = t.mem) (by
      xrun [CrtIfma.sizes, State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl sPlen (by decide),
        hl sQlen (by decide), hg.hdr.hw, hpl, hql]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
        show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, VG.Proof.Bignum.X86_64.ofNat_eq_iff hw (by decide), sx7, VG.Proof.Bignum.X86_64.sz_iff hpl',
        VG.Proof.Bignum.X86_64.sz_iff hql', and_assoc]) rfl) fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

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
    (k : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] t t') : CrtReady s t' B Z w pl ql minv mp mq N C P Q M := by
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
        List (Prog isa)) ++ VG.Impl.Rsa.X86_64.Crt.finish)) := by
  simp only [CrtIfma.main, List.append_assoc]

/-- The IFMA area fits in the working space the contract asks for. -/
theorem ifmaZ_of {Z k pl : Nat} (hzk : 128 * k ≤ Z) (hw : (k + 7) / 8 = 32) (hp : wsWords pl = 16) : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 + 2 * CrtIfma.D + 8 ≤ Z := by
  unfold offQ VG.Proof.Bignum.X86_64.slot wsWords hdrBytes tabBytes CrtIfma.D at *; omega

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
  rw [VG.Proof.Bignum.X86_64.ifmaMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp) (WP.mono_mx hfront (front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => ?_)
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hql8 := hdr_lt_slot (wsWords ql) 8 (show 31 < 32 by decide)
  refine wp_seqs_append (by simp) (by simp [VG.Impl.Rsa.X86_64.Crt.finish]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono_mx (by decide) (VG.Proof.Bignum.X86_64.sizes_ok (pl := pl) (ql := ql) hr.good
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
    exact wp_seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp [CrtIfma.post])
      (WP.mono (branchA_ok M h hv hr₁ rfl hw hp hq (VG.Proof.Bignum.X86_64.ifmaZ_of h.zk hw hp) hpre) fun t ⟨hd, mxa⟩ =>
        WP.mono (branchB_ok M h hv hd rfl hw hp hq hpost) fun t' ⟨hd', mxb⟩ =>
          ⟨hd', by rw [mxb, mxa, VG.Proof.Bignum.X86_64.mx_ffff, mx₁, mx₀]⟩)
  · exact WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) (WP.mono (qPart_ok M h hv hr₁ rfl)
      fun _ hq => pPart_ok M h hv hq rfl)) fun t hp' mxc => ⟨hp', by rw [mxc, mx₁, mx₀]⟩
  · refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTPre`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: constant time, before the vector code

`pre` is `prep` for each prime, whose pieces (`redc`, copies, Montgomery
multiplications, and the blocks entering and leaving the prime's
workspace) are constant time: so is `prep` (`prep_ct`), for `prep_ok`'s
hypotheses, and `pre` (`pre_ct`), for `pre_ok`'s. Before each piece, a
predicate carries the piece's claim's hypotheses and what correctness gives
after it (`prep_chain`, `pre_chain`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

/-- `redc` of `n`'s `R² mod n` and of its `x R mod n` is constant time. -/
theorem redc_ct_R2 (M : Mont) : RedcCT M Public.aR2 := redc_ct_of M (by taint_decide)
theorem redc_ct_Xm (M : Mont) : RedcCT M Public.aXm := redc_ct_of M (by taint_decide)

/-! ## `prep` -/

/-- `prep_ok`'s hypotheses, with the public data `p` (`n`'s workspace and
`-n⁻¹`, `n`, and the prime's workspace). -/
def PrepPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o ∧
    p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sl) = VG.Proof.Bignum.X86_64.off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X

/-- The prime's workspace. -/
abbrev UPub.pw (p : UPub) : Ws := ⟨VG.Proof.Bignum.X86_64.off p.B p.o, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩

/-- Before leaving the prime's workspace. -/
def PP7 (p : UPub) (s : State) : Prop := s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o

/-- Before `aY := aY · 1`. -/
def PP6 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm Public.aY Public.aY Public.aOne) s (VG.Proof.Bignum.X86_64.PP7 p)

/-- Before `aXc := aT`. -/
def PP5 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr aXc aT)) s (VG.Proof.Bignum.X86_64.PP6 M p)

/-- Before `aT := aY aXc`. -/
def PP4 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm aT Public.aY aXc) s (VG.Proof.Bignum.X86_64.PP5 M p)

/-- Before the second `redc`. -/
def PP3 (M : Mont) (p : UPub) (s : State) : Prop :=
  RPre Public.aXm (xp p) s ∧ WP isa (seqs (redc M.mm Public.aXm)) s (VG.Proof.Bignum.X86_64.PP4 M p)

/-- Before `aY := aXc`. -/
def PP2 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr Public.aY aXc)) s (VG.Proof.Bignum.X86_64.PP3 M p)

/-- Before the first `redc`. -/
def PP1 (M : Mont) (p : UPub) (s : State) : Prop :=
  RPre Public.aR2 (xp p) s ∧ WP isa (seqs (redc M.mm Public.aR2)) s (VG.Proof.Bignum.X86_64.PP2 M p)

/-- Before `prep`. -/
def PP0 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (VG.Proof.Bignum.X86_64.PP1 M p)

theorem prep_eq (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) :
    CrtIfma.prep mul sl = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ (redc mul Public.aR2 ++
      (copyArr Public.aY aXc ++ (redc mul Public.aXm ++ (([mul aT Public.aY aXc] : List (Prog isa)) ++
        (copyArr aXc aT ++ [mul Public.aY Public.aY Public.aOne, .block [leave]]))))) := by
  simp only [CrtIfma.prep, List.append_assoc]

/-- Entering the prime's workspace, from `n`'s. -/
theorem enter_rpre {s : State} {p : UPub} {sl j : Nat} (hj : j < 8) {mx : BitVec 64} {X : Nat}
    (hg : VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv)
    (hw28 : p.w < 2 ^ 28) (hlo : VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.o) (hhi : p.o + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z)
    (hwx2 : 2 ≤ p.wx) (hwx : p.wx ≤ p.w) (hsl : sl < 32) (hslv : VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sl) = VG.Proof.Bignum.X86_64.off p.B p.o)
    (hws : WsAt s.mem p.B p.o p.wx mx) (hX : XVals s p.B p.o p.wx mx X) (hX1 : 1 < X) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun t =>
      RPre j (xp p) t ∧ SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ t.mem = s.mem ∧
        VG.Proof.MlKem.X86_64.Keep [.rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hc : SubCtx t p.B p.Z p.o p.w p.wx mx :=
    SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) hdi hlo hhi
  have hX' : XVals t p.B p.o p.wx mx X := by
    rw [show t = { t with mem := s.mem } by rw [← hm]]; exact ⟨hX.n, hX.inv, hX.one⟩
  exact ⟨⟨mx, X, hc, hX', hwx2, hwx, show p.w < 2 ^ 30 by omega, hX1, hj⟩, hc, hX', hm, k⟩

/-- `prep_ok`'s hypotheses give `PP0`, as `prep_ok` runs the pieces. -/
theorem prep_chain (M : Mont) {sl : Nat} {p : UPub} {s : State} (h : VG.Proof.Bignum.X86_64.PrepPre sl p s) : VG.Proof.Bignum.X86_64.PP0 M sl p s := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot p.wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have lY := slot_le (w := p.wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot p.wx Public.aY (show 31 < 32 by decide)
  have lC := slot_le (w := p.wx) (show aXc < 8 by decide)
  have hC0 := hdr_lt_slot p.wx aXc (show 31 < 32 by decide)
  -- Into the prime's workspace.
  refine ⟨hg.rdi, WP.mono (VG.Proof.Bignum.X86_64.enter_rpre (j := Public.aR2) (by decide) hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1)
    fun s₁ ⟨hr₁, hc₁, hX₁, _, _⟩ => ⟨hr₁, ?_⟩⟩
  -- `redc` of `R_n²`.
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aR2) (by decide))
    fun s₂ ⟨hc₂, hX₂, _, _, _, _⟩ => ⟨⟨mx, hc₂.good, Nat.le_refl _⟩, ?_⟩
  -- `aY := aXc`.
  refine WP.mono (copyArr_ok hc₂.good (Nat.le_refl _) (by omega) (by omega) (o := Public.aY) (a := aXc)
    (by decide) (by decide) (by decide)) fun s₃ ⟨_, ho₃, k₃⟩ => ?_
  have hc₃ := hc₂.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot p.wx Public.aY, 8 * p.wx)]) (Frm.of_outside ho₃ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₃.2.2 (k₃.gpr (by decide))
  have hX₃ : XVals s₃ p.B p.o p.wx mx X := hX₂.of_outside ho₃ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₂.good.scr.nowrap; omega)
  refine ⟨⟨mx, X, hc₃, hX₃, hwx2, hwx, show p.w < 2 ^ 30 by omega, hX1, by decide⟩, ?_⟩
  -- `redc` of `x R_n`.
  refine WP.mono (redc_ok M hc₃ hX₃ hwx2 hwx (by omega) hX1 (j := Public.aXm) (by decide))
    fun s₄ ⟨hc₄, hX₄, hlt₄, _, _, _⟩ => ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, ?_⟩
  -- `aT := aY aXc`.
  refine WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc) hc₄.good (Nat.le_refl _) hwx2 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₄.inv
    (by rw [hX₄.n]; exact hlt₄)) fun s₅ ⟨_, _, _, ha₅, k₅⟩ => ?_
  obtain ⟨hc₅, hX₅, _⟩ := hc₄.of_arrays hX₄ ha₅ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₅.2.2 (k₅.gpr (by decide)) (by omega)
  refine ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, ?_⟩
  -- `aXc := aT`.
  refine WP.mono (copyArr_ok hc₅.good (Nat.le_refl _) (by omega) (by omega) (o := aXc) (a := aT)
    (by decide) (by decide) (by decide)) fun s₆ ⟨_, ho₆, k₆⟩ => ?_
  have hc₆ := hc₅.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot p.wx aXc, 8 * p.wx)]) (Frm.of_outside ho₆ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₆.2.2 (k₆.gpr (by decide))
  have hX₆ : XVals s₆ p.B p.o p.wx mx X := hX₅.of_outside ho₆ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₅.good.scr.nowrap; omega)
  -- `aY := aY · 1`.
  exact ⟨⟨mx, hc₆.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne)
    hc₆.good (Nat.le_refl _) hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₆.inv (by rw [hX₆.n, hX₆.one]; exact hX1)) fun _ h₇ => h₇.1.rdi⟩

/-- `prep` is constant time. -/
theorem prep_ct (M : Mont) (sl : Nat) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (VG.Proof.Bignum.X86_64.PrepPre sl)) (seqs (CrtIfma.prep M.mm sl)) fun _ _ => True := by
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.prep_chain M h) ?_
  rw [VG.Proof.Bignum.X86_64.prep_eq]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) hT (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [redc]) (by simp [copyArr]) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hR2 ?_
  refine ct_steps (by simp [copyArr]) (by simp [redc]) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  refine ct_steps (by simp [redc]) (by simp) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hXm ?_
  refine ct_steps (by simp) (by simp [copyArr]) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [copyArr]) (by simp) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  exact ct_step UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .rdi = _ from h₁, h₂]) (by taint_decide))

/-! ## `pre` -/

/-- The public data of `pre`: `n`'s workspace, `-n⁻¹`, `n`, and the primes'
workspaces (both of `wp` words). -/
structure PrePub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  op : Nat
  oq : Nat
  wp : Nat

abbrev PrePub.uq (p : VG.Proof.Bignum.X86_64.PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.oq, p.wp⟩
abbrev PrePub.up (p : VG.Proof.Bignum.X86_64.PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.op, p.wp⟩

/-- `pre_ok`'s hypotheses. -/
def PrePre (p : VG.Proof.Bignum.X86_64.PrePub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q C : Nat), VG.Proof.Bignum.X86_64.Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧
    p.op + VG.Proof.Bignum.X86_64.slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + VG.Proof.Bignum.X86_64.slot p.wp 8 + tabBytes p.wp ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.w = 2 * p.wp ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧
    WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wp mq ∧ NVals s p.B p.w p.minv p.N ∧
    wv s.mem p.B (VG.Proof.Bignum.X86_64.slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.op p.wp mp P ∧ 1 < P ∧ P % 2 = 1 ∧ XVals s p.B p.oq p.wp mq Q ∧ 1 < Q ∧ Q % 2 = 1

/-- Before `pre`. -/
def PR0 (M : Mont) (p : VG.Proof.Bignum.X86_64.PrePub) (s : State) : Prop :=
  VG.Proof.Bignum.X86_64.PrepPre sWsQ p.uq s ∧ WP isa (seqs (CrtIfma.prep M.mm sWsQ)) s (VG.Proof.Bignum.X86_64.PrepPre sWsP p.up)

/-- `pre_ok`'s hypotheses give `PR0`, as `pre_ok` runs the pieces. -/
theorem pre_chain (M : Mont) {p : VG.Proof.Bignum.X86_64.PrePub} {s : State} (h : VG.Proof.Bignum.X86_64.PrePre p s) : VG.Proof.Bignum.X86_64.PR0 M p s := by
  obtain ⟨B, Z, w, minv, N, op, oq, wp⟩ := p
  dsimp only [VG.Proof.Bignum.X86_64.PrePre] at h
  obtain ⟨mp, mq, P, Q, C, hg, hw28, hlo, hpq, hoq, hwp2, hw2, hsp, hsq, hwsp, hwsq, hN, hXm, hP,
    hP1, hPodd, hQ, hQ1, hQodd⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wp 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : oq < 2 ^ 64 := by omega
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + VG.Proof.Bignum.X86_64.slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  refine ⟨by dsimp only [VG.Proof.Bignum.X86_64.PrepPre, PrePub.uq]; exact ⟨mq, Q, hg, hw28, by omega, hoq, hwp2, by omega, by decide, hsq,
    hwsq, hQ, hQ1⟩,
    WP.mono (prep_ok (C := C) M hg hw28 (by omega) hoq hwp2 hw2 (by decide) hsq hwsq hN hXm hQ hQ1 hQodd)
    fun s₁ ⟨hg₁, _, _, _, _, _, _, fQ, _, _⟩ => ?_⟩
  have hb : ∀ d, d + 8 ≤ oq → VG.Proof.Bignum.X86_64.word s₁.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => fQ.x_below hd ho64
  dsimp only [VG.Proof.Bignum.X86_64.PrepPre, PrePub.up]
  exact ⟨mp, P, hg₁, hw28, hlo, by omega, hwp2, by omega, by decide,
    by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp,
    hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega),
    hP.of_disj fQ hQd (by omega), hP1⟩

/-- `pre` is constant time. -/
theorem pre_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.PrePre) (seqs (CrtIfma.pre M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.pre_chain M h) ?_
  refine ct_steps (by simp [CrtIfma.prep]) (by simp [CrtIfma.prep]) PrePub.uq (fun _ _ h => h.1)
    (fun _ _ h => h.2) (VG.Proof.Bignum.X86_64.prep_ct M sWsQ hR2 hXm (by taint_decide)) ?_
  exact ct_last PrePub.up (fun _ _ h => h) (VG.Proof.Bignum.X86_64.prep_ct M sWsP hR2 hXm (by taint_decide))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTPost`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: constant time, after the exponentiations

`post` is, in `p`'s workspace, a `redc`, the loads of `q`'s result's
address (split at each load whose address the previous one gave), its
copy, a Montgomery multiplication and a copy, then `hSteps` after its
`redc` (`h2_ct`): each is constant time, so `post` is (`post_ct`), for
`post_ok`'s hypotheses (`PostPre`), from which `post_chain` proves what
each piece needs, as `post_ok` runs them.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

/-- The public data of `post`: `n`'s workspace, `p`'s and `q`'s (of `wx`
words each), and `qInv`'s pointer and length. -/
structure PostPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  wx : Nat
  oq : Nat
  qp : Addr
  len : Nat

abbrev PostPub.x (p : VG.Proof.Bignum.X86_64.PostPub) : XPub := ⟨p.B, p.Z, p.op, p.w, p.wx⟩
abbrev PostPub.pw (p : VG.Proof.Bignum.X86_64.PostPub) : Ws := ⟨VG.Proof.Bignum.X86_64.off p.B p.op, VG.Proof.Bignum.X86_64.slot p.wx 8, p.wx⟩
abbrev PostPub.h (p : VG.Proof.Bignum.X86_64.PostPub) : HPub := ⟨p.B, p.Z, p.w, p.op, p.wx, p.qp, p.len⟩

/-- `post`'s loads of `q`'s result's address: `n`'s base, `q`'s, and from them. -/
def postBlk1 : List Instr := [.mov .rax (.mem (hdr sLink))]
def postBlk2 : List Instr := [.mov .rax (.mem (ws .rax sWsQ))]
def postBlk3 : List Instr :=
  [.mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk)))]

theorem post_eqCT (mul : Nat → Nat → Nat → Prog isa) :
    CrtIfma.post mul = ([.block [.mov .rdi (.mem (hdr sWsP))]] : List (Prog isa)) ++ (redc mul Public.aR2 ++
      (.block (VG.Proof.Bignum.X86_64.postBlk1 ++ (VG.Proof.Bignum.X86_64.postBlk2 ++ VG.Proof.Bignum.X86_64.postBlk3)) :: copyWords :: mul aChunk aChunk aXc ::
        (copyArr aXc aChunk ++ (subModArr aT Public.aY aXc ++ (loadArr aChunk sQinv sPlen ++ (maskArr aChunk ++
          [mul Public.aY aT aChunk, .block [leave]])))))) := by
  simp only [CrtIfma.post, enterP, VG.Proof.Bignum.X86_64.postBlk1, VG.Proof.Bignum.X86_64.postBlk2, VG.Proof.Bignum.X86_64.postBlk3, List.append_assoc, List.cons_append,
    List.nil_append]

/-- Before `aXc := aChunk`. -/
def Q7 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr aXc aChunk)) s (H2 M p.h)

/-- Before `aChunk := aChunk aXc`. -/
def Q6 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm aChunk aChunk aXc) s (VG.Proof.Bignum.X86_64.Q7 M p)

/-- Before the copy of `m_q`. -/
def Q5 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  s.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.oq) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧
    s.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot p.wx aChunk) ∧ WP isa copyWords s (VG.Proof.Bignum.X86_64.Q6 M p)

/-- Before the loads from `q`'s workspace. -/
def Q4 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  s.gpr .rax = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.op ∧ WP isa (.block VG.Proof.Bignum.X86_64.postBlk3) s (VG.Proof.Bignum.X86_64.Q5 M p)

/-- Before the load of `q`'s base. -/
def Q3 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  s.gpr .rax = p.B ∧ s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.op ∧ WP isa (.block VG.Proof.Bignum.X86_64.postBlk2) s (VG.Proof.Bignum.X86_64.Q4 M p)

/-- Before the load of `n`'s base. -/
def Q2 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  s.gpr .rdi = VG.Proof.Bignum.X86_64.off p.B p.op ∧ WP isa (.block VG.Proof.Bignum.X86_64.postBlk1) s (VG.Proof.Bignum.X86_64.Q3 M p)

/-- Before the `redc`. -/
def Q1 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  RPre Public.aR2 p.x s ∧ WP isa (seqs (redc M.mm Public.aR2)) s (VG.Proof.Bignum.X86_64.Q2 M p)

/-- Before `post`. -/
def Q0 (M : Mont) (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sWsP))]) s (VG.Proof.Bignum.X86_64.Q1 M p)

/-- `post_ok`'s hypotheses, with what `post` reads of them public. -/
def PostPre (p : VG.Proof.Bignum.X86_64.PostPub) (s : State) : Prop :=
  ∃ (minv mx mq : BitVec 64) (X : Nat) (qib : List Byte) (c : Bool),
    Good s p.B p.Z p.w minv ∧ p.w < 2 ^ 28 ∧ p.w = 2 * p.wx ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsQ) = VG.Proof.Bignum.X86_64.off p.B p.oq ∧ WsAt s.mem p.B p.oq p.wx mq ∧
    p.oq + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ VG.Proof.Bignum.X86_64.slot p.w 8 ≤ p.op ∧
    p.op + VG.Proof.Bignum.X86_64.slot p.wx 8 + tabBytes p.wx ≤ p.oq ∧ 2 ≤ p.wx ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sWsP) = VG.Proof.Bignum.X86_64.off p.B p.op ∧ WsAt s.mem p.B p.op p.wx mx ∧ XVals s p.B p.op p.wx mx X ∧
    1 < X ∧ wv s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (VG.Proof.Bignum.X86_64.slot p.wx Public.aY) p.wx < X ∧
    VG.Proof.Bignum.X86_64.word s.mem (VG.Proof.Bignum.X86_64.off p.B p.op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c ∧ VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sQinv) = p.qp ∧
    VG.Proof.Bignum.X86_64.word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 qib.length ∧ Src s p.B p.Z p.qp qib ∧ 1 ≤ qib.length ∧
    qib.length < 2 ^ 31 ∧ (qib.length + 7) / 8 ≤ p.wx ∧ (c = true → Spec.Rsa.os2ip qib < X) ∧ qib.length = p.len

/-- `post_ok`'s hypotheses give `Q0`, as `post_ok` runs the pieces. -/
theorem post_chain (M : Mont) {p : VG.Proof.Bignum.X86_64.PostPub} {s : State} (h : VG.Proof.Bignum.X86_64.PostPre p s) : VG.Proof.Bignum.X86_64.Q0 M p s := by
  obtain ⟨B, Z, w, op, wx, oq, qp, len⟩ := p
  dsimp only [VG.Proof.Bignum.X86_64.PostPre] at h
  obtain ⟨minv, mx, mq, X, qib, c, hg, hw28, hw2, hq, hwsq, hhiq, hlo, hhi, hwx2, hsp, hws, hX, hX1, hyl, hmask,
    hqp, hql, hqs, hq1, hq2, hqw, hqi, rfl⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ VG.Proof.Bignum.X86_64.slot wx 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have ho64 : op < 2 ^ 64 := by omega
  have hoL : op + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by omega
  have hwx : wx ≤ w := by omega
  have lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  have lC := slot_le (w := wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot wx aChunk (show 31 < 32 by decide)
  have lX := slot_le (w := wx) (show aXc < 8 by decide)
  have hX0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  have hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, VG.Proof.Bignum.X86_64.slot, hdrBytes] <;>
      omega
  have rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  -- Into `p`'s workspace.
  refine ⟨hg.rdi, WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off B op ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega), hsp]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ?_⟩
  have hc₁ : SubCtx s₁ B Z op w wx mx :=
    SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws) hdi₁ hlo (by omega)
  have hX₁ : XVals s₁ B op wx mx X := ⟨by rw [hm₁]; exact hX.n, by rw [hm₁]; exact hX.inv, by rw [hm₁]; exact hX.one⟩
  refine ⟨⟨mx, X, hc₁, hX₁, hwx2, hwx, show w < 2 ^ 30 by omega, hX1, by decide⟩, ?_⟩
  -- `redc` of `R_n²`.
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aR2) (by decide))
    fun s₂ ⟨hc₂, hX₂, hlt₂, _, r₂, k₂⟩ => ?_
  have fx₂ : Frm B [xRange op wx] s.mem s₂.mem := by
    rw [← hm₁]; exact r₂.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  have hb₂ : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => fx₂.x_below hd ho64
  have hab₂ : ∀ d, op + VG.Proof.Bignum.X86_64.slot wx 8 + tabBytes wx ≤ d → d + 8 ≤ 2 ^ 64 → VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d :=
    fun d hd hd' => fx₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) hd'
  have hs₂ := hc₂.scr
  have hsP := hc₂.good.scr
  have hdi₂ := hc₂.rdi
  refine ⟨hdi₂, ?_⟩
  -- `rax := B`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = B ∧ t.mem = s₂.mem)
    (by xrun [VG.Proof.Bignum.X86_64.postBlk1, State.ea, hdr, hdi₂, hdrOff, hsP.ld (d := 8 * sLink) (by unfold sLink sFn; omega),
      hc₂.link]) rfl) fun s₃ ⟨⟨hax₃, hm₃⟩, k₃⟩ => ⟨hax₃, (k₃.gpr (by decide)).trans hdi₂, ?_⟩
  have hs₃ := hs₂.congr k₃.2.2
  -- `rax := q`'s base.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off B oq ∧ t.mem = s₃.mem)
    (by xrun [VG.Proof.Bignum.X86_64.postBlk2, State.ea, ws, hax₃, hdrOff, hs₃.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega), hm₃,
      hb₂ (8 * sWsQ) (by unfold sWsQ sFn; omega), hq]) rfl)
    fun s₄ ⟨⟨hax₄, hm₄⟩, k₄⟩ => ⟨hax₄, (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂), ?_⟩
  have hs₄ := hs₃.congr k₄.2.2
  have hsP₄ := (hsP.congr k₃.2.2).congr k₄.2.2
  have hldq := (hs₄.sub (o := oq) (n := VG.Proof.Bignum.X86_64.slot wx 8) (by omega) (by omega)).ld (d := 8 * sArr Public.aY)
    (by unfold sArr Public.aY; omega)
  have hqa : VG.Proof.Bignum.X86_64.word s₄.mem (VG.Proof.Bignum.X86_64.off B oq) (8 * sArr Public.aY) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) := by
    rw [hm₄, hm₃, word_off, hab₂ (oq + 8 * sArr Public.aY) (by omega) (by unfold sArr Public.aY; omega), ← word_off]
    exact hwsq.hdr.harr Public.aY (by decide)
  have hdi₄ : s₄.gpr .rdi = VG.Proof.Bignum.X86_64.off B op := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  have hpw : ∀ i < 32, VG.Proof.Bignum.X86_64.word s₄.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) = VG.Proof.Bignum.X86_64.word s₂.mem (VG.Proof.Bignum.X86_64.off B op) (8 * i) := fun i _ => by
    rw [hm₄, hm₃]
  -- `rsi`, `r12`, `rbx`.
  refine WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B oq) (VG.Proof.Bignum.X86_64.slot wx Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aChunk) ∧ t.mem = s₄.mem)
    (by xrun [VG.Proof.Bignum.X86_64.postBlk3, State.ea, hdr, ws, hax₄, hdi₄, hdrOff, hldq, hqa,
      hsP₄.ld (d := 8 * sW) (by unfold sW; omega), hpw sW (by decide), hc₂.hdr.hw,
      hsP₄.ld (d := 8 * sArr aChunk) (by unfold sArr aChunk; omega), hpw (sArr aChunk) (by decide),
      hc₂.hdr.harr aChunk (by decide)]) rfl)
    fun s₅ ⟨⟨hsi₅, h12₅, hbx₅, hm₅⟩, k₅⟩ => ⟨hsi₅, h12₅, hbx₅, ?_⟩
  have k25 := (k₃.trans k₄).trans k₅
  have hs₅ := hs₂.congr k25.2.2
  have hsP₅ := hsP.congr k25.2.2
  have hsi₅' : s₅.gpr .rsi = VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY) := by rw [hsi₅, off_off]
  -- `aChunk := m_q`.
  refine WP.mono (copyWords_ok (S := B) (eS := oq + VG.Proof.Bignum.X86_64.slot wx Public.aY) (D := VG.Proof.Bignum.X86_64.off B op) (eD := VG.Proof.Bignum.X86_64.slot wx aChunk)
    (w := wx) hsi₅' hbx₅ h12₅ (by omega) (by omega) (by omega) (fun j hj => hs₅.ld (by omega))
    (fun j hj => hsP₅.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [show VG.Proof.Bignum.X86_64.off B (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY + 8 * j) = VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B op) (oq + VG.Proof.Bignum.X86_64.slot wx Public.aY + 8 * j - op) by
        rw [off_off]; congr 1; omega, VG.Proof.Bignum.X86_64.ofs_off (VG.Proof.Bignum.X86_64.off B op) (by omega)]; omega))) fun s₆ ⟨_, _, ho₆, k₆⟩ => ?_
  have hm25 : s₅.mem = s₂.mem := by rw [hm₅, hm₄, hm₃]
  rw [hm25] at ho₆
  have hz₂ : (VG.Proof.Bignum.X86_64.off B op).toNat + VG.Proof.Bignum.X86_64.slot wx 8 ≤ 2 ^ 64 := by have := hc₂.good.scr.nowrap; omega
  have hX₆ : XVals s₆ B op wx mx X := hX₂.of_outside ho₆ (by decide) (by decide) (by decide) (by omega) hz₂
  have hc₆ : SubCtx s₆ B Z op w wx mx := hc₂.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot wx aChunk, 8 * wx)]) (Frm.of_outside ho₆ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) (k25.trans k₆).2.2 ((k25.trans k₆).gpr (by decide))
  have hxc₆ : wv s₆.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx = wv s₂.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx aXc) wx := by
    have := slot_sep (w := wx) (show aXc ≠ aChunk by decide)
    exact ho₆.wv (by omega) (by omega)
  refine ⟨⟨mx, hc₆.good, Nat.le_refl _⟩, ?_⟩
  -- `aChunk := aChunk aXc`.
  refine WP.mono (M.mm_ok (o := aChunk) (a := aChunk) (b := aXc) hc₆.good (Nat.le_refl _) hwx2
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₆.inv
    (by rw [hX₆.n, hxc₆]; exact hlt₂)) fun s₇ ⟨_, hlt₇, _, ha₇, k₇⟩ => ?_
  rw [hX₆.n] at hlt₇
  obtain ⟨hc₇, hX₇, fx₇⟩ := hc₆.of_arrays hX₆ ha₇ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₇.2.2 (k₇.gpr (by decide)) (by omega)
  refine ⟨⟨mx, hc₇.good, Nat.le_refl _⟩, ?_⟩
  -- `aXc := aChunk`.
  refine WP.mono (copyArr_ok hc₇.good (Nat.le_refl _) (by omega) (by omega) (o := aXc) (a := aChunk)
    (by decide) (by decide) (by decide)) fun s₈ ⟨hv₈, ho₈, k₈⟩ => ?_
  have hc₈ := hc₇.of_frm (rs := [(VG.Proof.Bignum.X86_64.slot wx aXc, 8 * wx)]) (Frm.of_outside ho₈ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₈.2.2 (k₈.gpr (by decide))
  have hX₈ : XVals s₈ B op wx mx X := hX₇.of_outside ho₈ (by decide) (by decide) (by decide) (by omega) hz₂
  have fx₈ : Frm B [xRange op wx] s₇.mem s₈.mem :=
    (ho₈.mono (o' := VG.Proof.Bignum.X86_64.slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have fx₆ : Frm B [xRange op wx] s₂.mem s₆.mem :=
    (ho₆.mono (o' := VG.Proof.Bignum.X86_64.slot wx aChunk) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega)).to_x
      (by decide) hoL (List.mem_singleton_self _)
  have f08 : Frm B [xRange op wx] s.mem s₈.mem := ((fx₂.trans fx₆).trans fx₇).trans fx₈
  have hb₈ : ∀ d, d + 8 ≤ op → VG.Proof.Bignum.X86_64.word s₈.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun d hd => f08.x_below hd ho64
  have i08 : InScr B Z s.mem s₈.mem :=
    InScr.of_frm f08 fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega
  have hY₈ : wv s₈.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx = wv s.mem (VG.Proof.Bignum.X86_64.off B op) (VG.Proof.Bignum.X86_64.slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    have := slot_sep (w := wx) (show Public.aY ≠ aChunk by decide)
    rw [ho₈.wv (by omega) (by omega), ha₇.wv_of_not_mem (by decide) (by decide) hz₂, ho₆.wv (by omega) (by omega),
      r₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega), hm₁]
  have hM₈ : VG.Proof.Bignum.X86_64.word s₈.mem (VG.Proof.Bignum.X86_64.off B op) (8 * sMaskX) = VG.Proof.Bignum.X86_64.mask c := by
    have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega
    rw [ho₈.word (.inl (by omega)) (by omega), ha₇.hslot (by decide), ho₆.word (.inl (by omega)) (by omega),
      r₂.word_eq hrm (by omega), hm₁]; exact hmask
  exact h2_chain M hc₈ hX₈ hX1 hw28 hwx2 hwx (by rw [hY₈]; exact hyl) (by rw [hv₈]; exact hlt₇) hM₈
    (by rw [hb₈ _ (by unfold sQinv sFn; omega)]; exact hqp) (by rw [hb₈ _ (by unfold sPlen sFn; omega)]; exact hql)
    (hqs.congrK i08 (((((k₁.trans k₂).trans k25).trans k₆).trans k₇).trans k₈)) hq1 hq2 hqw hqi

/-- `post` is constant time. -/
theorem post_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hL : LoadCT aChunk sQinv sPlen) :
    RelCT isa (Two VG.Proof.Bignum.X86_64.PostPre) (seqs (CrtIfma.post M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => VG.Proof.Bignum.X86_64.post_chain M h) ?_
  rw [VG.Proof.Bignum.X86_64.post_eqCT]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [redc]) (by simp) PostPub.x (fun _ _ h => h.1) (fun _ _ h => h.2) hR2 ?_
  have b1 : RelCT isa (Two (VG.Proof.Bignum.X86_64.Q2 M)) (.block VG.Proof.Bignum.X86_64.postBlk1) (Two (VG.Proof.Bignum.X86_64.Q3 M)) :=
    two_piece [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) fun _ _ h => h.2
  have b2 : RelCT isa (Two (VG.Proof.Bignum.X86_64.Q3 M)) (.block VG.Proof.Bignum.X86_64.postBlk2) (Two (VG.Proof.Bignum.X86_64.Q4 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  have b3 : RelCT isa (Two (VG.Proof.Bignum.X86_64.Q4 M)) (.block VG.Proof.Bignum.X86_64.postBlk3) (Two (VG.Proof.Bignum.X86_64.Q5 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq b1 (RelCT.block_append (RelCT.seq b2 b3)))) ?_
  refine ct_taint [.rsi, .r12, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  refine RelCT.seq (two_post (Ψ := VG.Proof.Bignum.X86_64.Q7 M) (two_map PostPub.pw (fun _ _ h => h.1) (M.ct (by unfold MmUse; decide)))
    fun _ _ h => h.2) ?_
  exact ct_steps (by simp [copyArr]) (by simp [subModArr]) PostPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) (two_map PostPub.h (fun _ _ h => h) (h2_ct M hL))

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTMain`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: `main` in constant time

`CrtIfma.main` is `Crt.main` with a branch on the sizes, which are public:
the IFMA branch's parts (`pre`, `ifma`, `post`) are constant time for their
correctness lemmas' hypotheses (`pre_ct`, `ifma_ct`, `post_ct`), which the
states of a run between them satisfy (`prePre_of`, `ifPre_of`, `postPre_of`,
from `branchA_ok`'s and `branchB_ok`'s steps); the other branch is
`vg_rsa_private_crt`'s (`qS_ct`, `pS_ct`). So `main` is (`ifmaMain_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D sIfma)

/-! ## The parts' hypotheses from a run's states -/

/-- `pre_ok`'s hypotheses, after the checks. -/
theorem prePre_of {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    VG.Proof.Bignum.X86_64.PrePre ⟨B, Z, (k + 7) / 8, minv, Spec.Rsa.os2ip nb, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl, 16⟩ t₀ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  dsimp only [VG.Proof.Bignum.X86_64.PrePre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact ⟨mp, mq, _, _, C, hr.good, by omega, le_refl _, by rw [hoq]; rfl, by omega, by decide, by omega,
    hr.wsP, hr.wsQ, pws, qws, hr.nv, hr.xm, pxv, hP'.1, hP'.2, qxv, hQ'.1, hQ'.2⟩

/-- `ifma`'s hypotheses, after `pre` (as `branchA2_ok` runs it). -/
theorem ifPre_of {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hZa : offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 + 2 * VG.Impl.Rsa.X86_64.CrtIfma.D + 8 ≤ Z)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) 16 minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    IfPre ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), offQ ((k + 7) / 8) pl,
      offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16, dpp, dqp, pl, ql⟩ s₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  dsimp only [IfPre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hql' : ql ≤ 128 := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have hh₀ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  have ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := 16) (wq := 16) (le_refl (offP ((k + 7) / 8)))
    (show VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) 16 (offQ ((k + 7) / 8) pl) 16,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := fun r hr => by
    simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl | rfl
    · have := (gRanges_lt _ r hr).2; rw [hoq]; omega
    · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); rw [hoq]; simp only; omega
    · simp only [xRange]; omega
    · simp only [xRange]; rw [hoq, hop]; omega
  have i₀₁ : InScr B Z t₀.mem s₁.mem := InScr.of_frm f₁ fun r hr => by have := hpr r hr; omega
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => nsafe_word f₁ ns₁ hi h1 h2
  have hf₁ : ∀ i < 32, hFixed i = true → VG.Proof.Bignum.X86_64.word s₁.mem B (8 * i) = VG.Proof.Bignum.X86_64.word s.mem B (8 * i) := fun i hi hf => by
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  have kk₁ := hr.keep.trans k₁
  have ip : IPre s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (VG.Proof.Bignum.X86_64.mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  exact ⟨minv, mp, mq, VG.Proof.Bignum.X86_64.mask Mk, _, _, dpb, dqb, hg₁.scr, hg₁.rdi, ip, le_refl _, by rw [hoq, hop], rfl,
    by omega, hP'.2, hQ'.2, rp.ylt, rq.ylt, rp.clt, rq.clt, h.dp.congrK (hr.iscr.trans i₀₁) kk₁,
    h.dq.congrK (hr.iscr.trans i₀₁) kk₁, by rw [h.dpl]; exact hpl1, by rw [h.dpl]; exact hpl',
    by rw [h.dql]; exact hql1, by rw [h.dql]; exact hql', h.dpl, h.dql⟩

/-- `post`'s hypotheses, after `ifma` (as `branchB_ok` runs it). -/
theorem postPre_of {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    VG.Proof.Bignum.X86_64.PostPre ⟨B, Z, (k + 7) / 8, offP ((k + 7) / 8), wsWords pl, offQ ((k + 7) / 8) pl, qip, pl⟩ t₁ := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hZq := h.z
  have hqil := h.qil
  dsimp only [VG.Proof.Bignum.X86_64.PostPre]
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hop : offP ((k + 7) / 8) = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 + tabBytes (wsWords pl) := rfl
  have hW8 : 256 ≤ VG.Proof.Bignum.X86_64.slot (wsWords pl) 8 := by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega
  have hm := hd.im
  exact ⟨minv, mp, mq, _, qib, Mk, hd.good, by omega, by rw [hpl]; omega, hm.wsQ, by rw [hpl]; exact hm.qws,
    by have := hZq; rw [hql] at this; rw [hpl]; exact this, le_refl _, by rw [hoq, hop], by rw [hpl]; decide,
    hm.wsP, by rw [hpl]; exact hm.pws, by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩, hP'.1,
    by rw [hpl]; exact hd.plt, hm.pmk, hd.qi, by rw [hqil]; exact hm.pl, h.qi.congrK hd.iscr hd.keep,
    by rw [hqil]; exact hpl1, by rw [hqil]; omega, by rw [hqil, hpl]; omega,
    fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi, hqil⟩

/-- `pre`, from the checks: what `pre_ok` leaves. -/
theorem pre_apost (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16) :
    WP isa (seqs (CrtIfma.pre M.mm)) t₀ fun t => APost t₀ t B Z ((k + 7) / 8) (offP ((k + 7) / 8))
      (offQ ((k + 7) / 8) pl) 16 minv mp mq (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3)
      (if Mk then Spec.Rsa.os2ip qb else 3) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hoq : offQ ((k + 7) / 8) pl = VG.Proof.Bignum.X86_64.slot ((k + 7) / 8) 8 + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16 := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  exact pre_ok M (wp := 16) hr.good (by omega) (le_refl _) (by rw [hoq]; exact Nat.le_refl _) (by omega)
    (by decide) (by omega) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2

/-! ## The stages of the IFMA branch -/

/-- After the checks, with the sizes of the IFMA branch. -/
def R3I : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16

/-- After `pre`. -/
def RAp : StageRel := fun p σ xb pb qb _ _ qib t => ∃ (minv mp mq : BitVec 64) (t₀ : State),
  CrtReady σ t₀ p.B p.Z p.w p.pl p.ql minv mp mq p.N (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
    (p.mask xb pb qb qib) ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16 ∧
  APost t₀ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) 16 minv mp mq p.N
    (if p.mask xb pb qb qib then Spec.Rsa.os2ip pb else 3) (if p.mask xb pb qb qib then Spec.Rsa.os2ip qb else 3)
    (Spec.Rsa.os2ip xb)

/-- After `ifma`. -/
def RID : StageRel := fun p σ xb pb qb dpb dqb qib t => ∃ (minv mp mq : BitVec 64),
  IDone σ t p.B p.Z p.w (offP p.w) (offQ p.w p.pl) (offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16) minv mp mq p.N
    (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) p.dpp p.dqp p.qip p.pl p.ql dpb dqb
    (p.mask xb pb qb qib) ∧ p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16

theorem preS_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two (Stage VG.Proof.Bignum.X86_64.R3I)) (seqs (CrtIfma.pre M.mm)) (Two (Stage VG.Proof.Bignum.X86_64.RAp)) :=
  stage_step ((VG.Proof.Bignum.X86_64.pre_ct M hR2 hXm).mono (fun _ _ h => two_stage (fun p minv => (⟨p.B, p.Z, p.w, minv, p.N, offP p.w,
    offQ p.w p.pl, 16⟩ : VG.Proof.Bignum.X86_64.PrePub)) (fun _ _ _ _ _ _ _ _ _ h hv ⟨⟨minv, _, _, hr⟩, hw, hp, hq⟩ =>
      ⟨minv, hr.nv, VG.Proof.Bignum.X86_64.prePre_of h hv hr rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ t h hv ⟨⟨minv, mp, mq, hr⟩, hw, hp, hq⟩ =>
      WP.mono (VG.Proof.Bignum.X86_64.pre_apost M h hv hr rfl hw hp hq) fun _ hA => ⟨minv, mp, mq, t, hr, hw, hp, hq, hA⟩

theorem ifmaS_ct : RelCT isa (Two (Stage VG.Proof.Bignum.X86_64.RAp)) (seqs CrtIfma.ifma) (Two (Stage VG.Proof.Bignum.X86_64.RID)) :=
  stage_step (ifma_ct.mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w, offQ p.w p.pl,
    offQ p.w p.pl + VG.Proof.Bignum.X86_64.slot 16 8 + tabBytes 16, p.dpp, p.dqp, p.pl, p.ql⟩ : IfPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, _, hr, hw, hp, hq, hA⟩ =>
      ⟨minv, hA.2.1, VG.Proof.Bignum.X86_64.ifPre_of h hv hr rfl hw hp hq (VG.Proof.Bignum.X86_64.ifmaZ_of h.zk hw hp) hA⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, _, hr, hw, hp, hq, hA⟩ =>
      WP.mono (branchA2_ok h hv hr rfl hw hp hq (VG.Proof.Bignum.X86_64.ifmaZ_of h.zk hw hp) hA) fun _ ⟨hd, _⟩ =>
        ⟨minv, mp, mq, hd, hw, hp, hq⟩

theorem postS_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage VG.Proof.Bignum.X86_64.RID)) (seqs (CrtIfma.post M.mm)) (Two (Stage R5)) :=
  stage_step ((VG.Proof.Bignum.X86_64.post_ct M hR2 hL).mono (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w,
    wsWords p.pl, offQ p.w p.pl, p.qip, p.pl⟩ : VG.Proof.Bignum.X86_64.PostPub))
    (fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, _, _, hd, hw, hp, hq⟩ =>
      ⟨minv, hd.nv, VG.Proof.Bignum.X86_64.postPre_of h hv hd rfl hw hp hq⟩) h) fun _ _ h => h)
    fun _ _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hd, hw, hp, hq⟩ =>
      WP.mono (branchB_ok M h hv hd rfl hw hp hq hpost) fun _ ⟨hp', _⟩ => ⟨minv, mp, mq, hp'⟩

/-- After the sizes' check. -/
def R3S : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R3 p σ xb pb qb dpb dqb qib t ∧ t.zf = some (decide (p.w = 32 ∧ wsWords p.pl = 16 ∧ wsWords p.ql = 16))

theorem sizesS_ct : RelCT isa (Two (Stage R3)) (.block CrtIfma.sizes) (Two (Stage VG.Proof.Bignum.X86_64.R3S)) :=
  stage_step (two_taint [.rdi] (pins_eqs (fun p _ => p.B) fun p t h r hr => by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr'⟩ := h
      rw [List.mem_singleton.mp hr]; exact hr'.good.rdi) (by taint_decide))
    fun p _ _ _ _ _ _ _ _ h hv ⟨minv, mp, mq, hr⟩ => by
      have hn := hr.good.scr.nowrap
      have h8 := hdr_lt_slot ((p.k + 7) / 8) 8 (show 31 < 32 by decide)
      have hZq := h.z
      have hk2 := h.k2
      have hpl2 := h.pl2
      have hql2 := h.ql2
      exact WP.mono (VG.Proof.Bignum.X86_64.sizes_ok (pl := p.pl) (ql := p.ql) hr.good
        (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
        (by unfold offQ at hZq; omega) (show (p.k + 7) / 8 < 2 ^ 64 by omega) (by omega) (by omega))
        fun t' ⟨zf, me, k⟩ => ⟨⟨minv, mp, mq, hr.of_regs me k⟩, zf⟩

/-- The IFMA branch. -/
theorem ifmaB_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage VG.Proof.Bignum.X86_64.R3I)) (seqs (CrtIfma.pre M.mm ++ CrtIfma.ifma ++ CrtIfma.post M.mm))
      (Two (Stage R5)) := by
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [CrtIfma.pre, CrtIfma.prep]) (by simp [CrtIfma.ifma])
    (RelCT.seq (VG.Proof.Bignum.X86_64.preS_ct M hR2 hXm) ?_)
  exact RelCT.seqs_append (by simp [CrtIfma.ifma]) (by simp [CrtIfma.post])
    (RelCT.seq VG.Proof.Bignum.X86_64.ifmaS_ct (VG.Proof.Bignum.X86_64.postS_ct M hR2 hL hpost))

/-! ## `main` -/

/-- `main` leaks the same in runs that agree on the public data, given that
its parts do. -/
theorem ifmaMain_ct (M : Mont) (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (Stage R0)) (CrtIfma.main M.mm) fun _ _ => True := by
  rw [VG.Proof.Bignum.X86_64.ifmaMain_eq]
  refine RelCT.seqs_append (by simp [nSetup]) (by simp) (RelCT.seq (R := Two (Stage R3)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks])
      (RelCT.seq (R := Two (Stage R2)) ?_ (checksS_ct hC))
    refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (RelCT.seq (R := Two (Stage R1)) ?_ (setupS_ct hS))
    exact stage_step (nSetup_ct M) fun p σ xb _ _ _ _ _ t h hv ht => by
      subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
  refine RelCT.seqs_append (by simp) (by simp [VG.Impl.Rsa.X86_64.Crt.finish]) (RelCT.seq ?_ hF)
  refine RelCT.seq VG.Proof.Bignum.X86_64.sizesS_ct (two_ite (fun p s₁ s₂ h₁ h₂ => ?_) ?_ ?_)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, z₁⟩ := h₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, z₂⟩ := h₂
    simp only [eval, z₁, z₂]
  · refine (VG.Proof.Bignum.X86_64.ifmaB_ct M hR2 hXm hL hpost).mono (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, hz⟩, he⟩ := h
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, he⟩
  · refine (RelCT.seqs_append (by simp [qPhase]) (by simp [pPhase]) (RelCT.seq (qS_ct M hQ) (pS_ct M hP))).mono
      (fun _ _ h => two_mono (fun p s h => ?_) h) fun _ _ h => h
    obtain ⟨⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr, _⟩, _⟩ := h
    exact ⟨σ, xb, pb, qb, dpb, dqb, qib, hσ, hv, hr⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTCode`. -/
section

/-!
# `vg_rsa_private_crt_ifma` on x86-64: constant time but for `n`

`CrtIfma.code` is `Crt.code` with `CrtIfma.main` (`ifmaMain_ct`): the head
and the modulus' check are as in `crtCode_ct`, so the function is constant
time (`ifmaCode_constantTime_of`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

variable (M : Mont)

/-- `vg_rsa_private_crt_ifma` leaks the same in runs that agree on the public
data, given that `main`'s parts do. -/
theorem ifmaCode_ct (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two CCRel) (CrtIfma.code M.mm) fun _ _ => True := by
  unfold CrtIfma.code
  refine RelCT.seq (R := Two CC3) (RelCT.block_append (RelCT.seq (R := Two CC2) ?_ ?_)) ?_
  · rw [crtEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := crtCtx_of hs.1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++
        ((Crt.entry.drop 1) ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]))) s (CrtHeadPost s) := by
      rw [← crtEntry_split]; exact crtHead_ok c
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.1, c₂.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := crtCtx_of hs.1
    have hnb := c.hnb.congrK h.inScr h.keep
    obtain ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := id hs
    refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
      rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ =>
        ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, hn, hk]
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold fail
    have pin : ∀ p t, (CC3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.m.B := fun p t ⟨h, _⟩ => by
      obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
      exact hpre.rdi
    refine RelCT.seq (two_piece (Ψ := fun (p : CCPub) t => t.gpr .rsi = p.m.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.m.k ∧ t.gpr .rdi = p.m.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨h, -⟩
    obtain ⟨_, _, _, _, _, _, hpre⟩ := cc3_pre h
    have hn := hpre.scr.nowrap
    have hk1 := hpre.k1
    have hk2 := hpre.k2
    have hZq := hpre.z
    have h8 := hdr_lt_slot ((p.m.k + 7) / 8) 8 (show 31 < 32 by decide)
    have hZ : 8 * 32 ≤ p.m.Z := by unfold offQ at hZq; omega
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off p.m.B (8 * i)) 8 := fun i hi => hpre.scr.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.m.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 p.m.k) (by
      xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hpre.rdi⟩
  · -- `main`.
    have toM : ∀ p t, CC3 p t ∧ isa.eval .ne t = some false → Stage R0 p.m t := by
      rintro p t ⟨h, he⟩
      obtain ⟨xb, pb, qb, dpb, dqb, qib, hpre⟩ := cc3_pre h
      obtain ⟨_, _, _, _, _, _, hz⟩ := h
      have hv : Spec.Rsa.modulusValid p.m.N p.m.k = true := by
        simp only [eval, hz] at he; simpa using he
      exact ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, rfl⟩
    exact (VG.Proof.Bignum.X86_64.ifmaMain_ct M hS hC hQ hP hF hR2 hXm hL hpost).mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ =>
      ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h) fun _ _ h => h

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem ifmaCode_constantTime_of (hS : SetupCT) (hC : ChecksCT) (hQ : QPhaseCT M) (hP : PPhaseCT M)
    (hF : RelCT isa (Two (Stage R5)) (seqs VG.Impl.Rsa.X86_64.Crt.finish) fun _ _ => True) (hR2 : RedcCT M Public.aR2)
    (hXm : RedcCT M Public.aXm) (hL : LoadCT aChunk sQinv sPlen)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code M.mm) := by
  refine RelCT.constantTime ((VG.Proof.Bignum.X86_64.ifmaCode_ct M hS hC hQ hP hF hR2 hXm hL hpost).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ccPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaCode`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: correctness

`CrtIfma.code`, from a state `crtContract` allows, writes `privateCrt` of
its inputs (`ifmaCode_correct`), as `Crt.code` does. Unlike `Crt.code`, it
loads MXCSR (around the vector code), so the calling convention's MXCSR
bits are tracked through it rather than read off the code.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
the parts of its code outside the vector code never load MXCSR (which the
registration file evaluates). -/
theorem ifmaCode_correct (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (CrtIfma.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfma.code M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfma.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (VG.Proof.Bignum.X86_64.bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [VG.Proof.Bignum.X86_64.bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ mx₂ => ?_
  have hpre' := crtPre_of c h₁ hm₂ k₂
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono_mx (by decide +kernel) (fail_ok hpre'.scr hpre'.rdi (by omega)
      (by omega) (by omega) hpre'.hO hpre'.hK hpre'.out hpre'.outSep)
      fun t hp mx => ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩,
        by rw [mx, mx₂, mx₁]⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (VG.Proof.Bignum.X86_64.ifmaMain_ok M hpre' hv hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.IfmaVerified`. -/
section

/-!
# `vg_rsa_private_crt_ifma` on x86-64: verified against the shared contract

`main`'s parts are constant time (those of `vg_rsa_private_crt`, and the
IFMA branch's), so the function is (`ifmaCode_constantTime`); with
correctness (`ifmaCode_correct`) and the contract on the registers and the
stack (`crt_implies`), `CrtIfma.code` is verified (`ifma_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem ifmaCode_constantTime (M : Mont)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code M.mm) :=
  VG.Proof.Bignum.X86_64.ifmaCode_constantTime_of M setup_ct checks_ct
    (qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct (VG.Proof.Bignum.X86_64.redc_ct_R2 M) (VG.Proof.Bignum.X86_64.redc_ct_Xm M) loadArr_ct_pI hpost

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
its code but the vector code never loads MXCSR (which the registration file
evaluates). -/
theorem ifma_verified (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (CrtIfma.code M.mm) (Spec.Rsa.privateCrtContract abi) :=
  Verified.of_correct (VG.Proof.Bignum.X86_64.ifmaCode_correct M hfront hpre hpost hcrt) (VG.Proof.Bignum.X86_64.ifmaCode_constantTime M hpost) crt_implies

end VG.Proof.Bignum.X86_64

end

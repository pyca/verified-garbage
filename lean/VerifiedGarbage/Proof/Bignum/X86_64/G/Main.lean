import VerifiedGarbage.Proof.Bignum.X86_64.G.Branch
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCode

/-!
# RSA with AVX512_IFMA on x86-64, any size: the computation

`IfmaMain` and `IfmaCode` for `CrtIfmaG`: `main` runs `vg_rsa_private_crt`'s
front, then the IFMA branch of the first layout whose sizes the key has
(`branch`, `sizes`), the CRT one if none, and its finish (`main_ok`); `code`
writes `privateCrt` of its inputs (`code_correct`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.CrtIfmaG (Lay lay2048 lay3072 lay4096 sizes branch)
open VG.Proof.Bignum.X86_64 (ofNat_eq_iff mx_ffff CrtReady.of_regs)

variable {l : VG.Impl.Rsa.X86_64.CrtIfmaG.Lay}

/-- `(len + 7) / 8 = v`, for the workspace of a prime of `len` bytes. -/
theorem sz_iff {n v : Nat} (hn : n < 2 ^ 60) (hv : v < 2 ^ 31) :
    ((BitVec.ofNat 64 n + 7) >>> 3 ^^^ BitVec.ofNat 64 v = 0#64) ↔ (n + 7) / 8 = v := by
  have h7 : ((BitVec.ofNat 64 n + 7) >>> 3).toNat = (n + 7) / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      show (7 : BitVec 64).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (a := n + 7) (by omega)]
  rw [BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj, h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v) (by omega)]

/-- `sizes l`: ZF exactly if `n` has `2 W` words and `p` and `q` `W`. -/
theorem sizes_ok (hl : LayOk l) {t : State} {B : Addr} {Z w pl ql : Nat} {minv : BitVec 64}
    (hg : VG.Proof.Bignum.X86_64.Good t B Z w minv) (hpl : word t.mem B (8 * sPlen) = BitVec.ofNat 64 pl)
    (hql : word t.mem B (8 * sQlen) = BitVec.ofNat 64 ql) (hZ : 8 * 32 ≤ Z) (hw : w < 2 ^ 64)
    (hpl' : pl < 2 ^ 60) (hql' : ql < 2 ^ 60) :
    WP isa (.block (sizes l)) t fun t' =>
      t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem ∧
        Keep [.rax, .rdx] t t' := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hl' : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
  have sxW := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show l.W < 2 ^ 31 by omega)
  have sx2W := VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show 2 * l.W < 2 ^ 31 by omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' =>
    t'.zf = some (decide (w = 2 * l.W ∧ (pl + 7) / 8 = l.W ∧ (ql + 7) / 8 = l.W)) ∧ t'.mem = t.mem) (by
      xrun [sizes, State.ea, hdr, hg.rdi, hdrOff, hl' sW (by decide), hl' sPlen (by decide),
        hl' sQlen (by decide), hg.hdr.hw, hpl, hql, sxW, sx2W]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show (0 : BitVec 64) = 0#64 from rfl,
        BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
        ofNat_eq_iff hw (by omega), sx7, sz_iff hpl' (by omega), sz_iff hql' (by omega), and_assoc]) rfl)
    fun t' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- The IFMA area fits in the working space the contract asks for. -/
theorem ifmaZ_of (hl : LayOk l) {Z k pl : Nat} (hzk : 128 * k ≤ Z) (hw : (k + 7) / 8 = 2 * l.W)
    (hp : wsWords pl = l.W) : offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W + 2 * l.D + 8 ≤ Z := by
  rcases hl with rfl | rfl | rfl <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfmaG.lay2048, VG.Impl.Rsa.X86_64.CrtIfmaG.lay3072,
      VG.Impl.Rsa.X86_64.CrtIfmaG.lay4096] at hw hp ⊢ <;>
    unfold offQ slot wsWords hdrBytes tabBytes at * <;>
    simp only [VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.D, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oFin,
      VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oV, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oK1, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oE,
      VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oTab, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oS, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oX,
      VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.oY, VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.NB,
      VG.Impl.Rsa.X86_64.CrtIfmaG.Lay.E] at * <;> omega

/-- What `main` leaves after the front, for a valid modulus. -/
abbrev MainQ (s : State) (B : Addr) (Z k pl ql : Nat) (minv mp mq : BitVec 64) (nb xb pb qb qib dpb dqb : List Byte)
    (t : State) : Prop :=
  PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem sizes_mx (hl : LayOk l) : ((.block (sizes l)) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- `branch l els`: the IFMA branch for the sizes `l`, `els` otherwise. -/
theorem branch_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    {minv mp mq : BitVec 64} {els : Prog isa}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)))
    (mx₀ : t₀.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10)
    (hpre : (seqs (CrtIfmaG.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfmaG.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hels : ∀ t₁, CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) →
      t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 →
      WP isa els t₁ (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb)) :
    WP isa (branch l M.mm els) t₀ (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) := by
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hZq := h.z
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hql8 := hdr_lt_slot (wsWords ql) 8 (show 31 < 32 by decide)
  refine WP.seq (WP.mono_mx (sizes_mx hl) (sizes_ok hl (pl := pl) (ql := ql) hr.good
    (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hPl) (by rw [hr.hfix _ (by decide) (by decide)]; exact h.hQl)
    (by unfold offQ at hZq; omega) (by omega) (by omega) (by omega))
    fun t₁ ⟨zf, me, k₁⟩ mx₁ => ?_)
  have hr₁ := hr.of_regs me k₁
  refine WP.ite _ zf (fun hb => ?_) (fun _ => hels t₁ hr₁ (by rw [mx₁, mx₀]))
  simp only [decide_eq_true_eq] at hb
  obtain ⟨hw, hp, hq⟩ := hb
  obtain ⟨hW1, -⟩ := W_bounds hl
  replace hp : wsWords pl = l.W := by unfold wsWords; omega
  replace hq : wsWords ql = l.W := by unfold wsWords; omega
  exact wp_seqs_append (by simp [CrtIfmaG.pre, CrtIfmaG.prep]) (by simp [CrtIfmaG.post])
    (WP.mono (branchA_ok hl M h hv hr₁ rfl hw hp hq (ifmaZ_of hl h.zk hw hp) hpre) fun t ⟨hd, mxa⟩ =>
      WP.mono (branchB_ok hl M h hv hd rfl hw hp hq hpost) fun t' ⟨hd', mxb⟩ =>
        ⟨hd', by rw [mxb, mxa, mx_ffff, mx₁, mx₀]⟩)

theorem main_eq (mul : Nat → Nat → Nat → Prog isa) : CrtIfmaG.main mul =
    seqs ((nSetup mul ++ primesSetup ++ checks) ++
      ([branch lay2048 mul (branch lay3072 mul (branch lay4096 mul (seqs (qPhase mul ++ pPhase mul))))] ++
        finish)) := by
  simp only [CrtIfmaG.main, List.append_assoc]

/-- `main`, for a valid modulus: `privateCrt`'s result as `vg_rsa_private_crt`
leaves it, and MXCSR's control bits. -/
theorem main_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfmaG.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfmaG.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (CrtIfmaG.main M.mm) s fun t => (∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb)) ∧
      t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  rw [main_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp) (WP.mono_mx hfront (front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ mx₀ => ?_)
  refine wp_seqs_append (by simp) (by simp [finish]) ?_
  have hcrtB : ∀ t₁, CrtReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
      (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) →
      t₁.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 →
      WP isa (seqs (qPhase M.mm ++ pPhase M.mm)) t₁ (MainQ s B Z k pl ql minv mp mq nb xb pb qb qib dpb dqb) :=
    fun t₁ hr₁ mx₁ => WP.mono_mx hcrt (wp_seqs_append (by simp [qPhase]) (by simp [pPhase])
      (WP.mono (qPart_ok M h hv hr₁ rfl) fun _ hq => pPart_ok M h hv hq rfl)) fun t hp' mxc =>
        ⟨hp', by rw [mxc, mx₁]⟩
  refine WP.mono (branch_ok (Or.inl rfl) M h hv hr (by rw [mx₀]) hpre hpost fun t₁ hr₁ mx₁ =>
    branch_ok (Or.inr (Or.inl rfl)) M h hv hr₁ mx₁ hpre hpost fun t₂ hr₂ mx₂ =>
      branch_ok (Or.inr (Or.inr rfl)) M h hv hr₂ mx₂ hpre hpost hcrtB) fun t₂ ⟨hp, mx₂⟩ => ?_
  refine WP.mono_mx (by decide +kernel) (finPart_ok h hv hp rfl) fun t ht mxf => ⟨⟨_, ht, ?_⟩, by rw [mxf, mx₂]⟩
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
the parts of its code outside the vector code never load MXCSR (which the
registration file evaluates). -/
theorem code_correct (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfmaG.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfmaG.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : crtContract.pre s) :
    ∃ t s', Exec isa (CrtIfmaG.code M.mm) s t s' ∧ abiPreserved s s' ∧ crtContract.post s s' := by
  have c := crtCtx_of h
  clear h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa (CrtIfmaG.code M.mm) s fun s' => (gprPreserved s s' ∧ crtContract.post s s') ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hmx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hmx⟩, hp⟩
  unfold CrtIfmaG.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (c := .block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
    List Instr))) (by decide +kernel) (crtHead_ok c) fun t₁ h₁ mx₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono_mx (by decide +kernel) (invalid_ok h₁.rdx h₁.rcx hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
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
    exact WP.mono (main_ok M hpre' hv hfront hpre hpost hcrt) fun t ⟨⟨Mk, hp, hiff⟩, mx⟩ =>
      ⟨crtCode_fin c h₁ hm₂ k₂ hp (fun _ => ⟨hiff, rfl⟩) fun h => absurd h (by rw [hv]; decide),
        by rw [mx, mx₂, mx₁]⟩

end VG.Proof.Bignum.X86_64.G

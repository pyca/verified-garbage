import VerifiedGarbage.Proof.Bignum.AArch64.PubCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest

/-!
# RSAEP from the modulus on AArch64: constant time but for `n` and `e`

`Public.code`'s addresses and branches depend only on the pointers, the
lengths, `n` and `e`: its entry and the check of the modulus, the load of
`m` and `-m⁻¹` (`pcLoad_ct`), `R² mod m` (`r2_ct`), and `rest`
(`pdRest_ct`), for the values of `m` and `R² mod m` that `n` determines
(`pubCode_constantTime`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The public data of `Public.code`: the working space, `k`, the pointers,
`e`'s length, the bytes of `n` and `e`, and the stack pointer. -/
structure CPubP where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  ep : Addr
  ip : Addr
  len : Nat
  nb : List Byte
  eb : List Byte
  sp : Addr

/-- A state the contract allows, with the public data `p`. -/
def CRp (p : CPubP) (s : State) : Prop :=
  pubContract.pre s ∧ s.sp = p.sp ∧ stackArg s 0 = p.B ∧ (stackArg s 1).toNat * 8 = p.Z ∧
    (s.gpr .x3).toNat = p.k ∧ s.gpr .x0 = p.op ∧ s.gpr .x2 = p.np ∧ s.gpr .x4 = p.ep ∧
    s.gpr .x6 = p.ip ∧ (s.gpr .x5).toNat = p.len ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.nb ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = p.eb

/-- After the entry, from a state `s` the contract allows: the working space
changed only inside, the permissions, and the arguments in the header. -/
def Mid (p : CPubP) (t : State) : Prop :=
  ∃ s, CRp p s ∧ InScr p.B p.Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    word t.mem p.B (8 * sOut) = p.op ∧ word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word t.mem p.B (8 * sN) = p.np ∧ word t.mem p.B (8 * sE) = p.ep ∧
    word t.mem p.B (8 * sElen) = BitVec.ofNat 64 p.len ∧ word t.mem p.B (8 * sIn) = p.ip

/-- What `Mid` gives. -/
structure MidCtx (p : CPubP) (t : State) : Prop where
  scr : Scr t p.B p.Z
  z : slot ((p.k + 7) / 8) 8 ≤ p.Z
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  nb : Src t p.B p.Z p.np p.nb
  nl : p.nb.length = p.k
  eb : Src t p.B p.Z p.ep p.eb
  el : p.eb.length = p.len
  L1 : 1 ≤ p.len
  L2 : p.len ≤ p.k
  xb : ∃ xb, Src t p.B p.Z p.ip xb ∧ xb.length = p.k
  out : ∀ j < p.k, InRegions t.wr (p.op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < p.k, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 j)
  hO : word t.mem p.B (8 * sOut) = p.op
  hK : word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k
  hN : word t.mem p.B (8 * sN) = p.np
  hE : word t.mem p.B (8 * sE) = p.ep
  hL : word t.mem p.B (8 * sElen) = BitVec.ofNat 64 p.len
  hIn : word t.mem p.B (8 * sIn) = p.ip

theorem Mid.ctx {p : CPubP} {t : State} (h : Mid p t) : MidCtx p t := by
  obtain ⟨B, Z, k, op, np, ep, ip, len, nb, eb, sp⟩ := p
  obtain ⟨s, ⟨hpre, -, hB, hZ, hk, hop, hnp, hep, hip, hlen, hnb, heb⟩, hi, hrd, hwr, hO, hK, hN, hE, hL, hIn⟩ := h
  have c := pubCtx_of hpre
  have := c.hZ
  have := c.hk1
  subst hB hZ hk hop hnp hep hip hlen hnb heb
  exact ⟨c.hs.congr hwr, by dsimp only; unfold slot hdrBytes; omega, c.hk1, c.hk2, c.hnb.congr hi hrd hwr,
    bytesAt_length _ _ _, c.heb.congr hi hrd hwr, bytesAt_length _ _ _, c.hL1, c.hL2,
    ⟨_, c.hxb.congr hi hrd hwr, bytesAt_length _ _ _⟩, fun j hj => by rw [hwr]; exact c.hout j hj, c.houts,
    hO, hK, hN, hE, hL, hIn⟩

/-- `Mid` after code that changes only memory in the working space outside
the header's arguments. -/
theorem Mid.step {p : CPubP} {t t' : State} (h : Mid p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs t t') : Mid p t' := by
  obtain ⟨s, hs, hi, hrd, hwr, hO, hK, hN, hE, hL, hIn⟩ := h
  have hfx := Fixed.of_frm hf hx
  exact ⟨s, hs, hi.trans (InScr.of_frm hf hz), k.rd.trans hrd, k.wr.trans hwr, (hfx sOut (by decide)).trans hO,
    (hfx sK (by decide)).trans hK, (hfx sN (by decide)).trans hN, (hfx sE (by decide)).trans hE,
    (hfx sElen (by decide)).trans hL, (hfx sIn (by decide)).trans hIn⟩

/-- After the entry and the modulus' check. -/
def CE2p (p : CPubP) (t : State) : Prop :=
  Mid p t ∧ t.gpr .x0 = p.B ∧ t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat

/-- The entry and the modulus' check. -/
theorem pubHead_ok {p : CPubP} {s : State} (h : CRp p s) :
    WP isa (.block (Precomputed.entry true ++ invalid)) s (CE2p p) := by
  obtain ⟨B, Z, k, op, np, ep, ip, len, nb, eb, sp⟩ := p
  have h' := h
  obtain ⟨hpre, -, hB, hZ, hk, hop, hnp, hep, hip, hlen, hnb, heb⟩ := h'
  have c := pubCtx_of hpre
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  subst hB hZ hk hop hnp hep hip hlen hnb heb
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 0) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (pubEntry_ok rfl hw c.ha0) fun t₁ ⟨h0, hO, hN, hK, hE, hL, hIn, ho₁, k₁⟩ => ?_
  have i₁ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hnb₁ := c.hnb.congrK i₁ k₁
  refine WP.mono (invalid_ok (k₁.gpr .x2 (by decide)) (by rw [k₁.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    fun t₂ ⟨hz₂, hm₂, k₂⟩ => ⟨⟨s, h, by rw [hm₂]; exact i₁, (k₁.trans k₂).rd, (k₁.trans k₂).wr,
      by rw [hm₂]; exact hO, by rw [hm₂, hK, ofNat_toNat64], by rw [hm₂]; exact hN, by rw [hm₂]; exact hE,
      by rw [hm₂, hL, ofNat_toNat64], by rw [hm₂]; exact hIn⟩, (k₂.gpr .x0 (by decide)).trans h0, hz₂⟩

theorem pubHead_split : Precomputed.entry true ++ invalid =
    ([.ldrSp .x8 0] : List Instr) ++ ((Precomputed.entry true).drop 1 ++ invalid) := rfl

/-- After the entry's first instruction. -/
def CE1p (p : CPubP) (t : State) : Prop :=
  ∃ s, CRp p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x2 = p.np ∧ t.gpr .x3 = BitVec.ofNat 64 p.k ∧
    WP isa (.block ((Precomputed.entry true).drop 1 ++ invalid)) t (CE2p p)

/-- The load's public data. -/
abbrev CPubP.pc (p : CPubP) : PcPub := ⟨p.B, p.Z, p.k, p.op, p.np, p.nb⟩

theorem ce2_pcL {p : CPubP} {t : State} (h : CE2p p t)
    (he : isa.eval (.zero .x .x9) t = some false) : PcL p.pc t := by
  obtain ⟨hm, h0, hz⟩ := h
  have c := hm.ctx
  refine ⟨c.scr, h0, c.z, c.k1, c.k2, c.hK, c.hN, c.nb, c.nl, ?_⟩
  rw [eval_zero, hz] at he
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k
  · rw [hv] at he; simp at he
  · rfl

/-- After the load of `m` and `-m⁻¹`. -/
def PA (p : CPubP) (t : State) : Prop :=
  ∃ mi : BitVec 64, Mid p t ∧ R2Pre ⟨⟨p.B, p.Z, (p.k + 7) / 8, mi⟩, Spec.Rsa.os2ip p.nb⟩ t

theorem ce2_pa {p : CPubP} {t : State} (h : CE2p p t) (he : isa.eval (.zero .x .x9) t = some false) :
    WP isa (seqs pcLoad) t (PA p) := by
  have hl := ce2_pcL h he
  obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, hn, hnl, hv⟩ := hl
  exact WP.mono (pcLoad_r2 hs h0 hZ hk1 hk2 hK hN hn hnl hv) fun t' ⟨mi, hr, f, k⟩ =>
    ⟨mi, h.1.step f (fun r hr => Nat.le_trans (pcLoadRanges_le _ r hr) hZ) (pcLoadRanges_fixed _) k, hr⟩

/-- `rest`'s public data. -/
def CPubP.d (p : CPubP) : DPub :=
  ⟨p.B, p.Z, p.k, p.op, p.ep, p.ip, p.len, p.eb, Spec.Rsa.os2ip p.nb,
    2 ^ (128 * ((p.k + 7) / 8)) % Spec.Rsa.os2ip p.nb⟩

/-- `R² mod m`, then `rest`'s hypotheses. -/
theorem pa_r2 {q : CPubP × BitVec 64} {t : State}
    (h : Mid q.1 t ∧ R2Pre ⟨⟨q.1.B, q.1.Z, (q.1.k + 7) / 8, q.2⟩, Spec.Rsa.os2ip q.1.nb⟩ t) :
    WP isa (seqs (r2Steps Mont.base.mm)) t (DRel q.1.d) := by
  obtain ⟨⟨B, Z, k, op, np, ep, ip, len, nb, eb, sp⟩, mi⟩ := q
  obtain ⟨hm, hr⟩ := h
  obtain ⟨hg, hw, hw', hn, hinv, hodd, hlo⟩ := hr
  dsimp only at hg hw hw' hn hinv hodd hlo hm ⊢
  have hsn : B.toNat + Z ≤ 2 ^ 64 := hg.1.scr.nowrap
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := hg.2
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hg1 : Good t B Z ((k + 7) / 8) mi := hg.1
  refine WP.mono (r2_ok Mont.base hg1 hZ hw hw' hn hinv hodd hlo) fun t' ⟨hg', hlt, hr2, f, k'⟩ => ?_
  show ∃ xb, PdPre t' B Z k op ep ip len eb xb (Spec.Rsa.os2ip nb) (2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb)
  have c := (hm.step f (fun r hr => Nat.le_trans (r2Ranges_le _ r hr) hZ) (r2Ranges_fixed _) k').ctx
  obtain ⟨xb, hx, hxl⟩ := c.xb
  have h64 : 2 ^ 64 ≤ 2 ^ (64 * ((k + 7) / 8 - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt' : wv t'.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) < Spec.Rsa.os2ip nb := hlt
  refine ⟨xb, ?_⟩
  exact
    { scr := hg'.scr, x0 := hg'.x0, z := c.z, k1 := c.k1, k2 := c.k2, hO := c.hO, hK := c.hK,
      hE := c.hE, hL := c.hL, hIn := c.hIn, hW := hg'.hdr.hw, hb := hg'.hdr.harr,
      n := by rw [f.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hn,
      r := by rw [← Nat.mod_eq_of_lt hlt', hr2, ← Nat.pow_add]; congr 2; omega, odd := hodd,
      n1 := by omega, rlt := Nat.mod_lt _ (by omega), x := hx, e := c.eb, xl := hxl, el := c.el, L1 := c.L1, L2 := c.L2,
      out := c.out, outSep := c.outSep }

/-- `Public.code` leaks the same in runs that agree on the public data. -/
theorem pubCode_ct : RelCT isa (Two CRp) Public.code fun _ _ => True := by
  unfold Public.code
  refine RelCT.seq (R := Two CE2p) ?_ ?_
  · rw [pubHead_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CE1p) [] (fun _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide) ?_)
      (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]
        · rw [c₁, c₂]) (by taint_decide) fun p t ⟨_, _, _, _, _, hw⟩ => hw))
    intro p s hs
    have hh := pubHead_ok hs
    rw [pubHead_split] at hh
    have c := pubCtx_of hs.1
    have ha0' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := c.ha0
    have hB' : s.mem.readW s.sp 64 = stackArg s 0 := by
      simp only [stackArg, stackArgAddr, Nat.mul_zero, off_zero]
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 0)
      (by brun [exec_ldrSp_x' _ (show 0 % 8 = 0 ∧ 0 < 32768 by decide) ha0', hB']) (by decide) (by decide)
        (by decide +kernel))) fun t ⟨hw', h8, k⟩ => ⟨s, hs, h8.trans hs.2.2.1,
          (k.gpr .x2 (by decide)).trans hs.2.2.2.2.2.2.1,
          by rw [k.gpr .x3 (by decide), ← hs.2.2.2.2.1, ofNat_toNat64], hw'⟩
  refine two_ite (fun p s₁ s₂ ⟨_, _, z₁⟩ ⟨_, _, z₂⟩ => by rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold Precomputed.fail
    refine RelCT.seq (two_piece (Ψ := fun (p : CPubP) t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 p.k) [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.1, h₂.1.2.1])
      (by taint_decide) ?_)
      (two_taint [.x1, .x2] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    rintro p t ⟨⟨hm, h0, -⟩, -⟩
    have c := hm.ctx
    have hn := c.scr.nowrap
    have hZ := c.z
    obtain ⟨g0, g8⟩ := slot0_ge ((p.k + 7) / 8)
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := fun i hi => c.scr.ld (by omega)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 p.k) (by
      brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
        hl sK (by decide), c.hO, c.hK]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨h, _⟩ => h
  · -- `main`: the load of `m` and `-m⁻¹`.
    refine RelCT.seqs_append (by simp [pcLoad]) (by simp [r2Steps]) (RelCT.seq (R := Two PA)
      (two_post (pcLoad_ct.mono (fun _ _ h => two_bind (fun p s₁ s₂ h₁ h₂ => ⟨p.pc, ce2_pcL h₁.1 h₁.2,
        ce2_pcL h₂.1 h₂.2⟩) h) fun _ _ _ => trivial) fun p t h => ce2_pa h.1 h.2) ?_)
    -- `R² mod m`, for the same `-m⁻¹`.
    refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two fun (p : CPubP) t => DRel p.d t)
      ?_ ?_)
    · have h := two_post (Φ := fun (q : CPubP × BitVec 64) t =>
          Mid q.1 t ∧ R2Pre ⟨⟨q.1.B, q.1.Z, (q.1.k + 7) / 8, q.2⟩, Spec.Rsa.os2ip q.1.nb⟩ t)
        (Ψ := fun q t => DRel q.1.d t)
        (two_map (fun q => (⟨⟨q.1.B, q.1.Z, (q.1.k + 7) / 8, q.2⟩, Spec.Rsa.os2ip q.1.nb⟩ : R2Pub))
          (fun _ _ h => h.2) (r2_ct Mont.base)) fun _ _ h => pa_r2 h
      exact h.mono (fun _ _ hp => two_bind (fun p s₁ s₂ ⟨mi₁, m₁, r₁⟩ ⟨mi₂, m₂, r₂⟩ => by
          obtain rfl := pc3_minv (p := p.pc) r₁ r₂
          exact ⟨(p, mi₁), ⟨m₁, r₁⟩, m₂, r₂⟩) hp)
        fun _ _ h => two_bind (fun q s₁ s₂ h₁ h₂ => ⟨q.1, h₁, h₂⟩) h
    -- `rest`.
    rw [seqs_one]
    exact two_map CPubP.d (fun _ _ h => h) (pdRest_ct (M := Mont.base))

/-- The public data of a state. -/
def cpubOfP (s : State) : CPubP :=
  ⟨stackArg s 0, (stackArg s 1).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2, s.gpr .x4, s.gpr .x6,
    (s.gpr .x5).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat, s.sp⟩

/-- `Public.code` is constant time but for `n` and `e`. -/
theorem pubCode_constantTime : ConstantTime isa pubContract.pre pubContract.pub Public.code := by
  refine RelCT.constantTime (pubCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨cpubOfP s₁, ?_, ?_, hp.1⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hsp, a0, -, a2, a3, a4, a5, a6, -, s0, s1, hn, he⟩ := hp
    exact ⟨h₂, hsp.symm, s0.symm, by rw [← s1]; rfl, by rw [← a3]; rfl, a0.symm, a2.symm, a4.symm, a6.symm,
      by rw [← a5]; rfl, hn.symm, he.symm⟩

end VG.Proof.Bignum.AArch64

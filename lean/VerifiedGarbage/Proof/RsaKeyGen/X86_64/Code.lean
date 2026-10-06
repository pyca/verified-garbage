import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-!
# A candidate on x86-64: correctness

`code`, from a state `candContract` allows, ends as `candidateOp`
(`code_correct`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `code` uses of its precondition, for the scratch space `B`
(`arg 3`) of `Z` bytes and the prime's length `L`. -/
structure KCtx (s : State) : Prop where
  k1 : 32 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 512
  k8 : (s.gpr .rsi).toNat % 8 = 0
  el1 : 1 ≤ (s.gpr .r8).toNat
  el8 : (s.gpr .r8).toNat ≤ 8
  pl : (arg s 0).toNat = 0 ∨ (arg s 0).toNat = (s.gpr .rsi).toNat
  hZ : 128 * (s.gpr .rsi).toNat ≤ (arg s 4).toNat * 8
  hs : Scr s (arg s 3) ((arg s 4).toNat * 8)
  ha : ∀ i < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  hsep : ∀ m', Outside (arg s 3) 0 (8 * 32) s.mem m' → ∀ i < 3, m'.readW (stackArgAddr s i) 64 = stackArg s i
  esrc : Src s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rcx) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  psrc : Src s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .r9) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
  rsrc : Src s (arg s 3) ((arg s 4).toNat * 8) (arg s 1) (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat)
  ou : OutUp s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat
  doe : ∀ i < (s.gpr .r8).toNat, ∀ j < (s.gpr .rsi).toNat,
    s.gpr .rcx + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  dop : ∀ i < (arg s 0).toNat, ∀ j < (s.gpr .rsi).toNat,
    s.gpr .r9 + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  dor : ∀ i < (arg s 2).toNat, ∀ j < (s.gpr .rsi).toNat,
    arg s 1 + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j
  hret : ∀ b < 8, (arg s 4).toNat * 8 ≤ ofs (arg s 3) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    (∀ c < 8, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdx + BitVec.ofNat 64 c) ∧
    ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem stackArgAddr_add (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  simp only [stackArgAddr]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem kctx_of {s : State} (h : candPre s) : KCtx s := by
  simp only [candPre] at h
  obtain ⟨hsp, hrd, hwr, dOu, dOe, dOp, dOr, dOs, dOa, dUe, dUp, dUr, dUs, dUa, des, dps, drs, dsa,
    dRo, dRu, dRe, dRp, dRr, dRs, dRa, wO, wU, wE, wP, wR, wS, hk, hl1, hl8, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2, hk8⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (arg s 3) ((arg s 4).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have ha : ∀ i < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi =>
    ⟨⟨stackArgAddr s 0, 40⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_add s i]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : ∀ m', Outside (arg s 3) 0 (8 * 32) s.mem m' → ∀ i < 3, m'.readW (stackArgAddr s i) 64 = stackArg s i :=
    fun m' ho i hi => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * i + b) (by omega) (by omega))
      rw [stackArgAddr_add s i, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega))
  have he := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega) des
  have hp := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega) dps
  have hr := src_of_region (s := s) (B := arg s 3) (Z := (arg s 4).toNat * 8) (by rw [hrd]; simp) (by omega) drs
  have ho : OutUp s (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat := by
    refine ⟨⟨⟨s.gpr .rdx, 8⟩, by rw [hwr]; simp, ?_⟩, fun b hb => out_scr dUs (contains_byte _ (by omega) (by omega)),
      fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
      fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun j hj b hb he => ?_⟩
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · exact dOu _ (contains_byte _ (by omega) (by omega)) (by rw [he]; exact contains_byte _ (by omega) (by omega))
  refine ⟨hk1, hk2, hk8, hl1, hl8, hpl, by omega, hs, ha, hsep, he, hp, hr, ho,
    fun i hi j hj hh => dOe _ (contains_byte (s.gpr .rdi) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega)),
    fun i hi j hj hh => dOp _ (contains_byte (s.gpr .rdi) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega)),
    fun i hi j hj hh => dOr _ (contains_byte (s.gpr .rdi) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun c hc' he => dRu _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega)),
    fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- The postcondition, from how the candidate ended after the entry and the
zeros to `out`. -/
theorem candEnd_post {s t₃ t : State} (c : KCtx s)
    (hsv : ∀ i < 6, word t₃.mem (arg s 3) (8 * i) = s.gpr (saved.getD i .rax))
    (hz : ∀ i < (s.gpr .rsi).toNat, t₃.mem (s.gpr .rdi + BitVec.ofNat 64 i) = 0)
    (hret : ∀ b < 8, t₃.mem (s.gpr .rsp + BitVec.ofNat 64 b) = s.mem (s.gpr .rsp + BitVec.ofNat 64 b))
    (hsp : t₃.gpr .rsp = s.gpr .rsp)
    (h : CandEnd t₃ t (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat
      (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) (candRes s)) :
    gprPreserved s t ∧ candPost s t := by
  have key : ∀ {st u : Nat} {outv : Option Nat}, st < 4 →
      KEnd t₃ t (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat st u outv →
      gprPreserved s t ∧ ((t.gpr .rax).setWidth 32).toNat = st ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat = (match outv with
        | some c => Spec.Rsa.i2osp c (s.gpr .rsi).toNat
        | none => List.replicate (s.gpr .rsi).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 u] := by
    intro st u outv hst hk
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hk.saved 0 (by decide)).trans (hsv 0 (by decide))
      · exact (hk.saved 1 (by decide)).trans (hsv 1 (by decide))
      · exact (hk.keep.gpr (by decide)).trans hsp
      · exact (hk.saved 2 (by decide)).trans (hsv 2 (by decide))
      · exact (hk.saved 3 (by decide)).trans (hsv 3 (by decide))
      · exact (hk.saved 4 (by decide)).trans (hsv 4 (by decide))
      · exact (hk.saved 5 (by decide)).trans (hsv 5 (by decide))
    · obtain ⟨hZx, hnu, hno⟩ := c.hret b (by omega)
      rw [hk.frame _ hZx hnu hno, hret b (by omega)]
    · rw [hk.rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · show outBytes t.mem _ _ = _
      have := hk.out
      cases outv
      · rw [this]
        show List.map _ _ = _
        rw [List.map_congr_left fun i hi => hz i (List.mem_range.mp hi)]; simp [List.map_const']
      · exact this
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
        hk.used]
  unfold candPost
  rcases hres : candRes s with _ | ⟨_ | _ | _, rest⟩ <;> rw [hres] at h <;> simp only [CandEnd] at h
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, hw⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩

theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : k ≤ n) :
    (Spec.Rsa.bytesAt m p n).take k = Spec.Rsa.bytesAt m p k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- A buffer whose octets did not change. -/
theorem Src.congr' {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : ∀ i < bs.length, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i)) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm i hi]; exact h.val i hi, h.out⟩

/-- After the zeros to `out` and the length check, from the state `t₁` after
the entry. -/
structure Front (s t₁ t₃ : State) : Prop where
  cf : t₃.cf = some (decide ((arg s 2).toNat < (s.gpr .rsi).toNat))
  zero : ∀ i < (s.gpr .rsi).toNat, t₃.mem (s.gpr .rdi + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t₃.mem x = t₁.mem x
  keep : Keep [.rsi, .rcx, .rax] t₁ t₃

/-- `zeroOut` and the length check. -/
theorem front_ok {s t₁ : State} (c : KCtx s) (he : EntryPost s t₁ (arg s 3)) :
    WP isa (.seq zeroOut (.block [.mov .rax (.mem (hdr kRandLen)), .mov .rcx (.mem (hdr kLen)),
      .alu .cmp .rax (.reg .rcx)])) t₁ (Front s t₁) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hs₁ := hs.congr he.keep.2.2
  refine WP.seq (WP.mono (zeroOut_ok (k := (s.gpr .rsi).toNat) hs₁ he.rdi (by omega) (by omega) (by omega) he.out
    (by rw [he.len, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (fun j hj => by rw [he.keep.2.2]; exact c.ou.outw j hj))
    fun t₂ ⟨hz₂, hf₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hw₂ : ∀ i < 32, word t₂.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hf₂ _ fun j hj he' => by
      have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega)] at this; omega
  have hdi₂ : t₂.gpr .rdi = arg s 3 := (k₂.gpr (by decide)).trans he.rdi
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (arg s 3) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.cf = some (decide ((arg s 2).toNat < (s.gpr .rsi).toNat)) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ kRandLen (by decide), hl₂ kLen (by decide), hw₂ kRandLen (by decide),
      hw₂ kLen (by decide), he.rlen, he.len]) rfl) fun t₃ ⟨⟨hcf, hm₃⟩, k₃⟩ =>
    ⟨hcf, fun i hi => by rw [hm₃]; exact hz₂ i hi, fun x hx => by rw [hm₃]; exact hf₂ x hx, (k₂.trans k₃).mono (by decide)⟩

/-- The header words survive the zeros to `out`. -/
theorem Front.word {s t₁ t₃ : State} (c : KCtx s) (h : Front s t₁ t₃) {i : Nat} (hi : i < 32) :
    word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  exact Mem.readW_congr fun b hb => h.frame _ fun j hj he' => by
    have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega)] at this; omega

/-- What `kMain` needs, after the entry, the zeros and the length check. -/
theorem mainCtx_of {s t₁ t₃ : State} {w : Nat} (c : KCtx s) (he : EntryPost s t₁ (arg s 3)) (h : Front s t₁ t₃)
    (hw : (s.gpr .rsi).toNat = 8 * w) (hlt : (s.gpr .rsi).toNat ≤ (arg s 2).toNat) :
    MainCtx t₃ (arg s 3) ((arg s 4).toNat * 8) (8 * w) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r9)
      (arg s 1) (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat) (Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hk8 := c.k8
  have k13 : Keep [.r11, .rax, .rdi, .rsi, .rcx] s t₃ := (he.keep.trans h.keep).mono (by decide)
  have hs₃ := hs.congr k13.2.2
  have hdi₃ : t₃.gpr .rdi = arg s 3 := (h.keep.gpr (by decide)).trans he.rdi
  have hrs : ∀ i < 32, word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi => h.word c hi
  have hhi : ∀ x, 8 * 32 ≤ ofs (arg s 3) x → (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      t₃.mem x = s.mem x := fun x hx hx' => by
    rw [h.frame x hx', he.frame x (Or.inr (by omega))]
  have ho₃ : OutUp t₃ (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat :=
    c.ou.congr k13.2.2
  have hsrc : ∀ {p : Addr} {bs : List Byte}, Src s (arg s 3) ((arg s 4).toNat * 8) p bs →
      (∀ i < bs.length, ∀ j < (s.gpr .rsi).toNat, p + BitVec.ofNat 64 i ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      Src t₃ (arg s 3) ((arg s 4).toNat * 8) p bs := fun {p bs} h hd =>
    VG.Proof.RsaKeyGen.X86_64.Src.congr' h (fun i hi => hhi _ (by have := h.out i hi; omega) (hd i hi)) k13.2.1 k13.2.2
  refine ⟨hs₃, hdi₃, by rw [show 8 * w / 8 = w by omega]; unfold slot aTab hdrBytes; omega, by omega,
    by omega, by omega, by rw [hrs _ (by decide)]; exact he.out, ?_, by rw [hrs _ (by decide)]; exact he.usedP,
    by rw [hrs _ (by decide)]; exact he.e, ?_, by rw [hrs _ (by decide)]; exact he.p, ?_,
    by rw [hrs _ (by decide)]; exact he.rand, ?_, hsrc c.esrc (fun i hi => c.doe i (by rwa [bytesAt_length] at hi)),
    hsrc c.psrc (fun i hi => c.dop i (by rwa [bytesAt_length] at hi)),
    hsrc c.rsrc (fun i hi => c.dor i (by rwa [bytesAt_length] at hi)), by rw [bytesAt_length]; exact c.el1,
    by rw [bytesAt_length]; exact c.el8, by rw [bytesAt_length, ← hw]; exact c.pl,
    by rw [bytesAt_length]; exact (arg s 2).isLt, by rw [bytesAt_length, ← hw]; exact hlt, by rw [← hw]; exact ho₃⟩
  · rw [hrs _ (by decide), he.len, ← hw, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.elen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.plen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hrs _ (by decide), he.rlen, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem code_correct (M : Mont) (hmx : (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (h : candContract.pre s) : ∃ t s', Exec isa (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  have c := kctx_of h
  suffices hwp : WP isa (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm) s fun s' => gprPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hk8 := c.k8
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .rsi).toNat = 8 * w := ⟨(s.gpr .rsi).toNat / 8, by omega⟩
  have hhw : ∀ i < 32, InRegions s.wr (off (arg s 3) (8 * i)) 8 := fun i hi => hs.st (by omega)
  unfold VG.Impl.RsaKeyGen.X86_64.Candidate.code
  simp only [seqs]
  refine WP.seq (WP.mono (kEntry_ok rfl hhw c.ha c.hsep) fun t₁ he => ?_)
  refine WP.assoc (WP.seq (WP.mono (front_ok c he) fun t₃ hf => ?_))
  -- Facts at `t₃`.
  have k13 : Keep [.r11, .rax, .rdi, .rsi, .rcx] s t₃ := (he.keep.trans hf.keep).mono (by decide)
  have hs₃ := hs.congr k13.2.2
  have hdi₃ : t₃.gpr .rdi = arg s 3 := (hf.keep.gpr (by decide)).trans he.rdi
  have hw₃ : ∀ i < 32, word t₃.mem (arg s 3) (8 * i) = word t₁.mem (arg s 3) (8 * i) := fun i hi => hf.word c hi
  have hsv : ∀ i < 6, word t₃.mem (arg s 3) (8 * i) = s.gpr (saved.getD i .rax) := fun i hi =>
    (hw₃ i (by omega)).trans (he.saved i hi)
  have hhi : ∀ x, 8 * 32 ≤ ofs (arg s 3) x → (∀ j < (s.gpr .rsi).toNat, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      t₃.mem x = s.mem x := fun x hx hx' => by
    rw [hf.frame x hx', he.frame x (Or.inr (by omega))]
  have hret : ∀ b < 8, t₃.mem (s.gpr .rsp + BitVec.ofNat 64 b) = s.mem (s.gpr .rsp + BitVec.ofNat 64 b) :=
    fun b hb => hhi _ (by have := (c.hret b hb).1; omega) (c.hret b hb).2.2
  have hsp : t₃.gpr .rsp = s.gpr .rsp := k13.gpr (by decide)
  have ho₃ : OutUp t₃ (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rsi).toNat :=
    c.ou.congr k13.2.2
  have h8 : 8 * 32 ≤ (arg s 4).toNat * 8 := by omega
  refine WP.ite (decide ((arg s 2).toNat < (s.gpr .rsi).toNat)) (by simp [eval, hf.cf]) (fun hlt => ?_) (fun hlt => ?_)
  · -- Too few octets.
    simp only [decide_eq_true_eq] at hlt
    refine WP.mono (finNone_ok hs₃ hdi₃ h8 (by rw [hw₃ kUsedP (by decide)]; exact he.usedP) ho₃.upw ho₃.upZ)
      fun t ht => candEnd_post c hsv hf.zero hret hsp ?_
    have hnone : candRes s = none := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega), ite_f (by rw [bytesAt_length]; omega)]
    rw [hnone]; exact KEnd.of_fin ho₃ ht
  · -- `kMain`.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hlt
    refine WP.mono (kMain_ok M (mainCtx_of c he hf hw hlt)) fun t ht => candEnd_post c hsv hf.zero hret hsp ?_
    have hres : candRes s = VG.Proof.RsaKeyGen.afterDraw (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat))
        (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (arg s 0).toNat))
        (Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat).take (8 * w))))
        ((Spec.Rsa.bytesAt s.mem (arg s 1) (arg s 2).toNat).drop (8 * w)) := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega), ite_t (by rw [bytesAt_length]; omega),
        seg_zero, show 8 * (8 * w) = 64 * w by omega]
    rw [hres, ← hw]
    rw [← hw] at ht
    exact ht

end VG.Proof.RsaKeyGen.X86_64

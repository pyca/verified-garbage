module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Trial
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Loop
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Hdr
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load

/-!
# DSA's probable-prime test on PPC64LE: the body

`BIn σ s`: what the body reads at `s` (after the candidate's load), from the
call's state `σ`: the precondition, the working space at `B = ws + keyOff`
(`Env`) with its header (`Hdr`), the candidate in array 0, the table, and the
tape as at the call. `BOut`: after it, `hStat` holds the status of the test
(`Spec.Dsa.probablePrime`), `hUsed` the octets read when it decided, `r31` is
`B`, and memory changed only in the working space and the round's stack.

`body_ok`: trial division (`trial_ok`); then a composite (`comp_ok`), or
`montPrep` and the blinded Miller–Rabin loop (`mr_ok`, `millerRabin_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Impl.MillerRabin.PPC64LE.Blinded (hUni hTopOff)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off slot Frm ofs)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE.Blinded (BCtx LKeep MOut millerRabin_ok)

/-- The candidate. -/
abbrev cand (bits : Nat) (σ : State) : Nat := Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .r3)

/-- The tape. -/
abbrev tape (σ : State) : Spec.RsaKeyGen.Rand := Spec.Rsa.bytesAt σ.mem (σ.gpr .r5) (σ.gpr .r6).toNat

/-- The test's result. -/
abbrev res (bits : Nat) (σ : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (cand bits σ) (tape σ)

/-- What the body reads. -/
structure BIn (bits : Nat) (σ s : State) : Prop where
  hb : Bits bits
  cin : CIn bits σ
  env : Env s (wsB σ) (8 * keyWords bits) (words bits)
  hdr : Hdr bits (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r6) s.mem
  cand : arr s.mem (wsB σ) (words bits) 0 = cand bits σ
  tab : Tab (σ.syms TrialTable32.symbol) s.mem
  tabR : ⟨σ.syms TrialTable32.symbol, 8192⟩ ∈ s.rd
  tape : Spec.Rsa.bytesAt s.mem (σ.gpr .r5) (σ.gpr .r6).toNat = tape σ
  syms : s.syms = σ.syms
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr

/-- After the body. -/
structure BOut (bits : Nat) (σ s t : State) : Prop where
  r31 : t.gpr .r31 = wsB σ
  stat : word t.mem (wsB σ) (8 * hStat) = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  used : ∀ b rest, res bits σ = some (b, rest) →
    word t.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 ((σ.gpr .r6).toNat - rest.length)
  frame : Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 176] s.mem t.mem
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- A byte of the working space lies in `ws`. -/
theorem inW {bits : Nat} {σ : State} (h : CIn bits σ) {x : Addr}
    (hx : ofs (wsB σ) x < 8 * keyWords bits) : (cW σ).Contains x 1 := by
  have hsz := h.size
  have hfw := h.fw
  simp only [Region.Contains, ofs, wsB, keyOff] at hx hsz ⊢
  have : (x - σ.gpr .r3).toNat = (x - (σ.gpr .r3 + BitVec.ofNat 64 552)).toNat + 552 := by bv_omega
  omega

/-- The candidate's facts the tests need. -/
theorem cand_facts {bits : Nat} {σ : State} (hb : Bits bits) (h : CIn bits σ) :
    8161 < cand bits σ ∧ 3 ≤ cand bits σ ∧ cand bits σ % 2 = 1 ∧
      Spec.RsaKeyGen.bitLength (cand bits σ - 1) = bits := by
  have hbl := h.bl
  have hodd := h.odd
  have hs := shape_of hb
  have hbig := hs.big
  obtain ⟨hlo, -⟩ := (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mp hbl
  have : 2 ^ 13 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) hbig
  dsimp only [cand]
  refine ⟨by omega, by omega, hodd, VG.Proof.Dsa.Generation.predecessor_bits (by omega) hodd hbl⟩

/-- A change of bytes `[d, d + n)` of a region of `Z ≥ d + n` bytes at `B`. -/
theorem frame_outside {B : Addr} {Z d n : Nat} {rs : List Region} {m m' : Mem}
    (ho : VG.Proof.Bignum.Outside B d n m m') (hd : d + n ≤ Z) : Frame (⟨B, Z⟩ :: rs) m m' := fun x hx => by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains] at this
  exact ho x (.inr (by simp only [ofs]; omega))

/-- A composite: `hStat := 2`. -/
theorem comp_ok {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true) :
    WP isa (.block [.li .r3 2, sth .r3 hStat]) s (BOut bits σ s) := by
  have e := h.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts h.hb h.cin
  have hres : res bits σ = some (false, tape σ) := by
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, h.cin.bl, hc]; rfl
  generalize hB : wsB σ = B at e hs hnw
  refine WP.mono (WP.keep [.r3] (Q := fun x => x.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2))
    (by simp only [sth, hStat]; prun [e.h31, hs.st (d := 160) (n := 8) (by omega)]) (by decide)) fun x ⟨xm, kx⟩ => ?_
  subst hB
  have ho := VG.Proof.Bignum.writeW_outside s.mem (wsB σ) (d := 8 * hStat) (BitVec.ofNat 64 2)
    (by simp only [hStat]; omega)
  refine ⟨(kx.gpr _ (by decide)).trans e.h31, by rw [xm, VG.Proof.Bignum.word_writeW_self, hres]; rfl,
    fun b rest hr => ?_, by rw [xm]; exact frame_outside ho (by simp only [hStat]; omega), kx.sp.trans h.sp,
    kx.rd.trans h.rd, kx.wr.trans h.wr⟩
  rw [hres] at hr
  cases hr
  rw [xm, Frm.word_eq (rs := [(8 * hStat, 8)]) (fun y hy => ho y (hy _ List.mem_cons_self))
    (by simp only [hStat, hUsed, List.mem_singleton, forall_eq]; omega) (by simp only [hUsed]; omega), h.hdr.used]
  simp only [tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, Nat.sub_self]

/-- The header's words lie apart from what `montPrep` writes. -/
theorem hdr_apart (w : Nat) :
    ∀ d ∈ hdrWords, ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.Search.mpRanges w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rw [hdrWords_eq]
  intro d hd r hr
  simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr hd
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.PPC64LE.aE] <;> omega

/-- What `montPrep` writes lies within the working space. -/
theorem mp_within (w : Nat) :
    ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.Search.mpRanges w, r.1 + r.2 ≤ 256 + 28 * (8 * (w + 2)) := by
  intro r hr
  simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.PPC64LE.aE] <;> omega

/-- A byte of the tape lies outside the working space. -/
theorem tape_out {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < (σ.gpr .r6).toNat) :
    ¬ ofs (wsB σ) (σ.gpr .r5 + BitVec.ofNat 64 i) < 8 * keyWords bits := fun hx =>
  h.wR _ (inW h hx) (by
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := (σ.gpr .r6).isLt; omega)]; omega)

/-- After `montPrep`: the blinded loop's context, no octets read, the tape,
and memory changed only in the working space. -/
theorem montPrep_ctx {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa montPrep s fun v =>
      BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .r5) (σ.gpr .r6).toNat
        ((bits - 1) / 64) (topBits bits) (checks bits) ∧
      word v.mem (wsB σ) (8 * hUsed) = BitVec.ofNat 64 0 ∧
      Spec.Rsa.bytesAt v.mem (σ.gpr .r5) (σ.gpr .r6).toNat = tape σ ∧ v.sp = σ.sp ∧ v.rd = σ.rd ∧ v.wr = σ.wr ∧
      Frame [⟨wsB σ, 8 * keyWords bits⟩, below σ.sp 176] s.mem v.mem := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ : 256 + 28 * (8 * (words bits + 2)) ≤ 8 * keyWords bits := e.hZ
  have sh := shape_of h.hb
  have cin := h.cin
  obtain ⟨-, h3, hodd, hbl1⟩ := cand_facts h.hb cin
  have hch : checks bits < 2 ^ 63 := by rcases h.hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.montPrep_ok e h.cand hodd h3)
    fun v ⟨⟨ev, v0, vinv, _, _, v1, v9, v10, vE, vl, vO⟩, kv⟩ => ?_
  have hd : Hdr bits (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r6) v.mem :=
    h.hdr.keep fun d hdm => Frm.word_eq (fun x hx => vO x hx) (hdr_apart _ d hdm) (by
      rw [hdrWords_eq] at hdm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hdm
      rcases hdm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> omega)
  have prep : Prep v (wsB σ) (keyWords bits) (words bits) (cand bits σ) :=
    ⟨ev, hd.len, hd.w, hd.stride, hd.arr, v0, h3, hodd, vinv, v1, v9, v10, vE, vl⟩
  have vsp : v.sp = σ.sp := kv.sp.trans h.sp
  have vrd : v.rd = σ.rd := kv.rd.trans h.rd
  have bc : BCtx v (wsB σ) (keyWords bits) (words bits) (cand bits σ) (σ.gpr .r5) (σ.gpr .r6).toNat
      ((bits - 1) / 64) (topBits bits) (checks bits) := by
    refine ⟨prep, hd.rand, by rw [hd.randLen, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [hd.k, sh.hdraw],
      hd.top, by rw [hd.topOff, sh.hoff], hd.checks, sh.t0, sh.tw, sh.b1, sh.b64, by rw [hbl1]; exact sh.bt, hch,
      (σ.gpr .r6).isLt, fun i hi => ⟨_, List.mem_append_left _ (vrd ▸ cin.rd), ?_⟩,
      fun i hi x hx he => tape_out cin hi (he ▸ hx), by rw [vsp]; exact cin.spLo,
      fun a ha hb => cin.sW a (by rw [vsp] at ha; exact ha) (inW cin (by simp only [Region.Contains] at hb; exact hb)),
      fun i hi hc => cin.sR _ (by rw [vsp] at hc; exact hc) ?_⟩ <;>
    · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by have := (σ.gpr .r6).isLt; omega)]; omega
  have htape : Spec.Rsa.bytesAt v.mem (σ.gpr .r5) (σ.gpr .r6).toNat = tape σ := by
    rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    refine vO _ fun r hr => .inr ?_
    have h1 := tape_out cin hi
    have h2 := mp_within _ r hr
    change r.1 + r.2 ≤ ofs (wsB σ) _
    omega
  exact ⟨bc, hd.used, htape, vsp, vrd, kv.wr.trans h.wr,
    (VG.Proof.Mont.Outs.frame vO fun r hr => Nat.le_trans (mp_within _ r hr) hZ).mono (by simp)⟩

/-- No small prime divides: `montPrep` and the blinded Miller–Rabin loop. -/
theorem mr_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s)
    (hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false) :
    WP isa (.seq montPrep (VG.Impl.MillerRabin.PPC64LE.Blinded.millerRabin Ri.name Ri.code)) s (BOut bits σ s) := by
  have sh := shape_of h.hb
  have cin := h.cin
  obtain ⟨hbig, -, hodd, -⟩ := cand_facts h.hb cin
  refine WP.seq (WP.mono (montPrep_ctx h) fun v ⟨bc, hu, htape, vsp, vrd, vwr, f1⟩ => ?_)
  refine WP.mono (millerRabin_ok Ri bc hu htape) fun t mo => ?_
  have hres : res bits σ = Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (cand bits σ) (checks bits)
      (Spec.Rsa.splitTwos (cand bits σ - 1)).1 (Spec.Rsa.splitTwos (cand bits σ - 1)).2) (1, 0) (tape σ) := by
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega) hodd, cin.bl, hc, sh.hchecks]; rfl
  refine ⟨mo.1.prep.env.h31, by rw [hres]; exact mo.2.1, fun b rest hr => mo.2.2 b rest (hres ▸ hr), ?_,
    mo.1.sp.trans vsp, mo.1.rd.trans vrd, mo.1.wr.trans vwr⟩
  exact f1.trans (by rw [← vsp]; exact mo.1.frame)

/-- Trial division keeps the body's context. -/
theorem bin_after_trial {bits : Nat} {σ s u : State} (h : BIn bits σ s) (um : u.mem = s.mem)
    (ug : ∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) (urd : u.rd = s.rd) (uwr : u.wr = s.wr) (usp : u.sp = s.sp)
    (usy : u.syms = s.syms) : BIn bits σ u := by
  have e := h.env
  exact ⟨h.hb, h.cin, ⟨e.hs.congr uwr, (ug _ (by decide)).trans e.h10,
      (ug _ (by decide)).trans e.h29, (ug _ (by decide)).trans e.h11, (ug _ (by decide)).trans e.h31, e.hw, e.hw',
      e.hZ⟩, by rw [um]; exact h.hdr,
    by rw [um]; exact h.cand, by rw [um]; exact h.tab, by rw [urd]; exact h.tabR, by rw [um]; exact h.tape,
    usy.trans h.syms, usp.trans h.sp, urd.trans h.rd, uwr.trans h.wr⟩

/-- The body. -/
theorem body_ok (Ri : RoundImpl) {bits : Nat} {σ s : State} (h : BIn bits σ s) :
    WP isa (body Ri.name Ri.code) s (BOut bits σ s) := by
  obtain ⟨hbig, -, -, -⟩ := cand_facts h.hb h.cin
  unfold body
  refine WP.seq (WP.mono (trial_ok (c := cand bits σ) (T := σ.syms TrialTable32.symbol) h.env h.cand h.hdr.cnt
    (by rw [h.syms]) h.tab h.tabR) fun u ⟨⟨u22, um⟩, ug, urd, uwr, usp, usy⟩ => ?_)
  have hu : BIn bits σ u := bin_after_trial h um ug urd uwr usp usy
  rw [trial_spec h.hb hbig] at u22
  have fr : ∀ t, BOut bits σ u t → BOut bits σ s t := fun t o =>
    ⟨o.r31, o.stat, o.used, by rw [← um]; exact o.frame, o.sp, o.rd, o.wr⟩
  refine WP.ite _ (eval_zero_ofNat u .r22 (by split <;> decide) u22) (fun hz => ?_) (fun hz => ?_)
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (mr_ok Ri hu hc) fr
  · have hc : Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) = true := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite bits (cand bits σ) <;> simp
    exact WP.mono (comp_ok hu hc) fr

end VG.Proof.Dsa.PPC64LE.Prime

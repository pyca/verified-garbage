module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Trial
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Trial
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Loop
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
import VerifiedGarbage.Proof.Dsa.Generation.Primality
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `Dsa.PPC64LE.Prime.Correct`, which the modules that import this one used -/

section

/-! ### `Dsa.PPC64LE.Prime.Exit`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Prime.Body`, which only this module used -/

section

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
  omega_using [hx, hsz, this]

/-- The candidate's facts the tests need. -/
theorem cand_facts {bits : Nat} {σ : State} (hb : Bits bits) (h : CIn bits σ) :
    8161 < cand bits σ ∧ 3 ≤ cand bits σ ∧ cand bits σ % 2 = 1 ∧
      Spec.RsaKeyGen.bitLength (cand bits σ - 1) = bits := by
  have hbl := h.bl
  have hodd := h.odd
  have hs := shape_of hb
  have hbig := hs.big
  obtain ⟨hlo, -⟩ := (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [hbig])).mp hbl
  have : 2 ^ 13 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) hbig
  dsimp only [cand]
  refine ⟨by omega_using [hlo, this], by omega_using [hlo, this], hodd, VG.Proof.Dsa.Generation.predecessor_bits (by omega_using [hbig]) hodd hbl⟩

/-- A change of bytes `[d, d + n)` of a region of `Z ≥ d + n` bytes at `B`. -/
theorem frame_outside {B : Addr} {Z d n : Nat} {rs : List Region} {m m' : Mem}
    (ho : VG.Proof.Bignum.Outside B d n m m') (hd : d + n ≤ Z) : Frame (⟨B, Z⟩ :: rs) m m' := fun x hx => by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains] at this
  exact ho x (.inr (by simp only [ofs]; omega_using [hd, this]))

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
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega_using [hbig]) hodd, h.cin.bl, hc]; rfl
  generalize hB : wsB σ = B at e hs hnw
  refine WP.mono (WP.keep [.r3] (Q := fun x => x.mem = s.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 2))
    (by simp only [sth, hStat]; prun [e.h31, hs.st (d := 160) (n := 8) (by omega_using [hZ])]) (by decide)) fun x ⟨xm, kx⟩ => ?_
  subst hB
  have ho := VG.Proof.Bignum.writeW_outside s.mem (wsB σ) (d := 8 * hStat) (BitVec.ofNat 64 2)
    (by simp only [hStat]; omega_using [])
  refine ⟨(kx.gpr _ (by decide)).trans e.h31, by rw [xm, VG.Proof.Bignum.word_writeW_self, hres]; rfl,
    fun b rest hr => ?_, by rw [xm]; exact frame_outside ho (by simp only [hStat]; omega_using [hZ]), kx.sp.trans h.sp,
    kx.rd.trans h.rd, kx.wr.trans h.wr⟩
  rw [hres] at hr
  cases hr
  rw [xm, Frm.word_eq (rs := [(8 * hStat, 8)]) (fun y hy => ho y (hy _ List.mem_cons_self))
    (by simp only [hStat, hUsed, List.mem_singleton, forall_eq]; omega_using []) (by simp only [hUsed]; omega_using []), h.hdr.used]
  simp only [tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, Nat.sub_self]

/-- The header's words lie apart from what `montPrep` writes. -/
theorem hdr_apart (w : Nat) :
    ∀ d ∈ hdrWords, ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.Search.mpRanges w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rw [hdrWords_eq]
  intro d hd r hr
  simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr hd
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.PPC64LE.aE] <;> omega_using [hd]

/-- What `montPrep` writes lies within the working space. -/
theorem mp_within (w : Nat) :
    ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.Search.mpRanges w, r.1 + r.2 ≤ 256 + 28 * (8 * (w + 2)) := by
  intro r hr
  simp only [VG.Proof.MillerRabin.PPC64LE.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, VG.Impl.MillerRabin.PPC64LE.aE] <;> omega_using []

/-- A byte of the tape lies outside the working space. -/
theorem tape_out {bits : Nat} {σ : State} (h : CIn bits σ) {i : Nat} (hi : i < (σ.gpr .r6).toNat) :
    ¬ ofs (wsB σ) (σ.gpr .r5 + BitVec.ofNat 64 i) < 8 * keyWords bits := fun hx =>
  h.wR _ (inW h hx) (by
    simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := (σ.gpr .r6).isLt; omega_using [hi])]; omega_using [hi])

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
        rfl | rfl | rfl | rfl | rfl <;> omega_using [])
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
      rw [Nat.mod_eq_of_lt (by have := (σ.gpr .r6).isLt; omega_using [hi])]; omega_using [hi]
  have htape : Spec.Rsa.bytesAt v.mem (σ.gpr .r5) (σ.gpr .r6).toNat = tape σ := by
    rw [← h.tape]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    refine vO _ fun r hr => .inr ?_
    have h1 := tape_out cin hi
    have h2 := mp_within _ r hr
    change r.1 + r.2 ≤ ofs (wsB σ) _
    omega_using [hZ, h1, h2]
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
    rw [res, VG.Proof.Dsa.Generation.probablePrime_large (by omega_using [hbig]) hodd, cin.bl, hc, sh.hchecks]; rfl
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

end

end


/-!
# DSA's probable-prime test on PPC64LE: the exit

`exit_ok`: after the body (`BOut`), with the registers saved at the entry
still in `ws`: the status into `r3`, our caller's registers and return
address back (`Spill.restore_wp`), and the octets read into `used` unless
the tape ran out.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.Bignum (word off slot)

/-- What the exit leaves. -/
structure XOut (bits : Nat) (σ t f : State) : Prop where
  abi : abiPreserved σ f
  r3 : f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  frame : Frame [cU σ] t.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .r7) 1 = [BitVec.ofNat 64 ((σ.gpr .r6).toNat - rest.length)]

theorem status_le (x : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status x ≤ 2 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem status_eq_zero {x : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status x = 0) :
    x = none := by
  rcases x with _ | ⟨_ | _, _⟩ <;> first | rfl | cases h

/-- The restores' slots: `savedSlots` but the return address. -/
theorem restore_eq : restore = ([.load .d .r0 .r9 saveOff, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r9 savedSlots.tail := rfl

theorem tail_fits : ∀ p ∈ savedSlots.tail, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem tail_restorable : Spill.Restorable .r9 savedSlots.tail := by decide
theorem tail_in : ∀ p ∈ savedSlots.tail, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 168 := by decide
theorem tail_regs : savedSlots.tail.map Prod.fst =
    [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
      .r7, .r2] := by decide

/-- After the exit's first block: the calling convention's registers back,
the status in `r3`, `hUsed` in `r5` and `used` in `r7`. -/
def XMid (bits : Nat) (σ t f : State) : Prop :=
  abiPreserved σ f ∧ f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ)) ∧
    f.gpr .r5 = word t.mem (wsB σ) (8 * hUsed) ∧ f.gpr .r7 = σ.gpr .r7 ∧ f.mem = t.mem ∧ f.wr = t.wr

theorem exitA_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem) :
    WP isa (.block ([ldh .r3 hStat, ldh .r5 hUsed, .subi .r9 .r31 keyOff] ++ restore)) t (XMid bits σ t) := by
  have hsc : Scr t (wsB σ) (8 * keyWords bits) := scr_of h o.wr
  have hnw := hsc.nowrap
  have hsz := h.size
  have hfw := h.fw
  have hst := status_le (res bits σ)
  have hwsW : cW σ ∈ t.wr := by rw [o.wr, h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .r4).toNat * 8 → InRegions (t.rd ++ t.wr) (σ.gpr .r3 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega_using [hfw, hd])]; omega_using [hd]⟩
  have hkw : 32 ≤ keyWords bits := by unfold keyWords; omega_using []
  rw [restore_eq, WP.block_append_iff]
  have r31 := o.r31
  generalize hB : wsB σ = B at hsc hnw r31
  refine WP.mono (WP.keep [.r3, .r5, .r9] (Q := fun (u : State) =>
      u.gpr .r3 = word t.mem B (8 * hStat) ∧ u.gpr .r5 = word t.mem B (8 * hUsed) ∧
      u.gpr .r9 = B - BitVec.ofNat 64 552 ∧ u.mem = t.mem) ?_ (by decide))
    fun u ⟨⟨u3, u5, u9, um⟩, ku⟩ => ?_
  · simp only [ldh, hStat, hUsed, keyOff]
    prun [r31, hsc.ld (d := 160) (n := 8) (by omega_using [hkw]), hsc.ld (d := 152) (n := 8) (by omega_using [hkw])]
    done
  have u9' : u.gpr .r9 = σ.gpr .r3 := by
    rw [u9, ← hB]; simp only [wsB]; exact BitVec.add_sub_cancel _ _
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (v : State) => v.lr = σ.lr ∧ (∀ r, r ≠ .r0 → v.gpr r = u.gpr r) ∧ v.mem = u.mem ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp) ?_ fun v ⟨vlr, vg, vm, vrd, vwr, vsp⟩ => ?_
  · have hin := inWs saveOff (by simp only [saveOff, keyOff] at hsz ⊢; omega_using [hsz])
    simp only [saveOff] at hin ⊢
    refine WP.cons (exec_load_d (by decide) (by decide) (by rw [u9', ku.rd, ku.wr]; exact hin)) ?_
    refine WP.cons exec_mtlr (WP.block_nil ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩)
    · have := svd (.r0, saveOff) (by decide)
      simp only [State.write, ↓reduceIte, saveOff] at this ⊢
      rw [um, u9']; exact this
    · simp only [State.write, hr, ↓reduceIte]
  · have hpres : ∀ r ∈ preserved, r ∈ savedSlots.tail.map Prod.fst := by rw [tail_regs]; decide
    have gsv : ∀ r, r ≠ .r0 → (σ.write .r0 σ.lr).gpr r = σ.gpr r := fun r hr => by
      simp only [State.write, hr, ↓reduceIte]
    refine WP.mono (Spill.restore_wp (b := .r9) (B := σ.gpr .r3) (by decide) (by rw [vg _ (by decide)]; exact u9')
      tail_fits tail_restorable (fun p hp => by
        rw [vrd, vwr, ku.rd, ku.wr]
        exact inWs _ (by have := tail_in p hp; simp only [saveOff, keyOff] at *; omega_using [hsz, this]))
      (by rw [vm, um]; exact svd.sub fun p hp => List.mem_of_mem_tail hp)) fun f hf => ?_
    have o3 : f.gpr .r3 = u.gpr .r3 := (hf.other _ (by rw [tail_regs]; decide)).trans (vg _ (by decide))
    have o5 : f.gpr .r5 = u.gpr .r5 := (hf.other _ (by rw [tail_regs]; decide)).trans (vg _ (by decide))
    refine ⟨⟨fun r hr => (hf.gpr_of (.inl (hpres r hr))).trans (gsv r (by revert hr; decide +revert)),
        hf.sp.trans (vsp.trans (ku.sp.trans o.sp)), hf.lr.trans vlr⟩, ?_, ?_,
      (hf.gpr (.r7, saveOff + 152) (by decide)).trans (gsv _ (by decide)),
      hf.mem.trans (vm.trans um), hf.wr.trans (vwr.trans ku.wr)⟩
    · rw [o3, u3, ← hB]; exact o.stat
    · rw [o5, u5, ← hB]

theorem exit_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem) :
    WP isa exit t (XOut bits σ t) := by
  have hst := status_le (res bits σ)
  unfold exit
  refine WP.seq (WP.mono (exitA_ok h o svd) fun f ⟨fa, f3, f5, f7, fm, fwr⟩ => ?_)
  refine WP.ite _ (eval_zero_ofNat f .r3 (by omega_using [hst]) f3) (fun hz => ?_) (fun hz => ?_)
  · have h0 : Proof.Dsa.ProbablePrime.status (res bits σ) = 0 := by simpa using hz
    exact WP.block_nil ⟨fa, f3, by rw [fm]; exact Frame.refl _ _, fun b rest hr => by
      rw [status_eq_zero h0] at hr; cases hr⟩
  · have hU : InRegions f.wr (f.gpr .r7 + BitVec.ofNat 64 0) 8 := ⟨cU σ, by rw [fwr, o.wr, h.wr]; simp, by
      rw [f7]; simp only [Region.Contains, BitVec.add_zero, BitVec.sub_self, BitVec.toNat_zero]; omega_using []⟩
    refine WP.cons (exec_store_d (by decide) (by decide) hU) (WP.block_nil ⟨?_, f3, ?_, fun b rest hr => ?_⟩)
    · exact fa
    · rw [f7, fm, BitVec.add_zero]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [f7, Mem.readW_writeW_self64, f5, o.used b rest hr]

end VG.Proof.Dsa.PPC64LE.Prime

end

end


/-!
# DSA's probable-prime test on PPC64LE: correctness

`code_ok`: from the precondition (`CIn`, and the table's words and region,
`ConstsOk`), the entry (`entry_ok`), the candidate's load (`loadC_ok`), the
body (`body_ok`) and the exit (`exit_ok`) return the test's status, write
the octets read to `used`, keep every byte of `ws` but the saved registers
and the working space, and preserve what the calling convention asks.
`correct`: the contract's postcondition, under `abi.withConsts`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.Bignum (word off slot Frm Outside)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)

/-- The trial table. -/
abbrev K : List (String × List (BitVec 64)) := TrialTable32.consts

/-- `CIn` of the state without the table's region gives it of the state. -/
theorem CIn.ofStrip {bits : Nat} {σ : State} (h : CIn bits (stripConsts K σ)) : CIn bits σ :=
  ⟨h.spLo, List.mem_of_mem_take h.rd, h.wr, h.wR, h.wU, h.rU, h.sW, h.sR, h.sU, h.fw, h.fr, h.fu, h.size, h.odd,
    h.bl⟩

/-- A byte at offset `i` of `p` lies outside a region at offset `e`. -/
theorem not_in (p : Addr) {i e k : Nat} (h : i + 1 ≤ e ∨ e + k ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + k ≤ 2 ^ 64) :
    ¬ (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint p h hi he _ (Region.contains_self _ _) hc

/-- A region at offset `d` of `ws` lies in `ws`. -/
theorem sub_ws {σ : State} {d n : Nat} (h : d + n ≤ (σ.gpr .r4).toNat * 8) :
    Region.Sub ⟨σ.gpr .r3 + BitVec.ofNat 64 d, n⟩ (cW σ) :=
  Offset.sub_base _ h

theorem table_held {σ : State} (hk : ConstsOk K 176 σ) {i : Nat} (hi : i < 1024) :
    σ.mem.readW (σ.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
  have := hk.2.1 _ List.mem_cons_self i (by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; exact hi)
  have hl : i < TrialTable32.packed.length := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; exact hi
  rw [this]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact VG.Proof.RsaKeyGen.TrialTable32.packed_entry hi

theorem table_rd {σ : State} (hk : ConstsOk K 176 σ) : (⟨σ.syms TrialTable32.symbol, 8192⟩ : Region) ∈ σ.rd := by
  have := hk.mem_rd (name := TrialTable32.symbol) (ws := TrialTable32.packed) List.mem_cons_self
  rwa [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at this

theorem consts_wr1 {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State} (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

theorem table_wr {σ : State} (hk : ConstsOk K 176 σ) :
    ∀ r ∈ σ.wr, Region.Disjoint ⟨σ.syms TrialTable32.symbol, 8192⟩ r := by
  have := consts_wr1 (name := TrialTable32.symbol) (ws := TrialTable32.packed) hk
  rwa [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at this

/-- What the function leaves. -/
structure COut (bits : Nat) (σ f : State) : Prop where
  abi : abiPreserved σ f
  r3 : f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  keeps : Proof.Dsa.ModPow.Keeps (σ.gpr .r3) (σ.gpr .r4).toNat (layout bits).scratch σ.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .r7) 1 = [BitVec.ofNat 64 ((σ.gpr .r6).toNat - rest.length)]

/-- The bytes of `ws` the test keeps. -/
def Kept (bits : Nat) (σ : State) (m : Mem) : Prop :=
  ∀ i, i < 8 * (σ.gpr .r4).toNat → i < 384 ∨ 384 + (552 - 384 + 8 * keyWords bits) ≤ i →
    m (σ.gpr .r3 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .r3 + BitVec.ofNat 64 i)

/-- After the entry and the candidate's load: the body's context, the saved
registers, and the bytes of `ws` kept. -/
theorem after_loadC {bits : Nat} (hb : Bits bits) {σ s₁ s₂ : State} (h : CIn bits σ) (hk : ConstsOk K 176 σ)
    (ep : EntryPost bits σ s₁) (sy₁ : s₁.syms = σ.syms)
    (hl : (arr s₂.mem (wsB σ) (words bits) 0 = Proof.Dsa.ProbablePrime.candidateAt (layout bits) σ.mem (σ.gpr .r3) ∧
        Outside (wsB σ) (slot (words bits) 0) (8 * words bits) s₁.mem s₂.mem) ∧
      Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17] s₁ s₂) (sy₂ : s₂.syms = s₁.syms) :
    BIn bits σ s₂ ∧ Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s₂.mem ∧ Kept bits σ s₂.mem := by
  obtain ⟨⟨c₂, o₂⟩, k₂⟩ := hl
  have hs := shape_of hb
  have hsz := h.size
  have hfw := h.fw
  have hkey := hs.key
  have hw48 := hs.w48
  have hW : cW σ ∈ σ.wr := by rw [h.wr]; exact List.mem_cons_self
  have hslot : slot (words bits) 0 + 8 * words bits ≤ 8 * keyWords bits := by
    simp only [slot, VG.Impl.Bignum.hdrBytes]; omega_using [hkey]
  have f₁ : Frame [cW σ] σ.mem s₁.mem := ep.frame.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_ws (by simp only [saveOff, keyOff] at *; omega_arith)⟩
  have f₂ : Frame [⟨wsB σ, 8 * keyWords bits⟩] s₁.mem s₂.mem := frame_outside o₂ hslot
  have f₂' : Frame [cW σ] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨cW σ, List.mem_cons_self, by
    rw [List.mem_singleton] at hr; subst hr; exact sub_ws (by simp only [keyOff] at *; omega_using [hsz])⟩
  have fW := f₁.trans f₂'
  have bin : BIn bits σ s₂ := by
    refine ⟨hb, h, (env_of hs h ep).keep k₂ (by decide), (hdr_of ep).keep fun d hd => ?_, c₂, fun i hi => ?_,
      by rw [k₂.rd, ep.rd]; exact table_rd hk, ?_, sy₂.trans sy₁, k₂.sp.trans ep.sp, k₂.rd.trans ep.rd,
      k₂.wr.trans ep.wr⟩
    · rw [hdrWords_eq] at hd
      refine Frm.word_eq (Frm.of_outside o₂ (List.mem_singleton_self _)) (fun r hr => ?_) ?_
      · rw [List.mem_singleton] at hr; subst hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        left; simp only [slot, VG.Impl.Bignum.hdrBytes]
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> omega_using []
      · have := (env_of hs h ep).hs.nowrap
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl <;> omega_using []
    · rw [fW.readW (r := ⟨σ.syms TrialTable32.symbol, 8192⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact table_wr hk _ hW) (by decide)]
      exact table_held hk hi
    · simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      exact fW.bytes (R := cR σ) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact h.wR.symm)
        (by have := (σ.gpr .r6).isLt; exact Nat.le_of_lt this) hi
  refine ⟨bin, ep.svd.frame_in (lo := saveOff) (n := 168) savedSlots_in f₂ fun r hr => ?_, fun i hi hout => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (show saveOff + 168 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega_using [])
      (by simp only [keyOff] at *; omega_using [hsz, hfw])
  simp only [keyOff] at hsz
  have e₁ : s₂.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = s₁.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    f₂ _ fun r hr hc => by
      rw [List.mem_singleton] at hr; subst hr
      exact not_in _ (e := keyOff) (by simp only [keyOff]; omega_using [hout]) (by omega_using [hfw, hi]) (by simp only [keyOff]; omega_using [hsz, hfw]) hc
  have e₀ : s₁.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = σ.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    ep.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := saveOff) (by simp only [saveOff]; omega_using [hout]) (by omega_using [hfw, hi]) (by simp only [saveOff]; omega_using []) hc
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega_using [hkey, hout]) (by omega_using [hfw, hi]) (by simp only [keyOff]; omega_using []) hc
  rw [e₁, e₀]

/-- The saved registers survive the body. -/
theorem saved_body {bits : Nat} {σ s t : State} (h : CIn bits σ) (bo : BOut bits σ s t)
    (sv : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s.mem) :
    Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem := by
  have hsz := h.size
  have hfw := h.fw
  refine sv.frame_in (lo := saveOff) (n := 168) savedSlots_in bo.frame fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (show saveOff + 168 ≤ keyOff by decide)) (by simp only [saveOff] at *; omega_using [])
      (by simp only [keyOff] at *; omega_using [hsz, hfw])
  · exact (h.sW.symm.sub_left (sub_ws (by simp only [saveOff, keyOff] at *; omega_using [hsz])))

/-- The body and the exit, from the body's context. -/
theorem tail_ok (Ri : RoundImpl) {bits : Nat} {σ s₂ : State} (h : CIn bits σ) (bin : BIn bits σ s₂)
    (sv₂ : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots s₂.mem) (kept : Kept bits σ s₂.mem) :
    WP isa (.seq (body Ri.name Ri.code) exit) s₂ (COut bits σ) := by
  have hsz := h.size
  have hfw := h.fw
  refine WP.seq (WP.mono (body_ok Ri bin) fun t bo => ?_)
  refine WP.mono (exit_ok h bo (saved_body h bo sv₂)) fun f xo => ⟨xo.abi, xo.r3, fun i hi hout => ?_, xo.used⟩
  -- A byte of `ws` outside the scratch range.
  simp only [layout, List.mem_singleton, forall_eq, saveOff, keyOff] at hout hsz
  have inW : (cW σ).Contains (σ.gpr .r3 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hfw, hi])
  have e₃ : f.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = t.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    xo.frame _ fun r hr hc => by rw [List.mem_singleton] at hr; subst hr; exact h.wU _ inW hc
  have e₂ : t.mem (σ.gpr .r3 + BitVec.ofNat 64 i) = s₂.mem (σ.gpr .r3 + BitVec.ofNat 64 i) :=
    bo.frame _ fun r hr hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact not_in _ (e := keyOff) (by simp only [keyOff]; omega_using [hout]) (by omega_using [hfw, hi]) (by simp only [keyOff]; omega_using [hsz, hfw]) hc
      · exact h.sW _ hc inW
  rw [e₃, e₂, kept i hi hout]

theorem code_ok (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) {σ : State} (h : CIn bits σ)
    (hk : ConstsOk K 176 σ) : WP isa (code bits Ri.name Ri.code) σ (COut bits σ) := by
  have hs := shape_of hb
  unfold code
  refine WP.seq (WP.mono_syms (entry_ok hs h) fun s₁ ep sy₁ => ?_)
  refine WP.seq (WP.mono_syms (loadC_ok hs h ep) fun s₂ hl sy₂ => ?_)
  obtain ⟨bin, sv₂, kept⟩ := after_loadC hb h hk ep sy₁ hl sy₂
  exact tail_ok Ri h bin sv₂ kept

end VG.Proof.Dsa.PPC64LE.Prime

end

end

/-!
# DSA's probable-prime test on PPC64LE: constant time of trial division

`trial_ct`: two runs of trial division of the same candidate (public, as
DSA's primes are) by the same table leak the same trace. The table's address
is public (`taintSym`, as the contract with the table says); each entry
(`entry`) passes the taint analysis from the table's address, which the loop's
state `TInv` fixes, and whether the loop goes on (`step_ok`) is a function of
the candidate and of the entries tested.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.RsaKeyGen
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)
open VG.Proof.Bignum (word off slot)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)
open VG.Proof.RsaKeyGen.PPC64LE.Trial (TInv step_ok entryRegs)

/-- Code the taint analysis with the table's address public proves constant
time, from states a predicate relates. -/
theorem two_taint_sym {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    (hsym : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.syms TrialTable32.symbol = s₂.syms TrialTable32.symbol)
    {hc : VG.Taint.Hint VG.PPC64LE.Taint.T}
    (h : (VG.Taint.check (taintSym [TrialTable32.symbol]) (VG.PPC64LE.Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [TrialTable32.symbol]) (VG.PPC64LE.Taint.ofRegs rs) (fun _ _ ⟨a, h₁, h₂⟩ => by
    obtain ⟨hsp, hr⟩ := hpin a _ _ h₁ h₂
    refine ⟨⟨hsp, fun r hr' => hr r (VG.PPC64LE.Taint.mem_ofRegs.mp hr')⟩, fun n hn => ?_⟩
    simp only [List.mem_singleton] at hn; subst hn; exact hsym a _ _ h₁ h₂) h

/-- The public data of trial division. -/
structure TD where
  B : Addr
  T : Addr
  L : Nat
  w : Nat
  c : Nat
  n : Nat
  sp : Addr

/-- Trial division's start. -/
def TS (d : TD) (s : State) : Prop :=
  Env s d.B (8 * d.L) d.w ∧ arr s.mem d.B d.w 0 = d.c ∧ word s.mem d.B (8 * hCnt) = BitVec.ofNat 64 d.n ∧
    s.syms TrialTable32.symbol = d.T ∧ Tab d.T s.mem ∧ (⟨d.T, 8192⟩ : Region) ∈ s.rd ∧ s.sp = d.sp ∧
    1 ≤ d.n ∧ d.n ≤ 1024

/-- The first block: the table's address and the entries. -/
abbrev trialA : List Instr := [.adrSym .r23 TrialTable32.symbol, ldh .r24 hCnt]

/-- After it. -/
def TA (d : TD) (u : State) : Prop :=
  ∃ s, TS d s ∧ (u.gpr .r23 = d.T ∧ u.gpr .r24 = BitVec.ofNat 64 d.n ∧ u.mem = s.mem ∧ u.syms = s.syms) ∧
    (∀ r, r ∉ trialRegs → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp

theorem trialA_ok {d : TD} {s : State} (h : TS d s) : WP isa (.block trialA) s (TA d) := by
  obtain ⟨e, -, hcnt, hT, -, -, -, -, -⟩ := id h
  have hZ : 256 + 28 * (8 * (d.w + 2)) ≤ 8 * d.L := e.hZ
  refine WP.cons (exec_adrSym (by decide)) ?_
  simp only [ldh, hCnt]
  prun [e.h31, e.hs.ld (d := 40) (n := 8) (by omega_using [hZ])]
  refine ⟨s, h, ⟨hT, hcnt, rfl, rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  have h1 : r ≠ .r23 := fun h => hr (by subst h; decide)
  have h2 : r ≠ .r24 := fun h => hr (by subst h; decide)
  simp only [State.write, h1, h2, ↓reduceIte]

/-- The loop's state, with `m` entries left. -/
def TL (m : Nat) (d : TD) (v : State) : Prop := ∃ u, TA d u ∧ TInv u d.T d.c d.n m v

/-- What the loop's start gives each iteration. -/
theorem TA.facts {d : TD} {u : State} (h : TA d u) :
    Scr u d.B (8 * d.L) ∧ u.gpr .r10 = off d.B (slot d.w 0) ∧ u.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
      VG.Proof.Mont.val32 u.mem d.B (slot d.w 0) (2 * d.w) = d.c ∧ 4 ≤ d.w ∧ d.w ≤ 128 ∧
      slot d.w 0 + 8 * d.w ≤ 8 * d.L ∧ d.n ≤ 1024 ∧ u.sp = d.sp ∧
      (∀ i < d.n, u.mem.readW (d.T + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (TrialTable32.entry i) ∧
        InRegions (u.rd ++ u.wr) (d.T + BitVec.ofNat 64 (8 * i)) 8) := by
  obtain ⟨s, ⟨e, hc, -, -, htab, hTr, sp, -, hn⟩, ⟨-, -, um, -⟩, ug, urd, uwr, usp⟩ := h
  have hZ : 256 + 28 * (8 * (d.w + 2)) ≤ 8 * d.L := e.hZ
  refine ⟨e.hs.congr uwr, (ug _ (by decide)).trans e.h10, (ug _ (by decide)).trans e.h11, by rw [um]; exact hc,
    e.hw, e.hw', by simp only [slot, hdrBytes]; omega_using [hZ], hn, usp.trans sp, fun i hi => ⟨by rw [um]; exact htab i (by omega_using [hn, hi]),
      ⟨_, by rw [urd]; exact List.mem_append_left _ hTr, ?_⟩⟩⟩
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_using [hn, hi])]; omega_using [hn, hi]

theorem TA.init {d : TD} {u : State} (h : TA d u) : TInv u d.T d.c d.n d.n u := by
  obtain ⟨s, ⟨-, -, -, -, -, -, -, h1, -⟩, ⟨u23, u24, -, -⟩, -⟩ := h
  exact ⟨0, by omega_using [], by omega_using [h1], ⟨by rw [u23, Nat.mul_zero, BitVec.add_zero], by rw [u24, Nat.sub_zero], rfl, rfl⟩,
    Keep.refl _ _⟩

theorem TL.regs {m : Nat} {d : TD} {v : State} (h : TL m d v) :
    v.gpr .r10 = off d.B (slot d.w 0) ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
      v.gpr .r23 = d.T + BitVec.ofNat 64 (8 * (d.n - m)) ∧ v.sp = d.sp := by
  obtain ⟨u, hu, k, hm, hk, ⟨v23, -, -, -⟩, kv⟩ := h
  obtain ⟨-, h10, h11, -, -, -, -, -, sp, -⟩ := hu.facts
  refine ⟨(kv.gpr _ (by decide)).trans h10, (kv.gpr _ (by decide)).trans h11, by rw [v23]; congr 3; omega_using [hm, hk],
    kv.sp.trans sp⟩

theorem trial_ct : RelCT isa (Two TS) (VG.Impl.RsaKeyGen.PPC64LE.Trial.trial hCnt) fun _ _ => True := by
  have pS : Pins TS [.r31] := by
    rintro d s₁ s₂ ⟨e₁, -, -, -, -, -, sp₁, -⟩ ⟨e₂, -, -, -, -, -, sp₂, -⟩
    refine ⟨sp₁.trans sp₂.symm, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁.h31, e₂.h31]
  have pL : ∀ m, Pins (TL m) [.r10, .r11, .r23] := fun m d s₁ s₂ h₁ h₂ => by
    obtain ⟨a10, a11, a23, asp⟩ := h₁.regs
    obtain ⟨b10, b11, b23, bsp⟩ := h₂.regs
    refine ⟨asp.trans bsp.symm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a23, b23]
  unfold VG.Impl.RsaKeyGen.PPC64LE.Trial.trial
  refine RelCT.seq (two_post (Ψ := TA) (two_taint_sym _ pS (fun d s₁ s₂ h₁ h₂ => h₁.2.2.2.1.trans h₂.2.2.2.1.symm)
    (by taint_decide)) fun d s h => trialA_ok h) ?_
  refine (RelCT.exists_ fun m => RelCT.loop (M := isa) (fun m => Two (TL m)) (fun m => ?_) m).mono
    (fun s₁ s₂ ⟨d, h₁, h₂⟩ => ⟨d.n, d, ⟨s₁, h₁, h₁.init⟩, ⟨s₂, h₂, h₂.init⟩⟩) fun _ _ h => h
  refine (two_post (Ψ := fun d t => ∃ u, TA d u ∧
      isa.eval (.nonzero .d .r24) t = some (decide (d.c % tabEntry (d.n - m) ≠ 0 ∧ d.n - m + 1 ≠ d.n)) ∧
      (isa.eval (.nonzero .d .r24) t = some true → 0 < m ∧ TInv u d.T d.c d.n (m - 1) t))
    (two_taint _ (pL m) (by taint_decide)) fun d v ⟨u, hu, hI⟩ => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨hs, h10, h11, hc, hw4, hw128, hZ, hn, -, htab⟩ := hu.facts
    exact WP.mono (step_ok hs h10 h11 hc (by omega_using [hw4]) (by omega_using [hw128]) hZ hn htab hI) fun t ⟨e, _, g⟩ => ⟨u, hu, e, g⟩
  · rintro s₁ s₂ ⟨d, ⟨u₁, hu₁, e₁, g₁⟩, ⟨u₂, hu₂, e₂, g₂⟩⟩
    refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun he => ?_⟩
    obtain ⟨hm, i₁⟩ := g₁ he
    obtain ⟨-, i₂⟩ := g₂ (e₂.trans (e₁.symm.trans he))
    exact ⟨m - 1, by omega_using [hm], d, ⟨u₁, hu₁, i₁⟩, ⟨u₂, hu₂, i₂⟩⟩

end VG.Proof.Dsa.PPC64LE.Prime

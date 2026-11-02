module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.WLoop
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Gcd
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Args
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.MontP
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Hyp
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the constant-time proof (`CT.lean`) and the contract's proof (`Verified.lean`) build next to
-- it, and only the latter imports it

/-!
# A candidate on RISC-V: the body

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{Main,Tail,Body}.lean`), what the
body between the entry and the restore leaves (`mid_ok`), and so the whole
function (`code_correct`): the contract's results (`CQ`).

* `out` zeroed (`zeroOut_ok`), then 0 if `rand` is shorter than `out_len`;
* otherwise (`main_ok`) the working space set up (`setup_ok`) and the
  candidate drawn (`loadC_ok`); 2 if it is too close to `p`
  (`closeCheck_ok`); 3 unless `gcd(c − 1, e) = 1` (`gcdCheck_ok`);
* then (`test_ok`) the test's arguments in the header (`testArgs_ok`), trial
  division (`DivOk`), 3 if it finds a divisor, and otherwise the working
  space prepared (`prep_ok`), the witnesses (`millerRabin_ok`) and the result
  (`res_ok`).

The octets read are in the frame (`oRead`), not a register: each stage
carries them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Mont (off ofs word Outside Outs)
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (main setup loadC closeCheck gcdCheck test testArgs testResult finish
  finNone nArr aP aBnd aCm1 hTrial oRead oRandLen oOutLen ldf)
open VG.Impl.MillerRabin.RISCV64.Search (hUsed hStat hRand hRandLen hK hChecks)
open VG.Impl.RsaKeyGen (TrialTable32.symbol TrialTable32.packed)

/-! ## Helpers -/

theorem wp_seqs {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs (c :: l)) s Q ↔
      WP isa c s (fun t => WP isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem slot_lin (w j : Nat) : slot w j = 256 + j * (8 * w) + j * 16 := by
  show VG.Impl.Bignum.hdrBytes + j * (8 * (w + 2)) = _
  rw [Nat.mul_add 8 w 2, Nat.mul_add, ← Nat.add_assoc]; rfl

theorem bytesAt_len (m : Mem) (a : Addr) (n : Nat) : (Spec.Rsa.bytesAt m a n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem take_bytesAt (m : Mem) (a : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Rsa.bytesAt m a n).take k = Spec.Rsa.bytesAt m a k := by
  unfold Spec.Rsa.bytesAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

section
variable {s0 : State}

/-- The candidate's words. -/
abbrev cw (s0 : State) : Nat := oL s0 / 8

/-- The candidate. -/
abbrev candOf (s0 : State) : Nat :=
  Spec.RsaKeyGen.candidate (64 * cw s0) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (8 * cw s0)))

/-- `p`'s octets. -/
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a5) (s0.gpr .a6).toNat

/-- `rand`'s octets. -/
abbrev rB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0)

theorem cw_facts (hp : CIn s0) : oL s0 = 8 * cw s0 ∧ 4 ≤ cw s0 ∧ cw s0 ≤ 64 := by
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  simp only [cw, oL]
  omega

/-- What the contract asks, from the candidate in the first `8 w` octets. -/
theorem cOp_cand (hp : CIn s0) (hav : oL s0 ≤ rL s0) :
    cOp s0 = VG.Proof.RsaKeyGen.afterDraw (64 * cw s0) (eV s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0)
      ((rB s0).drop (8 * cw s0)) := by
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega), show 8 * (8 * cw s0) = 64 * cw s0 by omega,
    VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_len]; omega)]
  unfold VG.Proof.RsaKeyGen.seg
  rw [List.drop_zero, take_bytesAt _ _ (by omega)]

/-- Too few octets for a candidate. -/
theorem cOp_none (hp : CIn s0) (h : ¬ oL s0 ≤ rL s0) : cOp s0 = none := by
  obtain ⟨hw, hw4, _⟩ := cw_facts hp
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega),
    VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_len]; omega)]

theorem hlen_drop (w : Nat) : ((rB s0).drop (8 * w)).length = rL s0 - 8 * w := by
  rw [List.length_drop, bytesAt_len]

/-! ## The table of trial division -/

/-- The table of trial division, from the call's start. -/
structure TabOk (s0 : State) : Prop where
  fit : (s0.syms TrialTable32.symbol).toNat + 8 * 1024 ≤ 2 ^ 64
  al : (s0.syms TrialTable32.symbol).toNat % 8 = 0
  rd : (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region) ∈ s0.rd
  held : ∀ i < 1024, s0.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 =
    TrialTable32.packed.getD i 0
  dj : ∀ ρ ∈ [cO s0, cU s0, cS s0, cF s0], (⟨s0.syms TrialTable32.symbol, 8 * 1024⟩ : Region).Disjoint ρ

/-- The table's words through the body. -/
theorem TabOk.held_at (h : TabOk s0) {s : State} (hf : Fr s0 s) {i : Nat} (hi : i < 1024) :
    s.mem.readW (s0.syms TrialTable32.symbol + BitVec.ofNat 64 (8 * i)) 64 = TrialTable32.packed.getD i 0 := by
  rw [hf.out.readW (r := ⟨s0.syms TrialTable32.symbol, 8 * 1024⟩)
    (Offset.contains_base _ (by omega) (by have := h.fit; omega)) h.dj (by decide)]
  exact h.held i hi

/-! ## Keeping the body's state -/

/-- `Ctx` through code that keeps memory, the regions, the stack pointer and
`s11`. -/
theorem Ctx.keep {s t : State} {rs : List Reg} (h : Ctx s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (sp : t.sp = s.sp) (h11 : .s11 ∉ rs := by decide) : Ctx s0 t :=
  h.step sp k.2.1 k.2.2 (k.gpr h11) (by rw [hm]; exact Frame.refl _ _)

/-- What changes only within `scratch` keeps the body's state. -/
theorem frame4 {m m' : Mem} (f : Frame [cS s0] m m') : Frame [cU s0, cS s0, rF s0, rdW s0] m m' :=
  f.mono (by simp)

/-- The octets read survive what changes only `scratch`. -/
theorem rd_keep (hp : CIn s0) {m m' : Mem} (f : Frame [cS s0] m m') :
    m'.readW (fw s0 oRead) 64 = m.readW (fw s0 oRead) 64 :=
  f.readW (r := ⟨fw s0 oRead, 8⟩) (Region.contains_self _ _) (fun ρ hρ => by
    simp only [List.mem_singleton] at hρ; subst hρ
    exact hp.FS.sub_left (fw_sub s0 (by decide))) (by decide)

/-- A word of the header within `scratch`, through what changes only its
arrays from `slot w 0` on. -/
theorem outside_scr {B : Addr} {d n : Nat} {m m' : Mem} (o : Outside B d n m m') {e : Nat} (he : e + 8 ≤ d)
    (hB : B.toNat + e + 8 ≤ 2 ^ 64) : word m' B e = word m B e :=
  o.word (.inl he) (by omega)

end

/-! ## Once `rand` has the candidate's octets -/

section
variable {s0 : State}

/-- The body's state once `rand` has the candidate's octets. -/
structure MIn (s0 s : State) : Prop where
  ctx : Ctx s0 s
  s6 : s.gpr .s6 = stackArg s0 1
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

/-- After `setup`. -/
structure M1 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  zs : ∀ i < nArr * (cw s0 + 2), word s.mem (stackArg s0 1) (256 + 8 * i) = 0
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem setupS {s : State} (h : MIn s0 s) : WP isa setup s (M1 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, _, _⟩ := cw_facts hp
  refine WP.mono_syms (setup_ok h.ctx h.s6 hw) fun t ⟨⟨c₁, e₁, l₁, z₁, _⟩, _⟩ sy => ?_
  exact ⟨c₁, e₁, l₁, z₁, h.hav, sy.trans h.syms, h.tab⟩

/-- After `loadC`. -/
structure M2 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  zs : ∀ i, cw s0 ≤ i → i < nArr * (cw s0 + 2) → word s.mem (stackArg s0 1) (256 + 8 * i) = 0
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem loadCS {s : State} (h : M1 s0 s) : WP isa loadC s (M2 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (loadC_ok h.ctx h.env hw h.hav) fun t ⟨⟨c₂, e₂, v₂, r₂, ow⟩, _⟩ sy => ?_
  have ow' : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    ow d (by omega) (.inl (by rw [slot_lin]; omega))
  refine ⟨c₂, e₂, ⟨(ow' 0 (by omega)).trans h.lay.len, (ow' 48 (by omega)).trans h.lay.wW,
      (ow' 224 (by omega)).trans h.lay.strideW, fun j hj => (ow' _ (by omega)).trans (h.lay.arrW j hj)⟩,
    fun i h1 h2 => ?_, v₂, r₂, h.hav, sy.trans h.syms, h.tab⟩
  have h2' := h2
  simp only [nArr] at h2'
  rw [ow _ (by omega) (.inr (by rw [slot_lin]; omega)), h.zs i h2]

/-- After `closeCheck`. -/
structure M3 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  f : s.gpr .s9 = BitVec.ofNat 64
    (if Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) then 1 else 0)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem closeS {s : State} (h : M2 s0 s) : WP isa closeCheck s (M3 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (WP.rdwr (closeCheck_ok h.ctx h.env hw h.v
    (by rw [show slot (cw s0) 0 + 8 * cw s0 = 256 + 8 * cw s0 by rw [slot_lin]; omega]
        exact h.zs (cw s0) (by omega) (by simp only [nArr]; omega))
    (by rw [show slot (cw s0) aP + 8 * cw s0 = 256 + 8 * (28 * (cw s0 + 2) + cw s0) by
          simp only [aP, slot_lin]; omega]
        exact h.zs _ (by omega) (by simp only [nArr]; omega))
    (fun i hi => by
      rw [show slot (cw s0) aBnd + 8 * i = 256 + 8 * (32 * (cw s0 + 2) + i) by simp only [aBnd, slot_lin]; omega]
      exact h.zs _ (by omega) (by simp only [nArr]; omega))))
    fun t ⟨⟨⟨c₃, e₃, f₃, o₃⟩, _⟩, _, _, _⟩ sy => ?_
  have fS := out_frame (by simp only [aP, slot_lin]; omega) o₃
  have ow : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    o₃.word (.inl (by simp only [aP, slot_lin]; omega)) (by omega)
  refine ⟨c₃, e₃, ⟨(ow 0 (by omega)).trans h.lay.len, (ow 48 (by omega)).trans h.lay.wW,
      (ow 224 (by omega)).trans h.lay.strideW, fun j hj => (ow _ (by omega)).trans (h.lay.arrW j hj)⟩,
    ?_, f₃, (rd_keep hp fS).trans h.rd8, h.hav, sy.trans h.syms, h.tab⟩
  rw [← h.v]
  exact o₃.wordsVal (.inl (by simp only [aP, slot_lin]; omega)) (by rw [slot_lin]; omega)

/-- An end with the octets of the candidate read. -/
theorem drawnFin (k : Nat) (hk : k < 2048) {s : State} (hc : Ctx s0 s)
    (r8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)) (hav : oL s0 ≤ rL s0)
    {x : Spec.RsaKeyGen.Candidate} (hop : cOp s0 = some (x, (rB s0).drop (8 * cw s0)))
    (hout : outOf s0 = List.replicate (oL s0) 0) (hst : Spec.RsaKeyGen.candidateStatus (cOp s0) = k) :
    WP isa (finish k) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  obtain ⟨hw, _, _⟩ := cw_facts hc.fr.pre
  refine fin_ok k hk hc hst hout ?_
  rw [r8, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega

/-- Too close to `p`. -/
theorem closeFin {s : State} (h : M3 s0 s)
    (hcl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = true) :
    WP isa (finish 2) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := cOp_cand h.ctx.fr.pre h.hav
  rw [VG.Proof.RsaKeyGen.afterDraw, hcl] at hop
  simp only [↓reduceIte] at hop
  exact drawnFin 2 (by decide) h.ctx h.rd8 h.hav hop (by rw [outOf, hop]) (by rw [hop]; rfl)

/-- After `gcdCheck`. -/
structure M4 (s0 s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) (cw s0)
  lay : Lay s.mem (stackArg s0 1) (sL s0) (cw s0)
  v : A s.mem (stackArg s0 1) (cw s0) 0 = candOf s0
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  g : s.gpr .s9 = 0 ↔ Nat.gcd (candOf s0 - 1) (eV s0) = 1
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * cw s0)
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem gcdS {s : State} (h : M3 s0 s)
    (hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false) :
    WP isa gcdCheck s (M4 s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hZ := h35_of hp hw
  have hZ' := hZ
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ'
  have hshape : VG.Proof.RsaKeyGen.PrimeShape (64 * cw s0) (candOf s0) :=
    VG.Proof.RsaKeyGen.candidate_shape (by omega) _
  refine WP.mono_syms (WP.rdwr (gcdCheck_ok h.ctx.fr h.env hZ h.v hshape.1))
    fun t ⟨⟨⟨g₄, o₄⟩, k₄⟩, _, _, sp₄⟩ sy => ?_
  have fS := out_frame (by simp only [aCm1, slot_lin]; omega) o₄
  have ow : ∀ d, d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d := fun d hd =>
    o₄.word (.inl (by simp only [aCm1, slot_lin]; omega)) (by omega)
  refine ⟨h.ctx.step sp₄ k₄.2.1 k₄.2.2 (k₄.gpr (by decide)) (frame4 fS), h.env.keep k₄ (by decide),
    ⟨(ow 0 (by omega)).trans h.lay.len, (ow 48 (by omega)).trans h.lay.wW,
      (ow 224 (by omega)).trans h.lay.strideW, fun j hj => (ow _ (by omega)).trans (h.lay.arrW j hj)⟩,
    ?_, hncl, g₄, (rd_keep hp fS).trans h.rd8, h.hav, sy.trans h.syms, h.tab⟩
  rw [← h.v]
  exact o₄.wordsVal (.inl (by simp only [aCm1, slot_lin]; omega)) (by rw [slot_lin]; omega)

/-- `gcd(c − 1, e) ≠ 1`. -/
theorem gcdFin {s : State} (h : M4 s0 s) (hg : ¬ Nat.gcd (candOf s0 - 1) (eV s0) = 1) :
    WP isa (finish 3) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := cOp_cand h.ctx.fr.pre h.hav
  have hgb : (Nat.gcd (candOf s0 - 1) (eV s0) == 1) = false := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hop
  exact drawnFin 3 (by decide) h.ctx h.rd8 h.hav hop (by rw [outOf, hop]) (by rw [hop]; rfl)


/-! ## The test -/

/-- The scratch region, as `Prep` states it. -/
theorem cS_eq (s0 : State) : cS s0 = ⟨stackArg s0 1, 8 * sL s0⟩ := by simp only [cS, sL, Nat.mul_comm]

/-- The round's frame: the 96 bytes below the body's stack pointer. -/
theorem below_fb (s0 : State) : VG.RISCV64.below (fb s0) 96 = rF s0 := by
  simp only [VG.RISCV64.below, rF, fb_eq, BitVec.add_sub_cancel]

/-- What holds of the call throughout the test, for the candidate `c` of `w`
words. -/
structure TC (s0 : State) (w c : Nat) : Prop where
  h35 : slot w nArr ≤ 8 * sL s0
  shape : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c
  hw : oL s0 = 8 * w
  hw4 : 4 ≤ w
  hw64 : w ≤ 64
  h8 : 8 * w ≤ rL s0
  tab : TabOk s0
  hop : cOp s0 = if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then some (.rejected, (rB s0).drop (8 * w))
    else (Spec.RsaKeyGen.primalityTest c ((rB s0).drop (8 * w))).map
      fun pr => (if pr.1 then .prime c else .rejected, pr.2)

theorem TC.c8 {w c : Nat} (h : TC s0 w c) : 8161 < c := by
  have := h.shape.2.1
  have : 2 ^ 14 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by have := h.hw4; omega)
  omega

/-- The facts once `gcd(c − 1, e) = 1`. -/
structure TIn (s0 s : State) (w c : Nat) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

/-- The test's arguments in the header. -/
structure THdr (s0 : State) (w : Nat) (m : Mem) : Prop where
  rand : word m (stackArg s0 1) (8 * hRand) = s0.gpr .a7
  randLen : word m (stackArg s0 1) (8 * hRandLen) = BitVec.ofNat 64 (rL s0)
  used : word m (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  kk : word m (stackArg s0 1) (8 * hK) = BitVec.ofNat 64 (8 * w)
  checks : word m (stackArg s0 1) (8 * hChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)

theorem THdr.keep {w : Nat} {m m' : Mem} (h : THdr s0 w m)
    (ow : ∀ d, 128 ≤ d → d + 8 ≤ 224 → word m' (stackArg s0 1) d = word m (stackArg s0 1) d) : THdr s0 w m' :=
  ⟨(ow _ (by simp only [hRand]; omega) (by simp only [hRand]; omega)).trans h.rand,
    (ow _ (by simp only [hRandLen]; omega) (by simp only [hRandLen]; omega)).trans h.randLen,
    (ow _ (by simp only [hUsed]; omega) (by simp only [hUsed]; omega)).trans h.used,
    (ow _ (by simp only [hK]; omega) (by simp only [hK]; omega)).trans h.kk,
    (ow _ (by simp only [hChecks]; omega) (by simp only [hChecks]; omega)).trans h.checks⟩

/-- After `testArgs`. -/
structure T1 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  hdr : THdr s0 w s.mem
  trial : word s.mem (stackArg s0 1) (8 * hTrial) = BitVec.ofNat 64 (nTrial w)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem argsS {s : State} {w c : Nat} (h : TIn s0 s w c) : WP isa (.block testArgs) s (T1 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hZ := h.tc.h35
  have hnw := h.env.hs.nowrap
  simp only [nArr, slot_lin] at hZ
  refine WP.mono_syms (WP.rdwr (testArgs_ok hf h.env)) fun t ⟨⟨⟨ao, o₁⟩, k₁⟩, _, _, sp₁⟩ sy => ?_
  have fS := out_frame (by omega) o₁
  have ow : ∀ d, d + 8 ≤ 128 ∨ 224 ≤ d → d + 8 ≤ 8 * sL s0 →
      word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d :=
    fun d hd hd' => o₁.word hd (by omega)
  refine ⟨h.ctx.step sp₁ k₁.2.1 k₁.2.2 (k₁.gpr (by decide)) (frame4 fS), h.env.keep k₁ (by decide),
    ⟨(ow 0 (by omega) (by omega)).trans h.lay.len, (ow 48 (by omega) (by omega)).trans h.lay.wW,
      (ow 224 (by omega) (by omega)).trans h.lay.strideW,
      fun j hj => (ow _ (by omega) (by omega)).trans (h.lay.arrW j hj)⟩, ?_,
    ⟨ao.rand.trans hf.wRand, ao.randLen.trans (hf.rl.trans (bv_ofNat_toNat _).symm), ao.used.trans h.rd8,
      ao.k.trans (hf.wOutLen.trans (by rw [← h.tc.hw]; exact (bv_ofNat_toNat _).symm)),
      ao.checks⟩, ao.trial, (rd_keep hp fS).trans h.rd8, sy.trans h.syms, h.tc⟩
  rw [← h.arr0]
  exact (show VG.Proof.Mont.Outside _ _ _ s.mem t.mem from o₁).wordsVal (.inr (by rw [slot_lin]; omega))
    (by rw [slot_lin]; omega)

/-- Trial division's start. -/
theorem T1.divIn {s : State} {w c : Nat} (h : T1 s0 w c s) : DivIn s (stackArg s0 1) (8 * sL s0) w (nTrial w) :=
  ⟨h.env, h.trial, by unfold nTrial; split <;> decide, by unfold nTrial; split <;> decide,
    by rw [h.syms]; exact h.tc.tab.fit, by rw [h.syms]; exact h.tc.tab.al,
    by rw [h.syms, h.ctx.fr.rd]; exact h.tc.tab.rd, fun i hi => by rw [h.syms]; exact h.tc.tab.held_at h.ctx.fr hi⟩

/-- After trial division. -/
structure T2 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  env : Env s (stackArg s0 1) (8 * sL s0) w
  lay : Lay s.mem (stackArg s0 1) (sL s0) w
  arr0 : A s.mem (stackArg s0 1) w 0 = c
  hdr : THdr s0 w s.mem
  f : s.gpr .a4 = BitVec.ofNat 64 (if Spec.RsaKeyGen.obviouslyComposite (64 * w) c then 1 else 0)
  rd8 : s.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w)
  syms : s.syms = s0.syms
  tc : TC s0 w c

theorem trialS {trial : Prog isa} (D : DivOk trial) {s : State} {w c : Nat} (h : T1 s0 w c s) :
    WP isa trial s (T2 s0 w c) := by
  refine WP.mono (D.ok h.divIn) fun t ⟨f₂, m₂, g₂, rd₂, wr₂, sp₂, sy₂⟩ => ?_
  rw [h.arr0, show nTrial w = if w ≤ 16 then 512 else 1024 from rfl,
    VG.Proof.RsaKeyGen.trialPrefix_spec h.tc.c8] at f₂
  have k : Keep tdRegs s t := ⟨g₂, rd₂, wr₂⟩
  refine ⟨h.ctx.keep k m₂ sp₂, h.env.keep k (by decide), by rw [m₂]; exact h.lay, by rw [m₂]; exact h.arr0,
    by rw [m₂]; exact h.hdr, f₂, by rw [m₂]; exact h.rd8, sy₂.trans h.syms, h.tc⟩

/-- A divisor: rejected. -/
theorem compFin {s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = true) :
    WP isa (finish 3) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := h.tc.hop
  rw [hoc] at hop
  simp only [↓reduceIte] at hop
  have hw := h.tc.hw
  have h8 := h.tc.h8
  refine fin_ok 3 (by decide) h.ctx (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
  rw [h.rd8, usedOf, hop]
  simp only [hlen_drop]
  congr 1; omega

/-- The working space prepared. -/
structure T3 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  kc : KCtx s (stackArg s0 1) (sL s0) w c (s0.gpr .a7) (rL s0) (VG.Proof.RsaKeyGen.checksW w)
  hu0 : word s.mem (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (8 * w)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem prepS {s : State} {w c : Nat} (h : T2 s0 w c s)
    (hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false) :
    WP isa VG.Impl.MillerRabin.RISCV64.Search.montPrepHi s (T3 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hZ := h.tc.h35
  have hnw := h.env.hs.nowrap
  have hw4 := h.tc.hw4
  have hw64 := h.tc.hw64
  simp only [nArr, slot_lin] at hZ
  have hfS := hp.fS
  refine WP.mono (WP.rdwr (prep_ok h.env h.lay h.arr0 h.tc.shape.1 (by have := h.tc.c8; omega) (by
    have := h.tc.shape.2.1
    have : 2 ^ (64 * (w - 1)) < 2 ^ (64 * w - 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega))) fun t ⟨⟨⟨p₃, o₃⟩, k₃⟩, rd₃, wr₃, sp₃⟩ => ?_
  have hr : ∀ x ∈ VG.Proof.MillerRabin.RISCV64.Search.mpRanges w, x.1 + x.2 ≤ 8 * sL s0 := fun x hx => by
    simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega
  have fS : Frame [cS s0] s.mem t.mem := fun x hx => o₃ x fun r hr' => .inr (by
    have := hx _ List.mem_cons_self
    have := hr r hr'
    simp only [Region.Contains, cS, sL, ofs] at *
    omega)
  have c₃ := h.ctx.step sp₃ k₃.2.1 k₃.2.2 (k₃.gpr (by decide)) (frame4 fS)
  have ow₃ : ∀ d, 64 ≤ d → d + 8 ≤ 256 → word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d :=
    fun d h1 h3 => (show VG.Proof.Bignum.Frm _ (VG.Proof.MillerRabin.RISCV64.Search.mpRanges w) s.mem t.mem
      from o₃).word_eq (fun x hx => by
      simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega) (by omega)
  have hd := h.hdr.keep (m' := t.mem) fun d h1 h2 => ow₃ d (by omega) (by omega)
  have hrl : rL s0 < 2 ^ 64 := (stackArg s0 0).isLt
  have hfr := hp.fr
  have sp₃' : t.sp = fb s0 := sp₃.trans hf.sp
  have hbF : VG.RISCV64.below t.sp 96 = rF s0 := by rw [sp₃']; exact below_fb s0
  have spN : (fb s0).toNat = s0.sp.toNat - 192 := fb_toNat hp
  have hsp16 := hp.sp16
  have hspLo := hp.spLo
  refine ⟨c₃, ⟨p₃, hd.rand, hd.randLen, hd.kk, hd.checks,
    (VG.Proof.RsaKeyGen.cand_bits (by omega) h.tc.shape).2.1,
    by have := VG.Proof.RsaKeyGen.checksW_le w; omega, hrl,
    fun i hi => ⟨cR s0, List.mem_append_left _ (by rw [rd₃, hf.rd]; exact hp.rR),
      Offset.contains_base _ (by simp only [rL] at hi; omega) (by omega)⟩,
    fun i hi x hx e => ?_, by rw [sp₃', spN]; omega, by rw [sp₃', spN]; omega,
    by rw [hbF, ← cS_eq]; exact hp.FS.sub_left (rF_sub s0), fun i hi hc => ?_⟩, hd.used, h.tc, hoc⟩
  · refine hp.rS _ (Offset.contains_base _ (d := i) (by simp only [rL] at hi; omega) (by omega)) ?_
    show Region.Contains _ (s0.gpr .a7 + BitVec.ofNat 64 i) 1
    rw [e]
    show (x - stackArg s0 1).toNat + 1 ≤ (stackArg s0 2).toNat * 8
    have : (x - stackArg s0 1).toNat < 8 * (stackArg s0 2).toNat := hx
    omega
  · rw [hbF] at hc
    exact hp.Fr _ ((rF_sub s0) _ hc) (Offset.contains_base _ (d := i) (by simp only [rL] at hi; omega) (by omega))

/-- After the witnesses. -/
structure T4 (s0 : State) (w c : Nat) (s : State) : Prop where
  ctx : Ctx s0 s
  prep : Prep s (stackArg s0 1) (sL s0) w c
  res : match Spec.RsaKeyGen.primalityTest c ((rB s0).drop (8 * w)) with
    | none => word s.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 0
    | some (b, rest) => word s.mem (stackArg s0 1) (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
        word s.mem (stackArg s0 1) (8 * hUsed) = BitVec.ofNat 64 (rL s0 - rest.length)
  tc : TC s0 w c
  noc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false

theorem mrStage {s : State} {w c : Nat} (R : RoundImpl) (h : T3 s0 w c s) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Witness.millerRabin R.name R.code) s (T4 s0 w c) := by
  have hf := h.ctx.fr
  have hp := hf.pre
  have hrl : rL s0 < 2 ^ 64 := (stackArg s0 0).isLt
  have htape : Spec.Rsa.bytesAt s.mem (s0.gpr .a7) (rL s0) = rB s0 := bytes_keep hf.out hrl fun ρ hρ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact hp.oR.symm
    · exact hp.uR.symm
    · exact hp.rS
    · exact hp.Fr.symm
  have hpt := VG.Proof.RsaKeyGen.primalityTest_cand (by have := h.tc.hw4; omega) h.tc.shape ((rB s0).drop (8 * w))
  rw [VG.Proof.RsaKeyGen.checksW_eq w (by have := h.tc.hw64; omega) h.tc.hw4] at hpt
  refine WP.mono (millerRabin_ok R h.kc h.hu0 htape h.tc.h8 hpt) fun t ⟨lk, res⟩ => ?_
  have hbF : VG.RISCV64.below s.sp 96 = rF s0 := by rw [hf.sp]; exact below_fb s0
  have f₄ : Frame [cU s0, cS s0, rF s0, rdW s0] s.mem t.mem := by
    have := lk.frame
    rw [hbF, ← cS_eq] at this
    exact this.mono (by simp)
  exact ⟨h.ctx.step lk.sp lk.rd lk.wr lk.s11 f₄, lk.prep, res, h.tc, h.noc⟩

theorem T4.result_ok {s : State} {w c : Nat} (h : T4 s0 w c s) :
    WP isa testResult s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hop := h.tc.hop
  rw [h.noc] at hop
  simp only [Bool.false_eq_true, ↓reduceIte] at hop
  exact res_ok h.ctx h.prep h.tc.hw h.res hop

/-- Once `gcd(c − 1, e) = 1`: trial division, then Miller–Rabin. -/
theorem test_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s : State} {w c : Nat}
    (h : TIn s0 s w c) :
    WP isa (test trial R.name R.code) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs]
  refine WP.seq (WP.mono (argsS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (trialS D h₁) fun t₂ h₂ => ?_)
  refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero_ofNat _ _ (by split <;> decide) h₂.f) (fun hz => ?_)
    (fun hz => ?_)
  · exact compFin h₂ (by revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide)
  · have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * w) c = false := by
      revert hz; cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> decide
    refine WP.seq (WP.mono (prepS h₂ hoc) fun t₃ h₃ => ?_)
    exact WP.seq (WP.mono (mrStage R h₃) fun t₄ h₄ => h₄.result_ok)

/-! ## The body -/

theorem toTIn {s : State} (h : M4 s0 s) (hg : Nat.gcd (candOf s0 - 1) (eV s0) = 1) :
    TIn s0 s (cw s0) (candOf s0) := by
  have hp := h.ctx.fr.pre
  obtain ⟨hw, hw4, hw64⟩ := cw_facts hp
  have hop := cOp_cand hp h.hav
  have hgb : (Nat.gcd (candOf s0 - 1) (eV s0) == 1) = true := by simp [hg]
  rw [VG.Proof.RsaKeyGen.afterDraw, h.ncl] at hop
  simp only [hgb, Bool.and_true, Bool.false_eq_true, ↓reduceIte] at hop
  refine ⟨h.ctx, h.env, h.lay, h.v, h.rd8, h.syms,
    ⟨h35_of hp hw, VG.Proof.RsaKeyGen.candidate_shape (by omega) _, hw, hw4, hw64, by have := h.hav; omega, h.tab,
      ?_⟩⟩
  rw [hop]
  cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> rfl

theorem main_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s : State} (h : MIn s0 s) :
    WP isa (main trial R.name R.code) s fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  unfold main
  simp only [VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs]
  refine WP.seq (WP.mono (setupS h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (loadCS h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (closeS h₂) fun t₃ h₃ => ?_)
  refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero_ofNat _ _ (by split <;> decide) h₃.f) (fun hz => ?_)
    (fun hz => ?_)
  · exact closeFin h₃ (by revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide)
  · have hncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false := by
      revert hz; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
    refine WP.seq (WP.mono (gcdS h₃ hncl) fun t₄ h₄ => ?_)
    refine WP.ite _ (VG.RISCV64.Steps.eval_nonzero _ _) (fun hz => ?_) (fun hz => ?_)
    · exact gcdFin h₄ fun e => by rw [h₄.g.mpr e] at hz; exact absurd hz (by decide)
    · exact test_ok D R (toTIn h₄ (h₄.g.mp (by simpa using hz)))

/-- The flag of `rand`'s length: whether it has the candidate's octets. -/
theorem flagI {s : State} (hf : Fr s0 s) :
    WP isa (.block ([ldf .t3 oRandLen, ldf .t4 oOutLen] ++ VG.Impl.MillerRabin.RISCV64.Search.geFlag .t2 .t3 .t4))
      s fun t => t.gpr .t2 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0) ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, hf.load (r := .t3) (o := oRandLen) (by decide) (by decide), ?_⟩
  have h1 : Fr s0 (s.write .t3 (s.mem.readW (fw s0 oRandLen) 64)) :=
    hf.step (sp_write _ _ _) (rd_write _ _ _) (wr_write _ _ _) (by rw [gpr_write_of_ne _ _ (by decide)])
      (by rw [mem_write]; exact Frame.refl _ _)
  refine WP.block_cons_iff.mpr ⟨_, h1.load (r := .t4) (o := oOutLen) (by decide) (by decide), WP.block_nil ?_⟩
  refine WP.mono (VG.Proof.MillerRabin.RISCV64.Search.geFlag_ok (d := .t2) (x := rL s0) (y := oL s0) ?_ ?_
    (stackArg s0 0).isLt (s0.gpr .a1).isLt) fun t ⟨⟨t2, tm⟩, _⟩ => ⟨t2, by rw [tm]; simp only [mem_write]⟩
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hf.rl, bv_ofNat_toNat]
  · rw [gpr_write_self, mem_write, hf.wOutLen, bv_ofNat_toNat]

/-- The body between the entry and the restore. -/
theorem mid_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) (hT : TabOk s0) {s : State} (hf : Fr s0 s)
    (h6 : s.gpr .s6 = stackArg s0 1) (sy : s.syms = s0.syms) :
    WP isa (mid trial R.name R.code) s fun u => Fr s0 u ∧ CQ s0 (u.gpr .a0) u.mem := by
  have hp := hf.pre
  unfold mid
  refine WP.seq (WP.mono_syms (WP.rdwr (zeroOut_ok hf)) fun t₁ ⟨⟨c₁, _, k₁⟩, _, _, sp₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (WP.rdwr (WP.keep [.t3, .t4, .t2] (flagI c₁.fr) (by rfl) (by rfl)))
    fun t₂ ⟨⟨⟨f₂, m₂⟩, k₂⟩, _, _, sp₂⟩ sy₂ => ?_)
  have c₂ := c₁.keep k₂ m₂ sp₂
  refine WP.ite _ (VG.RISCV64.Steps.eval_zero_ofNat _ _ (by split <;> decide) f₂) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact finNone_post c₂ (cOp_none hp hav)
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact main_ok D R ⟨c₂, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h6), hav,
      sy₂.trans (sy₁.trans sy), hT⟩

/-- The whole function: its results are the contract's. -/
theorem code_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) (h : CIn s0) (hT : TabOk s0) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.code trial R.name R.code) s0
      fun t => abiPreserved s0 t ∧ CQ s0 (t.gpr .a0) t.mem :=
  code_ok h fun _ hf h6 _ sy => mid_ok D R hT hf h6 sy
end

end VG.Proof.RsaKeyGen.RISCV64.Cand

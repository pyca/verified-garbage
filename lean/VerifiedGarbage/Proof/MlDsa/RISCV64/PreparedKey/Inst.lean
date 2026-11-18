module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.VerifyEntry
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Top
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Prepare
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
meta import VerifiedGarbage.Proof.MlDsa.Round.Ones
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Output
import VerifiedGarbage.Proof.MlDsa.Sign.Setup
import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Output
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `MlDsa.RISCV64.Pack.HintPackCT`, which only this module used -/

section

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Constant time but for the hint, as on AArch64: zeroing `y` leaks only the
pointers and `len` (the taint analysis), and leaves states that agree on
`k`, `ω` and the pointers, and on all the memory the loops may access (the
hint, which the contract lets them leak, and `y`, zeroed); `memTaint`
proves the rest. `omega` is a `u32`, whose register's upper bits the two
runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem pre_of {s : State} (h : (hintBitPackContract RISCV64.abi).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]

theorem ct : ConstantTime isa (hintBitPackContract RISCV64.abi).pre (hintBitPackContract RISCV64.abi).pub
    Impl.MlDsa.RISCV64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.hintBitPack
  refine RelCT.seq (R := MAgree hbpTaint) ?_
    (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a3, .a4]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : pω x = pω y := by simp only [pω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.rd, fy.rd, px.rd, py.rd]; simp only [hR, pH, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.wr, fy.wr, px.wr, py.wr]; simp only [yR, pY, pLen, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fx.a0, fy.a0]; simp only [pH, p3]
    · rw [fx.a1, fy.a1]; simp only [pk, pLen, p7, hω]
    · rw [fx.a2, fy.a2, hω]
    · rw [fx.a3, fy.a3]; simp only [pY, p6]
  · rw [fx.rd, fx.wr, px.rd, px.wr] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      have hxy : ¬ (yR x).Contains a 1 := fun hc' => px.d_hy a hc hc'
      rw [fx.frame a (fun r hr hc' => by simp only [List.mem_singleton] at hr; subst hr; exact hxy hc'),
        fy.frame a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [yR, pY, pLen, ← p6, ← p7] at hc'
          exact hxy hc')]
      exact bytes_of_words (by simpa only [p3, p4] using hleak) (by simpa only [hR, pH, p3, p4] using hc)
    · -- `y`: zeros.
      have hlt : (a - pY x).toNat < pLen x := by simp only [Region.Contains] at hc; omega_using [hc]
      have ea : a = pY x + BitVec.ofNat 64 (a - pY x).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := fx.zero _ hlt
      have h₂ := fy.zero _ (show _ < pLen y by simpa only [pLen, ← p7] using hlt)
      rw [← ea] at h₁
      rw [show pY y = pY x by simp only [pY, p6], ← ea] at h₂
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1024 | .a2 => 80 | .a3 => 0x3000 | .a4 => 84 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

end VG.Proof.MlDsa.RISCV64.Pack.Hint

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint

theorem hintBitPack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.hintBitPack (hintBitPackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hy, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
    exact hy
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | (rw [hintOnes_zero]; exact Nat.zero_le _)
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack

end

end

/-! ### `MlDsa.RISCV64.Sign.Top`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V: the function

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sign/Correct.lean`, `SignCT.lean`,
`Top.lean`). The function returns 1 with `Sign_internal`'s signature (within
`maxBounds`) in `sig`, or 0 when `Sign_internal` returns nothing within
`minBounds` (`sign_ok`): its `ExpandA` or its loop does not finish
(`signMu_min_A`, `signMu_min_L`), or an iteration passes (`signMu_max`). Two
runs whose entry states agree on what the contract makes public leak the same
(`sign_tr`): the prologue and the return only the pointers, `ExpandA` its seed
and results, the loop what `signLeakT` says, and the signature its hint.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relStart relInv)
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Impl.MlDsa.RISCV64.KeyGen (callAt seqR)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign (aSeed amat ParamsOk)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega_using [hj]
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  Proof.MlDsa.Sign.expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
  exact Proof.MlDsa.Sign.signMu_none_A (Proof.MlDsa.Sign.expandA_none
    ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact Proof.MlDsa.Sign.signMu_none_A e
  | some A' =>
    have := Proof.MlDsa.Sign.expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact Proof.MlDsa.Sign.signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  Proof.MlDsa.Sign.signMu_some hA (Proof.MlDsa.Sign.signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega_using [ht]) (iter_pass hp hs hpass))

end

/-! ## Before the return -/

/-- What the return needs: the pointer to `scratch`, our caller's registers in it, and the registers
we preserve. -/
structure TF (p : Params) (STK : Nat) (σ s : State) : Prop where
  s11 : s.gpr .s11 = sScr σ
  sav : TopSaved s.mem (sScr σ) σ
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  inr : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (sScr σ + BitVec.ofNat 64 o) 8

theorem SC1.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC1 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.s11, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay1 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay1_size0]; omega_using [hscr, h₂]) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

theorem SC2.tf {p : Params} (hF : SFacts p) {STK : Nat} {σ s : State} (h : SC2 p STK σ s) : TF p STK σ s := by
  have hs := h.site
  have hscr := hF.scr
  exact ⟨hs.s11, h.sav, h.pres, h.sp, fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := slay2 p STK σ) (o := o)
    (l := 8) (hs.cw 0 (by decide) (by decide)) (by rw [slay2_size0]; omega_using [hscr, h₂]) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)⟩

/-- Before the return: `s4`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (STK : Nat) (σ s : State) : Prop where
  tf : TF p STK σ s
  r01 : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1
  ok : s.gpr .s4 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (sSig σ) p.sigLen)
  bad : s.gpr .s4 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

theorem r24_one {s : State} (h : s.gpr .s4 = 0 ∨ s.gpr .s4 = 1) (hne : s.gpr .s4 ≠ 0) : s.gpr .s4 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

section
variable {P : Prims} {S : Nat} (hP : SPrimsOk P S) {p : Params} (hF : SFacts p) {STK : Nat} (hS : S ≤ STK)
  (hp : ParamsOk p)
include hP hF hS hp

theorem rest_ok {σ : State} (hpre : SPre p STK σ) {s : State} (h : IM p STK σ s) :
    WP isa (rest P p) s (FS p STK σ) := by
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono ((decode_piece hP hF hS).ok σ s hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hF hS hp hpre h1.ik) fun s2 h2 => ?_)
  unfold ifOk ifOkElse
  refine WP.ite _ (Steps.eval_nonzero s2 .s4) (fun hb => ?_) fun hb => WP.block_nil ?_
  · have h1 := r24_one h2.r01 (by simpa using hb)
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h1
    refine WP.mono (output_ok hP hF hS ⟨h2.k, hz, hh, hpass, h1⟩ hct) fun s4 ⟨k4, hb4, h4⟩ =>
      ⟨k4.sc.tf hF, .inr h4, fun _ => ?_, fun h0 => absurd (h0.symm.trans h4) (by decide)⟩
    have e : (slay2 p STK σ).A 4 0 = sSig σ := by simp only [Lay.A, BitVec.add_zero]; rfl
    rw [← e, hb4]
    exact signMu_max hp hA ht hr hs hpass
  · have h0 : s2.gpr .s4 = 0 := by simpa using hb
    exact ⟨h2.k.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
      fun _ => signMu_min_L hA (h2.fail h0)⟩


theorem sign_ok {σ : State} (hpre : SPre p STK σ) (h48 : 1168 ≤ STK) :
    WP isa (sign P p) σ fun s' =>
      RISCV64.target.abiPreserved σ s' ∧ (Proof.MlDsa.signWithCacheContract p RISCV64.abi STK).post σ s' := by
  unfold sign
  refine WP.seq (WP.mono (spro_ok hF h48 hpre) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (expandA_ok hP hF hS h₁.1 h₁.2) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p STK σ) from ?_) fun s₄ h₄ => ?_)
  · unfold ifOk ifOkElse
    refine WP.ite _ (Steps.eval_nonzero s₂ .s4) (fun hb => ?_) fun hb => WP.block_nil ?_
    · exact rest_ok hP hF hS hp hpre (h₂.im (r24_one h₂.r01 (by simpa using hb)))
    · have h0 : s₂.gpr .s4 = 0 := by simpa using hb
      exact ⟨h₂.sc.tf hF, .inl h0, fun h1 => absurd (h0.symm.trans h1) (by decide),
        fun _ => signMu_min_A (h₂.bad h0)⟩
  · refine WP.mono (topEnd_ok h₄.tf.s11 hpre.al_c h₄.tf.sav h₄.tf.inr h₄.tf.pres)
      fun s' ⟨pr, lr, r3, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h₄.tf.sp, lr⟩, ?_⟩
    sig_post [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, RISCV64.abi,
      RISCV64.argRegs]
    rw [r3, m']
    rcases h₄.r01 with h0 | h1
    · exact .inr ⟨by rw [h0]; rfl, h₄.bad h0⟩
    · exact .inl ⟨by rw [h1]; rfl, maxBounds, h₄.ok h1⟩

/-! ## Two runs -/

omit hP hF hS hp in
/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : sPub p σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2.1
  rw [Proof.MlDsa.Sign.signLeak_eq hA₁, Proof.MlDsa.Sign.signLeak_eq hA₂, pub_rho hpub] at e
  exact List.append_cancel_left e

omit hP hF hS hp in
theorem relct_nil {Q : State → State → Prop} {P : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro _ _ _ _ _ _ hr e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, h _ _ hr⟩

omit hP hF hS hp in
theorem hintIs_unique {m : Mem} {a : Addr} {h h' : Vector Bool n} (H : HintIs m a 1 [h]) (H' : HintIs m a 1 [h']) :
    h = h' := by
  apply Vector.ext
  intro j hj
  have e := H.2 0 (by decide) j hj
  have e' := H'.2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, getElem!_pos h j hj, getElem!_pos h' j hj] at e e'
  rw [e] at e'
  revert e'
  cases h[j] <;> cases h'[j] <;> decide

omit hp in
/-- The two runs of the signature, from the end of the loop. -/
theorem outIf_tr :
    RelCT isa (OX p STK) (ifOk (output P p)) fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, _, _, _, _, _, _, e, _⟩ => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e]) ?_ ?_
  · refine liftG (Q₀ := fun _ _ => True) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_)
      (RelCT.mono (output_tr hP hF hS) (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, e24, hh⟩, hb⟩ => ?_) fun _ _ h => h)
    · have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [Steps.eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      exact ⟨_, _, output_ok hP hF hS ⟨h₁.k, z₁, hh₁, ps₁, hx⟩ ct₁, output_ok hP hF hS ⟨h₂.k, z₂, hh₂, ps₂, hy⟩ ct₂,
        fun x' y' a b _ => ⟨σ₁, σ₂, p₁, p₂, pub, a.1.sc, b.1.sc⟩⟩
    · have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
      have hy := r24_one h₂.r01 (by rw [← e24]; rw [Steps.eval_nonzero] at hb; simpa using hb)
      obtain ⟨t₁, -, -, -, ps₁, ct₁, z₁, hh₁⟩ := h₁.pass hx
      obtain ⟨t₂, -, -, -, ps₂, ct₂, z₂, hh₂⟩ := h₂.pass hy
      obtain ⟨f, f₁, f₂⟩ := hh hx
      refine ⟨σ₁, σ₂, p.ℓ * t₁, p.ℓ * t₂, p₁, p₂, pub, ⟨⟨h₁.k, z₁, hh₁, ps₁, hx⟩, ct₁⟩,
        ⟨⟨h₂.k, z₂, hh₂, ps₂, hy⟩, ct₂⟩, fun i hi => ?_⟩
      have a₂ := hh₂ i hi
      rw [← SL_pub pub] at a₂
      exact (hintIs_unique (hh₁ i hi) (f₁ i hi)).trans (hintIs_unique (f₂ i hi) a₂)
  · exact relct_nil fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂, _⟩, _⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.k.sc, h₂.k.sc⟩

/-- `rest`, from runs whose `ExpandA` finished. -/
theorem rest_tr :
    RelCT isa (Rel2 (SPre p STK) (sPub p) (IM p STK)) (rest P p)
      fun x y => Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y := by
  unfold rest
  refine RelCT.mono (P := RS p STK (LeakEq p 0) (IM p STK)) ?_
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub,
      pub_leq pub (expandA_max h₁.ok) (expandA_max h₂.ok), h₁, h₂⟩) fun _ _ h => h
  refine RelCT.seq (pieceRS (decode_piece hP hF hS)) (RelCT.seq ?_ (outIf_tr hP hF hS))
  exact RelCT.mono (signLoop_tr hP hF hS hp) (fun x y h => h.mono fun _ _ h => h.ik) fun _ _ h => h

/-- Two runs whose entry states agree on the public data leak the same. -/
theorem sign_tr (h48 : 1168 ≤ STK) :
    RelCT isa (Rel2 (SPre p STK) (sPub p) fun σ s => s = σ) (sign P p) fun _ _ => True := by
  unfold sign
  refine RelCT.seq (relInv (spro_piece hF h48).ok (spro_piece hF h48).tr) ?_
  refine RelCT.seq (RelCT.mono (expandA_tr hP hF hS) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun x y => Rel2 (SPre p STK) (sPub p) (SC1 p STK) x y ∨
      Rel2 (SPre p STK) (sPub p) (SC2 p STK) x y) ?_
    (relOr (srel1 (fun _ _ h => h) (by taint_decide)) (srel2 (fun _ _ h => h) (by taint_decide)))
  unfold ifOk ifOkElse
  refine RelCT.ite (fun x y ⟨_, e⟩ => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e]) ?_ ?_
  · refine RelCT.mono (rest_tr hP hF hS hp) (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, e⟩, hb⟩ => ?_)
      fun _ _ h => .inr h
    have hx := r24_one h₁.r01 (by rw [Steps.eval_nonzero] at hb; simpa using hb)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, h₁.im hx, h₂.im (r24_one h₂.r01 (by rw [← e, hx]; decide))⟩
  · exact relct_nil fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, _⟩, _⟩ => .inl ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sc, h₂.sc⟩
end

/-! ## The contract -/

/-- A state that satisfies `signWithCacheContract`'s precondition, with an
empty cache, for the contract's satisfiability. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a2 => 0x9000 | .a3 => 0xA000 | .a4 => 0x10000 | .a5 => 0x9800 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩, ⟨0x9800, 0⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_sign_with_cache` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack whose samplers' results are public
(`SPrimsOk`), and `S` at least the 48 bytes the sponge needs. The contract's
satisfiability (`hsat`, by `signSat`) is evaluated once `S` is known. -/
theorem sign_verified {P : Prims} {S : Nat} (hP : SPrimsOk P S) (h48 : 1168 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Proof.MlDsa.signWithCacheContract p RISCV64.abi S).pre (signSat p)) :
    Verified RISCV64.target (sign P p) (Proof.MlDsa.signWithCacheContract p RISCV64.abi S) := by
  have hF := sfacts hp3
  have hp : ParamsOk p := by rcases hp3 with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega_using [h48]⟩
  refine ⟨fun s hs => sign_ok hP hF (Nat.le_refl _) hp (spre_of hs) h48,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨signSat p, hsat⟩⟩
  sig_pub [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, Spec.MlDsa.signSig, RISCV64.abi,
    RISCV64.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  exact relStart (sign_tr hP hF (Nat.le_refl _) hp h48) s₁ s₂ t₁ t₂ s₁' s₂' (spre_of h₁) (spre_of h₂)
    ⟨hsp, h3, h4, h5, h6, h7, hl, h8, h9⟩ e₁ e₂

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-! ### `MlDsa.RISCV64.Round.UseHint`, which only this module used -/

section

/-!
# ML-DSA on RISC-V: `vg_mldsa_use_hint`

As PPC64LE's (`Proof/MlDsa/PPC64LE/Round/UseHint.lean`).

The selection of `γ₂` (`sel_ok'`), then the loop for it: one symbolic
execution of its body for any pointers (`body_ok`), which stores `uhv` of
the coefficient of `r` and the hint word (`uh_val`: the value
`useHint_eq` gives); the invariant says which coefficients of `out` are
done.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.UseHint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW coeffAt_frame zipWith_get useHint_eq
  mem_gamma2s hbF hbM hbF_le hintAt_get natPolyIs_of_toNat reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Round.Bits (dMul_lt kgpr selGpr sel_ok' sel_ct consts_ok)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_val loadImm_imm)

/-! ## Values -/

/-- What the body stores for the coefficient `a` and the hint word `w`. -/
def uhv (g : Nat) (a w : BitVec 64) : BitVec 64 :=
  fixk (BitVec.ofNat 64 (dMod g)) (fixk (BitVec.ofNat 64 (dMod g))
    (hbr g a + (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 -
      (hbr g a * BitVec.ofNat 64 (2 * g) - a) >>> 63 <<< 1 * ((w - 1) >>> 63) + (w - 1) >>> 63 - 1) -
    BitVec.ofNat 64 (dMod g))

/-- The value `useHint_eq` gives. -/
def uhNat (g a : Nat) (b : Bool) : Nat :=
  (if b then (if hbF g a * (2 * g) < a then hbF g a + hbM g + 1 else hbF g a + hbM g - 1)
    else hbF g a + hbM g) % hbM g

/-- `fixup`, a subtraction of `m` and `fixup` again, of `u` in `[-1, m + 1]`:
`u mod m`. -/
theorem fixk2 {m : Nat} (hm : m < 64) (hm0 : 0 < m) {u : BitVec 64} (hu : u.toNat ≤ m + 1 ∨ u.toNat = 2 ^ 64 - 1) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat =
      if u.toNat < m then u.toNat else if u.toNat ≤ m + 1 then u.toNat - m else m - 1 := by
  have hM : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega_using [hm]
  simp only [fixk_eq]
  generalize BitVec.ofNat 64 m = M at hM ⊢
  have h1 : u >>> 63 = 0 ∨ u >>> 63 = 1 := by bv_omega
  rcases h1 with h1 | h1 <;> rw [h1]
  · have h2 : (u + 0 * M - M) >>> 63 = 0 ∨ (u + 0 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega
  · have h2 : (u + 1 * M - M) >>> 63 = 0 ∨ (u + 1 * M - M) >>> 63 = 1 := by bv_omega
    rcases h2 with h2 | h2 <;> rw [h2] <;> split <;> (try split) <;> bv_omega

/-- `fixk2` of `u = x - m`, for `x` in `[m - 1, 2m + 1]`: `x mod m`. -/
theorem fixk2_mod {m : Nat} (hm : m < 64) (hm1 : 1 < m) {u : BitVec 64} {x : Nat} (hx : x ≤ 2 * m + 1)
    (hu : u.toNat + m = x ∨ (u.toNat = 2 ^ 64 - 1 ∧ x = m - 1)) :
    (fixk (BitVec.ofNat 64 m) (fixk (BitVec.ofNat 64 m) u - BitVec.ofNat 64 m)).toNat = x % m := by
  rw [fixk2 hm (by omega_using [hm1]) (by omega_using [hx, hu])]
  have m1 : ∀ y, m ≤ y → y < 2 * m → y % m = y - m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega_using [h2])]
  have m2 : ∀ y, 2 * m ≤ y → y < 3 * m → y % m = y - 2 * m := fun y h1 h2 => by
    rw [Nat.mod_eq_sub_mod (by omega_using [h1]), m1 _ (by omega_using [h1]) (by omega_using [h2])]; omega_using []
  rcases hu with hu | ⟨hu, rfl⟩
  · split
    · rw [m1 _ (by omega_using [hu]) (by omega_arith)]; omega_using [hu]
    · split
      · rw [m2 _ (by omega_arith) (by omega_using [hm1, hx])]; omega_using [hu]
      · omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_using [hm1])]
    split
    · omega_arith
    · split <;> omega_arith

theorem uh_val {g : Nat} (hg : g ∈ gamma2s) {a w : BitVec 64} (ha : a.toNat < q) (hw : w.toNat < 2 ^ 32) :
    (uhv g a w).toNat = uhNat g a.toNat (decide (w.toNat ≠ 0)) := by
  have hr := hbr_toNat hg ha
  have hf := hbF_le hg ha
  have hm := dMod_eq hg
  obtain ⟨-, m64⟩ := dMod_pos hg
  have m1 : 1 < dMod g := by unfold dMod; split <;> decide
  have hg2 : 2 * g ≤ 523776 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  have hF : (hbr g a).toNat ≤ dMod g := by rw [hr, hm]; exact hf
  unfold uhv uhNat
  rw [← hr, ← hm]
  generalize hbr g a = F at hF ⊢
  have hF44 : F.toNat ≤ 44 := Nat.le_trans hF (by unfold dMod; split <;> decide)
  rw [VG.Proof.MlDsa.Round.q_eq] at ha
  have hP : (F * BitVec.ofNat 64 (2 * g)).toNat = F.toNat * (2 * g) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hg2] : 2 * g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul hF44 hg2) (by decide))
  have hpf : F.toNat * (2 * g) ≤ 44 * 523776 := Nat.mul_le_mul hF44 hg2
  generalize F * BitVec.ofNat 64 (2 * g) = P at hP ⊢
  have z : (w - 1) >>> 63 = if w.toNat = 0 then 1 else 0 := by split <;> bv_omega
  have s : (P - a) >>> 63 = if P.toNat < a.toNat then 1 else 0 := by split <;> bv_omega
  rw [z, s, ← hP]
  by_cases hw0 : w.toNat = 0 <;> by_cases hs : P.toNat < a.toNat <;>
    simp only [hw0, hs, ite_true, ite_false, decide_true, decide_false, ne_eq, not_true_eq_false,
      not_false_eq_true, Bool.false_eq_true]
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (Or.inl (by bv_omega_using [hF, hF44, m1, m64]))
  · exact fixk2_mod m64 m1 (by omega_using [hF]) (by bv_omega_using [hF, hF44, m1, m64])

/-! ## The loop body -/

/-- What an iteration does, for the value stored. -/
def Step (s : State) (x y w c : BitVec 64) (v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a3 = w + 4 ∧ s'.gpr .t3 = c - 1 ∧
    (∀ r ∈ [Reg.a2, .a7, .t1, .t2], s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem.writeW w v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {g : Nat} {s : State} {x y w c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y)
  (h6 : s.gpr .a3 = w) (h7 : s.gpr .t3 = c) (h5 : s.gpr .a2 = BitVec.ofNat 64 (2 * g))
  (h10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g))
  (ix : InRegions (s.rd ++ s.wr) x 4) (iy : InRegions (s.rd ++ s.wr) y 4) (ow : InRegions s.wr w 4)
  (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (aw : w.toNat % 4 = 0)
include h3 h4 h6 h7 h5 h10 h11 h12 ix iy ow ax ay aw

theorem body_ok :
    WP isa (.block (uhBody g)) s
      (Step s x y w c ((uhv g ((s.mem.readW y 32).setWidth 64) ((s.mem.readW x 32).setWidth 64)).setWidth 32)) := by
  have hS := dShift_lt g
  crun [uhBody, hbRaw, fixup, Step, uhv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12, ix, iy, ow, ax, ay, aw, hS,
    preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Hp : Addr := s₀.gpr .a0
abbrev Rp : Addr := s₀.gpr .a1
abbrev G : BitVec 32 := (s₀.gpr .a2).setWidth 32
abbrev O : Addr := s₀.gpr .a3

/-- The values stored. -/
def outs (g : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj rj => (useHint g hj rj).toNat) ((hintAt s₀.mem (Hp s₀) 1).headD (Vector.replicate n false))
    (polyAt s₀.mem (Rp s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Hp s₀), pR (Rp s₀)]
  wr : s₀.wr = [pR (O s₀)]
  dh : (pR (Hp s₀)).Disjoint (pR (O s₀))
  dr : (pR (Rp s₀)).Disjoint (pR (O s₀))
  fitH : (Hp s₀).toNat + 1024 ≤ 2 ^ 64
  fitR : (Rp s₀).toNat + 1024 ≤ 2 ^ 64
  fitO : (O s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  red : Reduced s₀.mem (Rp s₀)
  alH : (Hp s₀).toNat % 4 = 0
  alR : (Rp s₀).toNat % 4 = 0
  alO : (O s₀).toNat % 4 = 0

/-- After `i` iterations. -/
structure Inv (g : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = Hp s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = Rp s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = O s₀ + BitVec.ofNat 64 (4 * i)
  r7 : s.gpr .t3 = BitVec.ofNat 64 (256 - i)
  r5 : s.gpr .a2 = BitVec.ofNat 64 (2 * g)
  r10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (O s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ g)[j]!

theorem out_lt {g : Nat} (hg : g ∈ gamma2s) (s₀ : State) {i : Nat} (hi : i < 256) : (outs s₀ g)[i]! < 64 := by
  rw [outs, zipWith_get _ _ _ hi, useHint_eq hg, Int.toNat_natCast]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by rcases mem_gamma2s hg with rfl | rfl <;> decide))
    (by rcases mem_gamma2s hg with rfl | rfl <;> decide)

theorem out_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    (uhv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64) ((coeffAt s₀.mem (Hp s₀) i).setWidth 64)).setWidth 32 =
      BitVec.ofNat 32 (outs s₀ g)[i]! := by
  obtain ⟨ea, ha⟩ := HighLow.load_toNat hp.red hi
  have hw : ((coeffAt s₀.mem (Hp s₀) i).setWidth 64).toNat = (coeffAt s₀.mem (Hp s₀) i).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (coeffAt s₀.mem (Hp s₀) i).isLt; omega_using [])
  have e := uh_val hg ha (by rw [hw]; exact (coeffAt s₀.mem (Hp s₀) i).isLt)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, e, BitVec.toNat_ofNat, outs, zipWith_get _ _ _ hi, useHint_eq hg,
    Int.toNat_natCast, hintAt_get _ _ hi, ea, hw, uhNat]
  have hb : decide ((coeffAt s₀.mem (Hp s₀) i).toNat ≠ 0) = decide (coeffAt s₀.mem (Hp s₀) i ≠ 0) :=
    decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl),
      fun h e => h (BitVec.eq_of_toNat_eq (by simpa using e))⟩
  rw [hb]

theorem inv_step {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv g s₀ i s) :
    WP isa (.block (uhBody g)) s fun s' => Inv g s₀ (i + 1) s' ∧ (s'.gpr .t3 != 0) = decide (i + 1 ≠ 256) := by
  have cH := coeff_contains (Hp s₀) (i := i) hi
  have cR := coeff_contains (Rp s₀) (i := i) hi
  have cO := coeff_contains (O s₀) (i := i) hi
  have hd : ∀ {p : Addr}, (pR p).Disjoint (pR (O s₀)) → ∀ r ∈ [pR (O s₀)], (pR p).Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  have eR : s.mem.readW (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i :=
    coeffAt_frame h.frame (hd hp.dr) hi
  have eH : s.mem.readW (Hp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Hp s₀) i :=
    coeffAt_frame h.frame (hd hp.dh) hi
  have hv := out_val hg hp hi
  rw [← eR, ← eH] at hv
  refine WP.mono (body_ok h.r3 h.r4 h.r6 h.r7 h.r5 h.r10 h.r11 h.r12 ?_ ?_ ?_ (align4_add hp.alH i)
      (align4_add hp.alR i) (align4_add hp.alO i))
    fun s' ⟨r3, r4, r6, r7, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_,
      (kp .a2 (by simp)).trans h.r5, (kp .a7 (by simp)).trans h.r10, (kp .t1 (by simp)).trans h.r11,
      (kp .t2 (by simp)).trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cO⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r7]; exact count_sub hi
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cO
  · intro j hj hji
    rw [m, hv, show O s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (O s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact h.coeff j hj (by omega_using [hji, e])
  · rw [r7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-! ## The function -/

/-- What the function leaves. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    ∀ j < 256, coeffAt s.mem (O s₀) j = BitVec.ofNat 32 (outs s₀ (G s₀).toNat)[j]!

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa useHint s₀ (Post s₀) := by
  refine sel_ok' (rg := .a2) (by decide) hp.g fun g hg hG s hgpr hm hrd hwr hsp => ?_
  have e : (if g = g32 then uhLoop g32 else uhLoop g88) = uhLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e]
  have b2 : 2 * g < 2 ^ 31 - 2048 := by rcases mem_gamma2s hg with rfl | rfl <;> decide
  unfold uhLoop
  rw [List.append_assoc]
  refine WP.seq (consts_ok ?_)
  simp only [loadImm, List.cons_append, List.nil_append]
  refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (loadImm_imm _))
    (Steps.WP.cons (exec_li (by decide)) (WP.block_nil ?_)))
  refine WP.mono (wp_loop_nz (Inv g s₀) (N := 256) (by decide) (fun i hi s h => inv_step hg hp hi h)
    (fun _ h => h) ?_) fun s' h' => ⟨h'.pres, h'.sp, h'.lr, fun j hj => hG ▸ h'.coeff j hj hj⟩
  have e5 := loadImm_val b2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrd, hwr, hsp, ?_, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_using [])⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e5
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · have : r ≠ .t0 ∧ r ≠ .a2 ∧ r ≠ .a4 ∧ r ≠ .t3 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2.1, this.2.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.useHintContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 95232 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified RISCV64.target useHint (Proof.MlDsa.useHintContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .a2) (by decide) [.a0, .a1, .a3] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs]
    refine natPolyIs_of_toNat fun j hj => ?_
    rw [h.2.2.2 j hj, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (out_lt hp.g s hj) (by decide))
  · sig_pub [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.2
    · exact h.2.2.2.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.useHintContract, Proof.MlDsa.useHintSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.UseHint

end

end

/-! ### `MlDsa.RISCV64.Sign.Inst`, which only this module used -/

section

/-!
# ML-DSA signing on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers' Keccak frames; the others use none),
and their frames use no more; with the 1168 bytes they are verified with, the
two samplers whose results signing branches on return
what depends only on their public data, and succeed only if their algorithm
finishes within `maxBounds` (`rn_ret`, `sb_ret`, from what their own proofs
say they return). So signing with them is verified with 1168
(`sign44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sign

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Sign
open VG.Proof.MlDsa.Sign (ifn rejNTTPoly_mono sampleInBall_mono)
open VG.Proof.MlDsa.Sample (rnFold ballFold rejNTT_some sampleInBall_some)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The samplers' results -/

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.rejNTT s tr s') :
    s'.gpr .a0 = if (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.RejNtt.correct (Sample.RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract RISCV64.abi 1168).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 34 = bytesAt s₂.mem (s₂.gpr .a0) 34 := by
  sig_pub [rejNTTContract, rejNTTSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract RISCV64.abi 1168).pre s)
    (e : Exec isa Impl.MlDsa.RISCV64.Sample.sampleInBall s tr s') :
    s'.gpr .a0 = if (ballFold ((s.gpr .a2).setWidth 32).toNat
      (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.Ball.correct (Sample.Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract RISCV64.abi 1168).pub s₁ s₂) :
    (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧
      bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat = bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat := by
  sig_pub [sampleInBallContract, sampleInBallSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨_, hb, _, _, h5, _⟩ := h
  exact ⟨h5, Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem zero_ne_one32 : (BitVec.setWidth 32 (0 : BitVec 64)) ≠ 1 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_ok : SPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNTT := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  expandMask := ⟨⟨1168, by decide, Sample.expandMask_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  highBits := ⟨⟨0, by decide, Round.HighLow.high_verified⟩, by decide +kernel⟩
  lowBits := ⟨⟨0, by decide, Round.HighLow.low_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩
  makeHint := ⟨⟨0, by decide, Round.MakeHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  hintBitPack := ⟨⟨0, by decide, Pack.hintBitPack_verified⟩, by decide +kernel⟩
  rejX := ⟨1168, by decide, Sample.rejNTT_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩,
    fun s t s' h e h1 => by
      rw [rn_ret h e] at h1
      by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .a0) 34) 1008)).length = 256
      · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩
  ballX := ⟨1168, by decide, Sample.sampleInBall_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩,
    fun s t s' h e h1 => by
      rw [sb_ret h e] at h1
      by_cases hf : (ballFold ((s.gpr .a2).setWidth 32).toNat
        (H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 272)).2 = 256
      · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some _ (by decide) hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩

theorem withCache44_sat : (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168).pre (signSat mlDsa44) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache44
      (Proof.MlDsa.signWithCacheContract mlDsa44 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168).pre (signSat mlDsa65) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache65
      (Proof.MlDsa.signWithCacheContract mlDsa65 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168).pre (signSat mlDsa87) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, RISCV64.abi,
    RISCV64.argRegs, signSat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.withCache87
      (Proof.MlDsa.signWithCacheContract mlDsa87 RISCV64.abi 1168) :=
  sign_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Sign

end

end

/-! ### `MlDsa.RISCV64.Verify.Inst`, which only this module used -/

section

/-!
# ML-DSA verification on RISC-V, with this library's primitives

The RISC-V implementations of the primitives (`prims`) are verified with at
most 1168 bytes of stack (the samplers', for the sponge's frames; the others
use none), and their frames use no more (`prims_ok`), so verification with
them is verified with 1168 (`verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Verify

open VG VG.RISCV64
open VG.Impl.MlDsa.RISCV64.Verify

theorem prims_ok : VPrimsOk prims 1168 where
  ntt := ⟨⟨0, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨0, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨1168, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨1168, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨0, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨0, by decide, Pack.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem withCache44_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa44) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified RISCV64.target withCache44 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa44 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inl rfl) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa65) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified RISCV64.target withCache65 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa65 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inl rfl)) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168).pre
    (verifySat Spec.MlDsa.mlDsa87) := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, RISCV64.abi,
    RISCV64.argRegs, verifySat]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified RISCV64.target withCache87 (Proof.MlDsa.verifyWithCacheContract Spec.MlDsa.mlDsa87 RISCV64.abi 1168) :=
  verify_verified prims_ok (by decide) _ (.inr (.inr rfl)) withCache87_sat

end VG.Proof.MlDsa.RISCV64.Verify

end

end


/-!
# ML-DSA on RISC-V: the entries of the kernels, with this library's kernels

`vg_mldsa*_sign` and `vg_mldsa*_verify` call `vg_mldsa*_sign_with_cache` and
`vg_mldsa*_verify_with_cache` (`Sign/Inst.lean`, `Verify/Inst.lean`), verified
with 1168 bytes of stack, in a frame of 16: so they are verified with 1184
(`sign44_verified`, `verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64
open VG.Spec.MlDsa

/-- A state that satisfies `signContract`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a2 => 0x9000 | .a3 => 0xA000 | .a4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scratchWords p * 8⟩]

theorem sign44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign44 (signContract mlDsa44 RISCV64.abi 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ false
    ⟨signSat mlDsa44, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign65 (signContract mlDsa65 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ false
    ⟨signSat mlDsa65, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign87 (signContract mlDsa87 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ false
    ⟨signSat mlDsa87, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

/-- A state that satisfies `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scratchWords p * 8⟩]

theorem verify44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify44 (verifyContract mlDsa44 RISCV64.abi 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa44, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify65 (verifyContract mlDsa65 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa65, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify87 (verifyContract mlDsa87 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa87, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

/-! ## Preparing keys -/

/-- A state that satisfies the precondition of preparing a key of `kl` bytes
into `ol`, with the buffer (`buf`) or without it. -/
def prepSat (kl ol : Nat) (buf : Bool) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x4000 | .a2 => 0x10000 | .a3 => 0x11000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, kl⟩]
  wr := [⟨0x4000, ol⟩, ⟨0x10000, 1024⟩] ++ if buf then [⟨0x11000, 1072⟩] else []

theorem preparePublic44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa44)
      (preparePublicKeyContract mlDsa44 RISCV64.abi 1072) :=
  preparePublic_verified (.inl rfl)
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa44)
      (prepareSecretKeyContract mlDsa44 RISCV64.abi 1072) :=
  prepareSecret_verified (.inl rfl)
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa65)
      (preparePublicKeyContract mlDsa65 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa65)
      (prepareSecretKeyContract mlDsa65 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa87)
      (preparePublicKeyContract mlDsa87 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa87)
      (prepareSecretKeyContract mlDsa87 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

/-! ## Signing and verifying with a prepared key -/

/-- A prepared private key, at `0x4000` of some memory: the one `prepareSecret` writes from `prepSat`. -/
theorem secret_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret p)
      (prepareSecretKeyContract p RISCV64.abi 1072))
    (hs : (prepareSecretKeyContract p RISCV64.abi 1072).pre (prepSat p.skLen (preparedSecretKeyBytes p) false)) :
    ∃ m, PreparedSecretKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A prepared public key, at `0x4000` of some memory. -/
theorem public_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic p)
      (preparePublicKeyContract p RISCV64.abi 1072))
    (hs : (preparePublicKeyContract p RISCV64.abi 1072).pre (prepSat p.pkLen (preparedPublicKeyBytes p) false)) :
    ∃ m, PreparedPublicKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A state that satisfies `preparedSignContract`'s precondition, with the prepared key in `m`. -/
def psSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x10100 | .a3 => 0x11000 | .a4 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedSecretKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x10100, 32⟩]
  wr := [⟨0x11000, p.sigLen⟩, ⟨0x20000, scratchWords p * 8⟩]

/-- A state that satisfies `preparedVerifyContract`'s precondition, with the prepared key in `m`. -/
def pvSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x11000 | .a3 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedPublicKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x11000, p.sigLen⟩]
  wr := [⟨0x20000, scratchWords p * 8⟩]

theorem psSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedSecretKey p m 0x4000) : (signEK p true 1184).pre (psSat p m) := by
  simp only [signEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs, psSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem pvSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedPublicKey p m 0x4000) : (verifyEK p true 1184).pre (pvSat p m) := by
  simp only [verifyEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs, pvSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem secret44_mem : ∃ m, PreparedSecretKey mlDsa44 m 0x4000 :=
  secret_mem prepareSecret44_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public44_mem : ∃ m, PreparedPublicKey mlDsa44 m 0x4000 :=
  public_mem preparePublic44_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign44E true) (signEK mlDsa44 true 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret44_mem; exact ⟨psSat _ m, psSat_pre (.inl rfl) hm⟩)

theorem verifyPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify44E true) (verifyEK mlDsa44 true 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public44_mem; exact ⟨pvSat _ m, pvSat_pre (.inl rfl) hm⟩)

theorem secret65_mem : ∃ m, PreparedSecretKey mlDsa65 m 0x4000 :=
  secret_mem prepareSecret65_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public65_mem : ∃ m, PreparedPublicKey mlDsa65 m 0x4000 :=
  public_mem preparePublic65_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign65E true) (signEK mlDsa65 true 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret65_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inl rfl)) hm⟩)

theorem verifyPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify65E true) (verifyEK mlDsa65 true 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public65_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inl rfl)) hm⟩)

theorem secret87_mem : ∃ m, PreparedSecretKey mlDsa87 m 0x4000 :=
  secret_mem prepareSecret87_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public87_mem : ∃ m, PreparedPublicKey mlDsa87 m 0x4000 :=
  public_mem preparePublic87_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign87E true) (signEK mlDsa87 true 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret87_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inr rfl)) hm⟩)

theorem verifyPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify87E true) (verifyEK mlDsa87 true 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public87_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inr rfl)) hm⟩)

end VG.Proof.MlDsa.RISCV64.PreparedKey

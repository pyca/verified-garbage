module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Entry
import VerifiedGarbage.Proof.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Verified
import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Verified
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.ExpandMask
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.Pro
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.ExpandMask
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.HighLow
meta import VerifiedGarbage.Proof.MlDsa.Round.Ones
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintPack
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.HintCT
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `MlDsa.PPC64LE.Pack.HintPackCT`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Constant time but for the hint, as on AArch64: zeroing `y` leaks only the
pointers and `len` (the taint analysis), and leaves states that agree on
`k`, `ω` and the pointers, and on all the memory the loops may access (the
hint, which the contract lets them leak, and `y`, zeroed); `memTaint`
proves the rest. `omega` is a `u32`, whose register's upper bits the two
runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack.Hint

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem pre_of {s : State} (h : (hintBitPackContract PPC64LE.abi).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.PPC64LE.Taint.T := VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]

theorem ct : ConstantTime isa (hintBitPackContract PPC64LE.abi).pre (hintBitPackContract PPC64LE.abi).pub
    Impl.MlDsa.PPC64LE.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.PPC64LE.Pack.hintBitPack
  refine RelCT.seq (R := MAgree hbpTaint) ?_
    (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.PPC64LE.Taint.ofRegs [.r6, .r7]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : pω x = pω y := by simp only [pω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.rd, fy.rd, px.rd, py.rd]; simp only [hR, pH, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.wr, fy.wr, px.wr, py.wr]; simp only [yR, pY, pLen, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fx.r3, fy.r3]; simp only [pH, p3]
    · rw [fx.r4, fy.r4]; simp only [pk, pLen, p7, hω]
    · rw [fx.r5, fy.r5, hω]
    · rw [fx.r6, fy.r6]; simp only [pY, p6]
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
    | .r3 => 0x1000 | .r4 => 1024 | .r5 => 80 | .r6 => 0x3000 | .r7 => 84 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

end VG.Proof.MlDsa.PPC64LE.Pack.Hint

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.PPC64LE.Pack.Hint

theorem hintBitPack_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.hintBitPack (hintBitPackContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hy, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel), ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hy
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | (rw [hintOnes_zero]; exact Nat.zero_le _)
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Pack

end

end

/-! ### `MlDsa.PPC64LE.Round.MakeHint`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_make_hint`

The selection of `γ₂` (`sel_ok'`), then the loop for it: one symbolic
execution of its body for any pointers (`body_ok`), which stores `r₁` of
`r` to `h[i]`, reads it back and stores whether it differs from `r₁` of
`r + z mod q` (`mhBit`, `mh_val`, through `makeHint_eq`), and adds that to
the count in `r0`. The invariant says which coefficients of `h` are done and
counts their 1s (`onesTo`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Round.MakeHint

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Round
open VG.Impl.MlKem.PPC64LE (fixup)
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm loadQ)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW coeffAt_writeW_disjoint coeffAt_frame
  zipWith_get makeHint_eq mem_gamma2s hbF hbM hintIs_of_toNat onesTo onesTo_succ hintOnes_onesTo reduced_zero)
open VG.Proof.MlDsa.PPC64LE.Round
open VG.Proof.MlDsa.PPC64LE.Round.Bits (dMod_le dMul_lt kgpr selGpr sel_ok' sel_ct consts_ok)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz ptr_succ)

/-! ## Values -/

/-- What the body computes from `a` (of `r`), `b` (of `z`) and `h1` (`r₁`
of `a`, read back): whether `r₁` of `a + b mod q` differs from `h1`. -/
def mhBit (g : Nat) (a b h1 : BitVec 64) : BitVec 64 :=
  ((hbv g (fixk 8380417 (a + b - 8380417)) ^^^ h1) + 63) >>> 6

theorem xor_bit {u v : BitVec 64} (hu : u.toNat < 64) (hv : v.toNat < 64) :
    ((u ^^^ v) + 63) >>> 6 = if u = v then 0 else 1 := by
  have hx : (u ^^^ v).toNat < 64 := by rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 6) hu hv
  split <;> rename_i h
  · subst h; rw [BitVec.xor_self]; decide
  · have : u ^^^ v ≠ 0#64 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    bv_omega

theorem mh_val {g : Nat} (hg : g ∈ gamma2s) {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    mhBit g a b (((hbv g a).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 (decide (hbF g a.toNat % hbM g ≠ hbF g ((a.toNat + b.toNat) % q) % hbM g)).toNat := by
  have ha' := hbv_lt hg ha
  have e1 : ((hbv g a).setWidth 32).setWidth 64 = hbv g a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [ha'])]
  have hs : (fixk 8380417 (a + b - 8380417)).toNat = (a.toNat + b.toNat) % q := by
    rw [VG.Proof.MlDsa.Round.q_eq] at ha hb ⊢
    have := fixk_sub (k := 8380417) (by decide) (by decide) (x := a + b) (by bv_omega)
    rw [show (8380417 : BitVec 64) = BitVec.ofNat 64 8380417 from rfl, this, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega_using [ha, hb] : a.toNat + b.toNat < 2 ^ 64)]
  have hsq : (fixk 8380417 (a + b - 8380417)).toNat < q := by rw [hs]; exact Nat.mod_lt _ (by decide)
  unfold mhBit
  rw [e1, xor_bit (hbv_lt hg hsq) ha']
  have iff : hbv g (fixk 8380417 (a + b - 8380417)) = hbv g a ↔
      hbF g ((a.toNat + b.toNat) % q) % hbM g = hbF g a.toNat % hbM g := by
    rw [BitVec.toNat_eq, hbv_toNat hg hsq, hbv_toNat hg ha, hs]
  by_cases hc : hbF g a.toNat % hbM g = hbF g ((a.toNat + b.toNat) % q) % hbM g
  · rw [ite_eq_left (iff.mpr hc.symm), decide_eq_false (fun h' => h' hc)]; rfl
  · rw [ite_eq_right (fun e => hc (iff.mp e).symm), decide_eq_true hc]; rfl

/-! ## The loop body -/

/-- `r₁` of the coefficient at `y`, as stored. -/
def h1v (g : Nat) (m : Mem) (y : Addr) : BitVec 32 := (hbv g ((m.readW y 32).setWidth 64)).setWidth 32

/-- What an iteration does, for the memory `m1` after the first store and the
bit `v` stored. -/
def Step (s : State) (x y w c : BitVec 64) (m1 : Mem) (v : BitVec 64) (s' : State) : Prop :=
  s'.gpr .r3 = x + 4 ∧ s'.gpr .r4 = y + 4 ∧ s'.gpr .r6 = w + 4 ∧ s'.gpr .r7 = c - 1 ∧
    s'.gpr .r0 = s.gpr .r0 + v ∧ (∀ r ∈ [Reg.r5, .r10, .r11, .r12], s'.gpr r = s.gpr r) ∧
    s'.mem = m1.writeW w (v.setWidth 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {g : Nat} {s : State} {x y w c : BitVec 64} (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y)
  (h6 : s.gpr .r6 = w) (h7 : s.gpr .r7 = c) (h5 : s.gpr .r5 = 8380417)
  (h10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g))
  (ix : InRegions (s.rd ++ s.wr) x 4) (iy : InRegions (s.rd ++ s.wr) y 4) (iw : InRegions (s.rd ++ s.wr) w 4)
  (ow : InRegions s.wr w 4)
include h3 h4 h6 h7 h5 h10 h11 h12 ix iy iw ow

theorem body_ok :
    WP isa (.block (mhBody g)) s (Step s x y w c (s.mem.writeW w (h1v g s.mem y))
      (mhBit g (((s.mem.writeW w (h1v g s.mem y)).readW y 32).setWidth 64)
        (((s.mem.writeW w (h1v g s.mem y)).readW x 32).setWidth 64)
        (((s.mem.writeW w (h1v g s.mem y)).readW w 32).setWidth 64))) := by
  have hS := dShift_lt g
  have hM := dMod_le g
  crun [mhBody, hb, hbRaw, fixup, Step, mhBit, h1v, hbv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12,
    ix, iy, iw, ow, hS, hM, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Z : Addr := s₀.gpr .r3
abbrev Rp : Addr := s₀.gpr .r4
abbrev G : BitVec 32 := (s₀.gpr .r5).setWidth 32
abbrev H : Addr := s₀.gpr .r6

/-- The hint. -/
def hint (g : Nat) : Vector Bool n := Vector.zipWith (makeHint g) (polyAt s₀.mem (Z s₀)) (polyAt s₀.mem (Rp s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Z s₀), pR (Rp s₀)]
  wr : s₀.wr = [pR (H s₀)]
  dz : (pR (Z s₀)).Disjoint (pR (H s₀))
  dr : (pR (Rp s₀)).Disjoint (pR (H s₀))
  fitZ : (Z s₀).toNat + 1024 ≤ 2 ^ 64
  fitR : (Rp s₀).toNat + 1024 ≤ 2 ^ 64
  fitH : (H s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  redZ : Reduced s₀.mem (Z s₀)
  redR : Reduced s₀.mem (Rp s₀)

/-- After `i` iterations. -/
structure Inv (g : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = Z s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .r4 = Rp s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .r6 = H s₀ + BitVec.ofNat 64 (4 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (256 - i)
  r0 : s.gpr .r0 = BitVec.ofNat 64 (onesTo (hint s₀ g) i)
  r5 : s.gpr .r5 = 8380417
  r10 : s.gpr .r10 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (dMod g)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (H s₀) j = BitVec.ofNat 32 (hint s₀ g)[j]!.toNat

theorem bit_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    mhBit g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64) ((coeffAt s₀.mem (Z s₀) i).setWidth 64)
      (((hbv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64)).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 (hint s₀ g)[i]!.toNat := by
  obtain ⟨ea, ha⟩ := HighLow.load_toNat hp.redR hi
  obtain ⟨eb, hb⟩ := HighLow.load_toNat hp.redZ hi
  rw [mh_val hg ha hb, hint, zipWith_get _ _ _ hi, makeHint_eq hg, ea, eb, Nat.add_comm]

theorem inv_step {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv g s₀ i s) :
    WP isa (.block (mhBody g)) s fun s' => Inv g s₀ (i + 1) s' ∧ (s'.gpr .r7 != 0) = decide (i + 1 ≠ 256) := by
  have cZ := coeff_contains (Z s₀) (i := i) hi
  have cR := coeff_contains (Rp s₀) (i := i) hi
  have cH := coeff_contains (H s₀) (i := i) hi
  have hd : ∀ {p : Addr}, (pR p).Disjoint (pR (H s₀)) → ∀ r ∈ [pR (H s₀)], (pR p).Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  -- the reads after the first store, as on entry
  have eR : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i :=
    (coeffAt_writeW_disjoint s.mem hp.dr cH hi _).trans (coeffAt_frame h.frame (hd hp.dr) hi)
  have eZ : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (Z s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Z s₀) i :=
    (coeffAt_writeW_disjoint s.mem hp.dz cH hi _).trans (coeffAt_frame h.frame (hd hp.dz) hi)
  have eH : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (H s₀ + BitVec.ofNat 64 (4 * i)) 32 = (hbv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64)).setWidth 32 := by
    rw [Mem.readW_writeW_self32, h1v, show s.mem.readW (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i
      from coeffAt_frame h.frame (hd hp.dr) hi]
  have hv := bit_val hg hp hi
  rw [← eH, ← eR, ← eZ] at hv
  refine WP.mono (body_ok h.r3 h.r4 h.r6 h.r7 h.r5 h.r10 h.r11 h.r12 ?_ ?_ ?_ ?_)
    fun s' ⟨r3, r4, r6, r7, r0, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_,
      (kp .r5 (by simp)).trans h.r5, (kp .r10 (by simp)).trans h.r10, (kp .r11 (by simp)).trans h.r11,
      (kp .r12 (by simp)).trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cZ⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨pR (H s₀), by simp, cH⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r7]; exact count_sub hi
  · rw [r0, h.r0, hv, onesTo_succ, BitVec.ofNat_add]
  · rw [m]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH).writeW (List.mem_singleton_self _) _ cH
  · intro j hj hji
    rw [m, hv, show H s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (H s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      cases (hint s₀ g)[i]! <;> rfl
    · rw [ite_eq_right e, coeffAt_writeW _ _ hj hi, ite_eq_right e]; exact h.coeff j hj (by omega_using [hji, e])
  · rw [r7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-! ## The function -/

/-- What the function leaves. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    (∀ j < 256, coeffAt s.mem (H s₀) j = BitVec.ofNat 32 (hint s₀ (G s₀).toNat)[j]!.toNat) ∧
    s.gpr .r3 = BitVec.ofNat 64 (onesTo (hint s₀ (G s₀).toNat) 256)

theorem exit_ok {s₀ s : State} {g : Nat} (hG : (G s₀).toNat = g) (h : Inv g s₀ 256 s) :
    WP isa (.block [.logic .or .r3 .r0 .r0]) s (Post s₀) := by
  subst hG
  refine WP.cons exec_logic (wp_nil ⟨?_, h.sp, h.lr, fun j hj => h.coeff j hj hj, ?_⟩)
  · intro r hr
    have : ¬r = .r3 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this]; exact h.pres r hr
  · rw [RegUpd.gpr_write_self, BitVec.or_self]; exact h.r0

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa makeHint s₀ (Post s₀) := by
  refine sel_ok' (rg := .r5) (by decide) hp.g fun g hg hG s hgpr hm hrd hwr hsp hlr => ?_
  have e : (if g = g32 then mhLoop g32 else mhLoop g88) = mhLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e]
  refine WP.seq (consts_ok (WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_li (by decide))
    (WP.cons (exec_li (by decide)) (wp_nil ?_))))))
  refine WP.seq (wp_loop_nz (Inv g s₀) (N := 256) (by decide) (fun i hi s h => inv_step hg hp hi h)
    (fun s h => exit_ok hG h) ?_)
  have e7 := VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val (v := 8380417) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrd, hwr, hsp, hlr, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega_using [])⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write]
  · simp [State.write, onesTo]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e7
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · have : r ≠ .r0 ∧ r ≠ .r5 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.makeHintContract PPC64LE.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem onesTo_le (h : Vector Bool n) (i : Nat) : onesTo h i ≤ i := by
  unfold onesTo
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 95232 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified PPC64LE.target makeHint (Proof.MlDsa.makeHintContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .r5) (by decide) [.r3, .r4, .r6] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, PPC64LE.abi, PPC64LE.argRegs]
    refine ⟨hintIs_of_toNat fun j hj => ?_, ?_⟩
    · rw [h.2.2.2.1 j hj]; rfl
    · rw [h.2.2.2.2, hintOnes_onesTo, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := onesTo_le (hint s (G s).toNat) 256
      rw [Nat.mod_eq_of_lt (by omega_using [this]), Nat.mod_eq_of_lt (by omega_using [this])]
      rfl
  · sig_pub [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, PPC64LE.abi, PPC64LE.argRegs] at h
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
    · sig_reduce [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Round.MakeHint

end

end

/-! ### `MlDsa.PPC64LE.Sample.ExpandMask`, which only this module used -/

section

/-!
# ML-DSA on PPC64LE: `vg_mldsa_expand_mask_poly`

As on 32-bit ARM (`Proof/MlDsa/Arm/Sign/Inst.lean`). The function
runs in pieces: the prologue (`J0`, with `r27` the zero-extended `γ₁`), the
sponge, whose output is `H(ρ′, 640)` (`T`), the branch on `γ₁`, and the loop
of `vg_mldsa_bit_unpack` for `c = 1 + bitlen (γ₁ - 1)` on the first `32c`
bytes of output (`Pack.unpackLoop_buFin_ok`, run from the state permitted
only those bytes and `a`, and widened to the function's permissions by
`WP.narrow`), which are `H(ρ′, 32c)` (`H_take`). It is constant time: the
blocks without memory accesses leak nothing, the sponge by `sponge_ct`, the
branch goes the same way in two runs whose `γ₁` agree, and the loop by
`Pack.unpackLoop_ct18` and `Pack.unpackLoop_ct20`, from the same pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.ExpandMask

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.PPC64LE (relct_noMem)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Impl.MlDsa.PPC64LE.Pack (unpackLoop buFin loadB)
open VG.Proof.MlDsa.PPC64LE.Pack (RB loadBVal loadB_ok Shape loopRegs)
open VG.Spec.MlDsa (Zq q H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt rates)

/-- The call, from the entry state: `seed = r3`, `gamma1 = r4`, `a = r5`,
`scratch = r6`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r3, 66, σ.gpr .r6, σ.gpr .r5⟩

/-- `γ₁`, the low 32 bits of `r4`. -/
abbrev gam (σ : State) : Nat := ((σ.gpr .r4).setWidth 32).toNat

/-- What the function writes, for the call `P`. -/
abbrev Out (P : Sp) (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (P.msg σ) (32 * (1 + bitlen (gam σ - 1)))) (gam σ - 1) (gam σ))

/-- After the sponge. -/
structure T (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

/-- After the branch's block. -/
structure Br (P : Sp) (σ s : State) : Prop where
  t : T P σ s
  r12 : s.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 131072

/-- Before the loop of `BitUnpack` for `b = Bv`. -/
structure L (Bv : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 640 = H (P.msg σ) 640
  r10 : s.gpr .r10 = P.at' 840
  r11 : s.gpr .r11 = P.a
  rb : RB Bv s

/-- After the loop. -/
structure EDone (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : PolyIs s.mem P.a (Out P σ)

theorem zx_eq {x y : BitVec 64} (h : x.setWidth 32 = y.setWidth 32) : zx x = zx y :=
  BitVec.eq_of_toNat_eq (by rw [zx_toNat, zx_toNat, h])

theorem zx_sub_beq (x : BitVec 64) :
    (zx x - BitVec.ofNat 64 131072 == 0) = decide ((x.setWidth 32).toNat = 2 ^ 17) := by
  by_cases h : (x.setWidth 32).toNat = 2 ^ 17
  · have e : zx x = BitVec.ofNat 64 131072 := BitVec.eq_of_toNat_eq (by rw [zx_toNat, h]; rfl)
    rw [e]; simp [h]
  · have e : zx x ≠ BitVec.ofNat 64 131072 := fun e => h (by rw [← zx_toNat, e]; rfl)
    simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e'
    have h2 := congrArg (· + BitVec.ofNat 64 131072) e'
    simp only [BitVec.sub_add_cancel] at h2
    exact e h2

theorem preserved_not_loop : ∀ r ∈ preserved, r ∉ loopRegs := by decide

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The branch's block. -/
theorem br_ok {s : State} (h : T P σ s) :
    WP isa (.block [.lis .r12 2, .sub .r12 .r27 .r12]) s (Br P σ) := by
  have hk : WP isa (.block [.lis .r12 2, .sub .r12 .r27 .r12]) s fun s' =>
      s'.gpr .r12 = s.gpr .r27 - BitVec.ofNat 64 131072 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    have hv : ((2 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 = BitVec.ofNat 64 131072 := by decide
    prun [exec_lis, hv]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g12, gp, m, rd, wr, sp⟩ => ⟨⟨h.env.regs hp m gp rd wr sp, by rw [m]; exact h.out,
    (gp _ (by decide)).trans h.r27⟩, by rw [g12, h.r27]⟩

/-- The loop's setup: the pointers, `q` and `b`. -/
theorem setup_ok {Bv : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv) {s : State} (h : T P σ s) :
    WP isa (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv)) s (L Bv P σ) := by
  have g30 := h.env.r30
  have g31 := h.env.r31
  have hk : WP isa (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++
      Impl.MlDsa.PPC64LE.Pack.loadQ)) s fun s' =>
      s'.gpr .r10 = P.at' 840 ∧ s'.gpr .r11 = P.a ∧ s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [Impl.MlDsa.PPC64LE.Pack.loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30,
      g31]
    simp only [true_and, and_true]
    pres_tac
  rw [WP.block_append_iff]
  refine WP.mono hk fun s₁ ⟨g10, g11, g7, gp, m, rd, wr, sp⟩ => ?_
  refine WP.mono (Pack.WP.withSp (loadB_ok .r4 hl s₁)) fun s' ⟨⟨⟨g4, m'⟩, k⟩, sp'⟩ => ?_
  have m2 : s'.mem = s.mem := m'.trans m
  refine ⟨h.env.regs hp m2 (fun r hr => (k.gpr (by
      rw [List.mem_singleton]; rintro rfl; exact absurd hr (by decide))).trans (gp r hr))
      (k.2.1.trans rd) (k.2.2.trans wr) (sp'.trans sp), by rw [m2]; exact h.out,
    (k.gpr (by decide)).trans g10, (k.gpr (by decide)).trans g11, g4, (k.gpr (by decide)).trans g7⟩

omit hp in
/-- After the sponge, from its output and the zero-extended `γ₁` in `r27`. -/
theorem T.of {s₀ s : State} (h : J6 136 640 P σ s₀ s) (r27 : s₀.gpr .r27 = zx (σ.gpr .r4)) : T P σ s :=
  ⟨h.j0.env, by rw [h.out]; exact (H_eq _ _).symm, (h.gp .r27 (by decide)).trans r27⟩

/-- The loop of `BitUnpack` for `(Bv, d, c, nb)`, from its setup, run on the
first `32 d` bytes of the output and the polynomial `a` alone. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Shape d c nb) (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d)
    (h32 : 32 * d ≤ 640) {s : State} (h : L Bv P σ s) :
    WP isa (unpackLoop buFin d c nb) s fun s' =>
      Env P σ s' ∧ PolyIs s'.mem P.a (toRq (bitUnpack (H (P.msg σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  have ewr : s.wr = [P.aR, P.scrR] := h.env.wr.trans hp.wr
  refine WP.narrow (rd := [⟨s.gpr .r10, 32 * d⟩]) (wr := [⟨s.gpr .r11, 1024⟩])
    (Pack.unpackLoop_buFin_ok (a := Bv - 1) hs hB19 hd h.rb (List.mem_append_left _ (List.mem_singleton_self _))
      (List.mem_singleton_self _) ?_) ?_ ?_ (fun s' rd' wr' sp' hf hq => ?_) (by unfold unpackLoop; rfl)
  · show Region.Disjoint ⟨s.gpr .r10, 32 * d⟩ ⟨s.gpr .r11, 1024⟩
    rw [h.r10, h.r11]
    exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 32 * d) (by omega_using [h32]))).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨P.scrR, List.mem_append_right _ (by rw [ewr]; simp), 840, h.r10, by show 840 + 32 * d ≤ 2048; omega_using [h32]⟩
    · exact ⟨P.aR, List.mem_append_right _ (by rw [ewr]; simp), 0, by rw [h.r11]; exact (BitVec.add_zero _).symm,
        by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨P.aR, by rw [ewr]; simp, 0, by rw [h.r11]; exact (BitVec.add_zero _).symm, by simp⟩
  obtain ⟨hpoly, -, hk⟩ := hq
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => hk.1 r (preserved_not_loop r hr)
  refine ⟨h.env.step hp (rs := [P.aR]) (by rw [h.r11] at hf; exact hf) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h)) gp rd' wr' sp', ?_⟩
  have eb : bytesAt s.mem (P.at' 840) (32 * d) = H (P.msg σ) (32 * d) := by
    rw [← MlKem.bytesAt_take _ _ h32, h.out, H_take _ h32]
  simp only [State.withRegions_mem, State.withRegions_gpr] at hpoly
  rw [h.r11, h.r10, eb] at hpoly
  exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) {s : State} (h : T P σ s) :
    WP isa (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20))) s
      (EDone P σ) := by
  refine WP.seq (WP.mono (br_ok hp h) fun s1 h1 => ?_)
  refine WP.ite (M := isa) (decide (gam σ = 2 ^ 17)) (by rw [eval_zero, h1.r12, zx_sub_beq]) (fun e => ?_)
    (fun e => ?_)
  · have hγ : gam σ = 2 ^ 17 := of_decide_eq_true e
    show WP isa (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 131072)) (unpackLoop buFin 18 4 9)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 131072) (by decide) h1.t) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo
  · have hγ : gam σ = 2 ^ 19 := by have := of_decide_eq_false e; omega_using [hg, this]
    show WP isa (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 524288)) (unpackLoop buFin 20 2 5)) s1 _
    refine WP.seq (WP.mono (setup_ok hp (Bv := 524288) (by decide) h1.t) fun s2 h2 => ?_)
    refine WP.mono (loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide)
      (by decide) (by decide) h2) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo

/-- The function, from an entry state whose regions are those of the call `P`. -/
theorem correct (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) (h3 : σ.gpr .r3 = P.sd) (h5 : σ.gpr .r5 = P.a)
    (h6 : σ.gpr .r6 = P.scr) (hlen : P.len = 66) :
    WP isa Impl.MlDsa.PPC64LE.Sample.expandMask σ fun s' => PolyIs s'.mem P.a (Out P σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rb hp h3 h5 h6 hlen) fun _ ⟨j1, r27⟩ =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 640) (by decide) (by decide) j1) fun _ h2 =>
      WP.seq (WP.mono (tail_ok hp hg (T.of h2 r27)) fun _ h3 =>
        WP.mono (epi_ok hp h3.env) fun _ ⟨ha, hm, _⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

end

/-! ## Constant time -/

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The setup and the loop of one branch. -/
theorem em_ct {Bv d c nb : Nat} (hl : loadBVal Bv = BitVec.ofNat 64 Bv)
    (hnm : ((([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv).all VG.Proof.MlKem.PPC64LE.noMem) = true)
    (hloop : ∀ {Q : State → State → Prop},
      (∀ a b, Q a b → a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11) →
      RelCT isa Q (unpackLoop buFin d c nb) fun _ _ => True)
    {R : State → State → Prop} (hR : ∀ a b, R a b → T P σ₁ a ∧ T P σ₂ b) :
    RelCT isa R (.seq (.block (([.addi .r10 .r31 840, mov .r11 .r30] : List Instr) ++ Impl.MlDsa.PPC64LE.Pack.loadQ ++
      loadB .r4 Bv)) (unpackLoop buFin d c nb)) fun _ _ => True :=
  RelCT.seq (R := fun a b => L Bv P σ₁ a ∧ L Bv P σ₂ b)
    (relct_wp (relct_noMem hnm) fun a b hab => ⟨setup_ok hp₁ hl (hR a b hab).1, setup_ok hp₂ hl (hR a b hab).2⟩)
    (hloop fun a b hab => ⟨by rw [hab.1.env.sp, hab.2.env.sp, hsp], by rw [hab.1.r10, hab.2.r10],
      by rw [hab.1.r11, hab.2.r11]⟩)

/-- The branch on `γ₁` and the loop, from runs whose `γ₁` agree. -/
theorem tail_ct (hg : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32) :
    RelCT isa (fun a b => T P σ₁ a ∧ T P σ₂ b)
      (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20)))
      fun _ _ => True := by
  refine RelCT.seq (R := fun a b => Br P σ₁ a ∧ Br P σ₂ b)
    (relct_wp (relct_noMem rfl) fun a b hab => ⟨br_ok hp₁ hab.1, br_ok hp₂ hab.2⟩) ?_
  refine RelCT.ite (fun a b hab => by rw [eval_zero, eval_zero, hab.1.r12, hab.2.r12, zx_eq hg]) ?_ ?_
  · exact em_ct hp₁ hp₂ hsp (Bv := 131072) (by decide) rfl (fun hQ => Pack.unpackLoop_ct18 hQ)
      fun a b hab => ⟨hab.1.1.t, hab.1.2.t⟩
  · exact em_ct hp₁ hp₂ hsp (Bv := 524288) (by decide) rfl (fun hQ => Pack.unpackLoop_ct20 hQ)
      fun a b hab => ⟨hab.1.1.t, hab.1.2.t⟩

end

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : SpOk (spOf σ₁) σ₁
  p₂ : SpOk (spOf σ₂) σ₂
  g₁ : gam σ₁ = 2 ^ 17 ∨ gam σ₁ = 2 ^ 19
  g₂ : gam σ₂ = 2 ^ 17 ∨ gam σ₂ = 2 ^ 19
  sp : σ₁.sp = σ₂.sp
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  r4 : (σ₁.gpr .r4).setWidth 32 = (σ₂.gpr .r4).setWidth 32
  r5 : σ₁.gpr .r5 = σ₂.gpr .r5
  r6 : σ₁.gpr .r6 = σ₂.gpr .r6

theorem all_ct {σ₁ σ₂ : State} (h : Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.PPC64LE.Sample.expandMask fun _ _ => True := by
  have eP : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r3, h.r5, h.r6]
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ h.p₂
  refine RelCT.seq (R := fun (a b : State) => (J0 (spOf σ₁) σ₁ a ∧ a.gpr .r27 = zx (σ₁.gpr .r4)) ∧
      (J0 (spOf σ₁) σ₂ b ∧ b.gpr .r27 = zx (σ₂.gpr .r4)))
    (relct_wp (pro_rb_ct (fun a b hab => by rw [hab.1, hab.2]; exact h.sp)
      fun a b hab => by rw [hab.1, hab.2]; exact h.r6) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact pro_rb h.p₁ rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rb hp₂' h.r3.symm h.r5.symm h.r6.symm rfl
  refine RelCT.seq (R := fun a b => T (spOf σ₁) σ₁ a ∧ T (spOf σ₁) σ₂ b)
    (relct_wp ((sponge_ct h.p₁ hp₂' h.sp (rate := 136) (outlen := 640) (by decide) (by decide)).mono
      (fun a b hab => ⟨hab.1.1, hab.2.1⟩) fun _ _ x => x) fun a b hab =>
      ⟨WP.mono (sponge_ok h.p₁ (by decide) (by decide) hab.1.1) fun _ x => T.of x hab.1.2,
        WP.mono (sponge_ok hp₂' (by decide) (by decide) hab.2.1) fun _ x => T.of x hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => EDone (spOf σ₁) σ₁ a ∧ EDone (spOf σ₁) σ₂ b)
    (relct_wp (tail_ct h.p₁ hp₂' h.sp h.r4) fun a b hab => ⟨tail_ok h.p₁ h.g₁ hab.1, tail_ok hp₂' h.g₂ hab.2⟩) ?_
  exact epi_ct (fun a b hab => by rw [hab.1.env.sp, hab.2.env.sp, h.sp])
    fun a b hab => by rw [hab.1.env.r31, hab.2.env.r31]

/-! ## `Verified` -/

theorem pre_of {s : State} (h : (Proof.MlDsa.expandMaskContract PPC64LE.abi 48).pre s) :
    SpOk (spOf s) s ∧ (gam s = 2 ^ 17 ∨ gam s = 2 ^ 19) := by
  sig_pre [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hg⟩ := h
  exact ⟨⟨by rw [h1]; exact List.mem_singleton_self _, h2, h3, h4, h5, h6, h7, h8,
    show (66 : Nat) < 2 ^ 64 by decide, h10, h11, h0⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x20000 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.PPC64LE.Sample.ExpandMask

namespace VG.Proof.MlDsa.PPC64LE.Sample

open VG VG.PPC64LE
open ExpandMask

theorem expandMask_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Sample.expandMask (Proof.MlDsa.expandMaskContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨hp, hg⟩ := pre_of hs
    obtain ⟨t, s', he, hpoly, ha⟩ := correct hp hg rfl rfl rfl rfl
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpoly
  · sig_pub [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, h3, h4, h5, h6⟩ := hpub
    obtain ⟨p₁, g₁⟩ := pre_of h₁
    obtain ⟨p₂, g₂⟩ := pre_of h₂
    exact (all_ct ⟨p₁, p₂, g₁, g₂, hsp, h3, h4, h5, h6⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Sample

end

end

/-!
# ML-DSA signing on PPC64LE, with this library's primitives

The PPC64LE implementations of the primitives (`prims`) are verified with at
most 96 bytes of stack, and their frames use no more; with the 48 bytes they
are verified with, the two samplers whose results signing branches on return
what depends only on their public data, and succeed only if their algorithm
finishes within `maxBounds` (`rn_ret`, `sb_ret`, from what their own proofs
say they return). So the kernels with them are verified with 96, and the 96
of their own frames (`withCache44_verified`, …), and the entries calling
them with 48 more (`sign44_verified`, `signPrepared44_verified`, …): the
precondition of a prepared key's holds of the memory its preparation writes
(`PreparedKey.secret_mem`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sign

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Sign
open VG.Proof.MlDsa.Sign (ifn rejNTTPoly_mono sampleInBall_mono)
open VG.Proof.MlDsa.Sample (rnFold ballFold rejNTT_some sampleInBall_some)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The samplers' results -/

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract PPC64LE.abi 48).pre s)
    (e : Exec isa Impl.MlDsa.PPC64LE.Sample.rejNTT s tr s') :
    s'.gpr .r3 = if (Sample.RejNtt.Lr s).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.RejNtt.correct (Sample.RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract PPC64LE.abi 48).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .r3) 34 = bytesAt s₂.mem (s₂.gpr .r3) 34 := by
  sig_pub [rejNTTContract, rejNTTSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract PPC64LE.abi 48).pre s)
    (e : Exec isa Impl.MlDsa.PPC64LE.Sample.sampleInBall s tr s') :
    s'.gpr .r3 = if (ballFold ((s.gpr .r5).setWidth 32).toNat
      (H (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Sample.Ball.correct (Sample.Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract PPC64LE.abi 48).pub s₁ s₂) :
    (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32 ∧
      bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat = bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat := by
  sig_pub [sampleInBallContract, sampleInBallSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨_, hb, _, _, h5, _⟩ := h
  exact ⟨h5, Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem zero_ne_one32 : (BitVec.setWidth 32 (0 : BitVec 64)) ≠ 1 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_ok : SPrimsOk prims 96 where
  ntt := ⟨⟨96, by decide, VNtt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨96, by decide, VNtt.iverified⟩, by decide +kernel⟩
  mul := ⟨⟨0, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨0, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNTT := ⟨⟨48, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  expandMask := ⟨⟨48, by decide, Sample.expandMask_verified⟩, by decide +kernel⟩
  ball := ⟨⟨48, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  highBits := ⟨⟨0, by decide, Round.HighLow.high_verified⟩, by decide +kernel⟩
  lowBits := ⟨⟨0, by decide, Round.HighLow.low_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨0, by decide, Round.NormLt.verified⟩, by decide +kernel⟩
  makeHint := ⟨⟨0, by decide, Round.MakeHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨0, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨0, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  hintBitPack := ⟨⟨0, by decide, Pack.hintBitPack_verified⟩, by decide +kernel⟩
  rejX := ⟨48, by decide, Sample.rejNTT_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by
          rw [rn_ret h₁ e₁, rn_ret h₂ e₂]
          simp only [Sample.RejNtt.Lr, Sample.RejNtt.X, Sample.RejNtt.B, rn_pub s₁ s₂ hp]⟩,
    fun s t s' h e h1 => by
      rw [rn_ret h e] at h1
      simp only [Sample.RejNtt.Lr, Sample.RejNtt.X, Sample.RejNtt.B] at h1
      by_cases h0 : (rnFold [] (G (bytesAt s.mem (s.gpr .r3) 34) (3 * 280))).length = 256
      · rw [rejNTTPoly_mono (show 3 * 280 ≤ maxBounds.rejNTT by decide) (rejNTT_some h0)]; rfl
      rw [ifn h0] at h1
      by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .r3) 34) (3 * 336))).length = 256
      · rw [rejNTTPoly_mono (show 3 * 336 ≤ maxBounds.rejNTT by decide) (rejNTT_some hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩
  ballX := ⟨48, by decide, Sample.sampleInBall_verified,
    fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
      ⟨Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
        show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩,
    fun s t s' h e h1 => by
      rw [sb_ret h e] at h1
      by_cases hf : (ballFold ((s.gpr .r5).setWidth 32).toNat
        (H (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 272)).2 = 256
      · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some _ (by decide) hf)]; rfl
      · rw [ifn hf] at h1; exact absurd h1 zero_ne_one32⟩

theorem withCache44_sat : (Proof.MlDsa.signWithCacheContract mlDsa44 PPC64LE.abi (96 + 96)).pre (kSat mlDsa44) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache44_verified :
    Verified PPC64LE.target withCache44 (Proof.MlDsa.signWithCacheContract mlDsa44 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inl rfl) (by decide +kernel) withCache44_sat

theorem withCache65_sat : (Proof.MlDsa.signWithCacheContract mlDsa65 PPC64LE.abi (96 + 96)).pre (kSat mlDsa65) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache65_verified :
    Verified PPC64LE.target withCache65 (Proof.MlDsa.signWithCacheContract mlDsa65 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inr (.inl rfl)) (by decide +kernel) withCache65_sat

theorem withCache87_sat : (Proof.MlDsa.signWithCacheContract mlDsa87 PPC64LE.abi (96 + 96)).pre (kSat mlDsa87) := by
  sig_pre [Proof.MlDsa.signWithCacheContract, Proof.MlDsa.signWithCacheSig, signSig, PPC64LE.abi,
    PPC64LE.argRegs]
  sig_and_intros
  all_goals first
    | exact .inl rfl
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem withCache87_verified :
    Verified PPC64LE.target withCache87 (Proof.MlDsa.signWithCacheContract mlDsa87 PPC64LE.abi (96 + 96)) :=
  withCache_verified prims_ok (by decide) _ (.inr (.inr rfl)) (by decide +kernel) withCache87_sat

/-! ## The entries -/

/-- A state that satisfies `preparedSignContract`'s precondition, with the
memory `m`, a prepared private key at `0x10000`. -/
def psSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x8000 | .r5 => 0x9000 | .r6 => 0xA000 | .r7 => 0x20000 | _ => 0
  lr := 0
  sp := 0x100000
  mem := m
  rd := [⟨0x10000, preparedSecretKeyBytes p⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x20000, KeyGen.scrLen p⟩]

theorem prepared_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (Proof.MlDsa.preparedSignContract p PPC64LE.abi (191 + 1 + 48)).pre s := by
  obtain ⟨m, hm⟩ := PreparedKey.secret_mem hp3
  refine ⟨psSat p m, ?_⟩
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, PPC64LE.abi, PPC64LE.argRegs, psSat]
    sig_and_intros
    all_goals first
      | exact hm
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem sign_sat {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    ∃ s, (signContract p PPC64LE.abi (191 + 1 + 48)).pre s := by
  refine ⟨signSat p, ?_⟩
  rcases hp3 with rfl | rfl | rfl
  all_goals sig_sat_check [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs, signSat]

theorem sign44_verified : Verified PPC64LE.target sign44 (signContract mlDsa44 PPC64LE.abi 240) :=
  sign_entry_verified withCache44_verified (by decide +kernel) (by decide) (sign_sat (.inl rfl))
theorem sign65_verified : Verified PPC64LE.target sign65 (signContract mlDsa65 PPC64LE.abi 240) :=
  sign_entry_verified withCache65_verified (by decide +kernel) (by decide) (sign_sat (.inr (.inl rfl)))
theorem sign87_verified : Verified PPC64LE.target sign87 (signContract mlDsa87 PPC64LE.abi 240) :=
  sign_entry_verified withCache87_verified (by decide +kernel) (by decide) (sign_sat (.inr (.inr rfl)))

theorem signPrepared44_verified :
    Verified PPC64LE.target signPrepared44 (Proof.MlDsa.preparedSignContract mlDsa44 PPC64LE.abi 240) :=
  prepared_entry_verified withCache44_verified (by decide +kernel) (by decide) (.inl rfl) (prepared_sat (.inl rfl))
theorem signPrepared65_verified :
    Verified PPC64LE.target signPrepared65 (Proof.MlDsa.preparedSignContract mlDsa65 PPC64LE.abi 240) :=
  prepared_entry_verified withCache65_verified (by decide +kernel) (by decide) (.inr (.inl rfl))
    (prepared_sat (.inr (.inl rfl)))
theorem signPrepared87_verified :
    Verified PPC64LE.target signPrepared87 (Proof.MlDsa.preparedSignContract mlDsa87 PPC64LE.abi 240) :=
  prepared_entry_verified withCache87_verified (by decide +kernel) (by decide) (.inr (.inr rfl))
    (prepared_sat (.inr (.inr rfl)))

end VG.Proof.MlDsa.PPC64LE.Sign

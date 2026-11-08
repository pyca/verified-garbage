module

import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKey
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCT
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKey
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCT
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
meta import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed448.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ed448_public_key` on PPC64LE, verified

The code meets `publicKeyContract` with the frame as one more argument
(`Sig.scratchContract`), and 48 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`pkC`), which it implies, and
a state satisfying it; and, in a frame of 192 bytes whose first 120 it zeroes
before returning (`Verified.stackScratchWiped`), the contract itself. Only
the pointers are public: they stay in `r20`–`r23`, which no function called
writes, so the taint analysis (`taint_decide`) sees them public throughout,
callees included.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Spec.Ed448 (bytesAt)
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs)
open VG.Proof.Ed25519.PPC64LE.Whole (slotArea)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)
open VG.Proof.X25519.PPC64LE

/-- The contract by register: `out` in `r3`, `seed` in `r4`, `scratch` in `r5`, the frame in `r6`. -/
def pkC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let seed : Region := ⟨s.gpr .r4, 57⟩
    let sc : Region := ⟨s.gpr .r5, 8192⟩
    let fr : Region := ⟨s.gpr .r6, 160⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint seed ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .r3) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .r4) 57)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem pk_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := publicKey_wp hl ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

/-- The setup: the registers saved and the arguments moved, from which the
hash runs. -/
private theorem pk_setup {s : State} (hp : PkPre s) :
    WP isa (.block (saveRegs .r6 120 pkRegs ++ [mov .r21 .r3, mov .r22 .r4, mov .r23 .r5, mov .r24 .r6])) s
      fun t => PkInv s t ∧ HashOk .r23 .r24 0 [⟨.r22, 0, .imm 57⟩] t := by
  have hFw : (⟨s.gpr .r6, 160⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hCw : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hsS : Region.Sub (slotArea (s.gpr .r6) 120 pkRegs) ⟨s.gpr .r6, 160⟩ := Offset.sub_base _ (by decide)
  have F0 : s.gpr .r6 + BitVec.ofNat 64 0 = s.gpr .r6 := BitVec.add_zero _
  have hF114 : Region.Sub ⟨s.gpr .r6, 114⟩ ⟨s.gpr .r6, 160⟩ := Region.sub_prefix (by decide)
  refine WP.mono (show WP isa (.block (saveRegs .r6 120 pkRegs ++
      ([(.r21, .r3), (.r22, .r4), (.r23, .r5), (.r24, .r6)] : List (Reg × Reg)).map (fun p => mov p.1 p.2) ++ []))
      s (PkInv s) from setup_ok (by decide) (by decide) (by decide)
        (fun p hp' => in_base hFw (by revert p; decide) (by revert p; decide)) ⟨_, by simp, hsS⟩ rfl
        (by decide) (by decide) (fun p hp' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl | rfl | rfl <;> rfl) fun u hu => WP.block_nil hu) fun t₁ h₁ => ⟨h₁, ?_⟩
  have g22x : t₁.gpr .r22 = s.gpr .r4 := h₁.regs _ (by decide)
  have g23x : t₁.gpr .r23 = s.gpr .r5 := h₁.regs _ (by decide)
  have g24x : t₁.gpr .r24 = s.gpr .r6 := h₁.regs _ (by decide)
  have e₁ : KEnv (s.gpr .r5) t₁ := ⟨by rw [h₁.wr]; exact hCw, by rw [h₁.sp]; exact hp.sp, by rw [h₁.sp]; exact hp.bC⟩
  have pR : Piece.R t₁.gpr ⟨.r22, 0, .imm 57⟩ = ⟨s.gpr .r4, 57⟩ := by
    simp only [Piece.R, Piece.addr, Len.val, g22x, BitVec.add_zero]
  have pk : PieceOk (s.gpr .r5) t₁ ⟨.r22, 0, .imm 57⟩ :=
    ⟨by decide, by decide, show 57 < 2 ^ 15 by decide, by
      rw [pR, h₁.rd, hp.rd]; exact fun a n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      by rw [pR]; exact hp.sC, by rw [pR, h₁.sp]; exact hp.bS⟩
  have hwF : PPC64LE.Covers [⟨s.gpr .r6, 114⟩] t₁.wr := by
    rw [h₁.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hFw, 0, by simp, by simp⟩
  exact ⟨by decide, by decide, by decide, by simp, by rw [g23x]; exact e₁,
    fun p hp' => by rw [List.mem_singleton.mp hp', g23x]; exact pk, by rw [g24x, F0]; exact hwF,
    by rw [g24x, F0, g23x]; exact hp.cF.symm.sub_left hF114,
    by rw [g24x, F0, h₁.sp]; exact hp.bF.sub_right hF114⟩

private theorem pkPre_of {s : State} (h : pkC.pre s) : PkPre s := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩

private theorem pk_hashRegs : ∀ r ∈ hashRegs .r23 .r24 [⟨.r22, 0, .imm 57⟩], r ∈ pkRegs := by decide

/-- Constant time: the setup by the taint analysis, then the hash (`hash_then`,
which relates the runs through the sponge functions' constant time and the
registers they keep), then the rest by the taint analysis from `r21`–`r24`. -/
theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧
      (pkC.pre x.1 ∧ pkC.pre x.2 ∧ pkC.pub x.1 x.2))
    (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : pkC.pre s₁ ∧ pkC.pre s₂ ∧ pkC.pub s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨h₁, h₂, p3, p4, p5, p6, psp⟩ := hH
  have q₁ := pkPre_of h₁
  have q₂ := pkPre_of h₂
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have hv : ∀ r ∈ pkRegs, pkV s₁ r = pkV s₂ r := by
    intro r hr
    simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [p3, p4, p5, p6]
  unfold publicKey
  refine RelCT.seq (R := fun a b => (PkInv s₁ a ∧ HashOk .r23 .r24 0 [⟨.r22, 0, .imm 57⟩] a) ∧
      (PkInv s₂ b ∧ HashOk .r23 .r24 0 [⟨.r22, 0, .imm 57⟩] b))
    (relct_wp (taint_block [.r3, .r4, .r5, .r6] (fun a b hab => by rw [hab.1, hab.2]; exact psp)
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [p3, p4, p5, p6]) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact pk_setup q₁, by rw [hab.2]; exact pk_setup q₂⟩) ?_
  exact hash_then (by taint_decide) (fun a b h => ⟨h.1.2, h.2.2, by rw [h.1.1.sp, h.2.1.sp, psp],
      fun r hr => by rw [h.1.1.regs r (pk_hashRegs r hr), h.2.1.regs r (pk_hashRegs r hr), hv r (pk_hashRegs r hr)]⟩)
    pkRegs (fun a b h r hr => ⟨pkRegs_pres r hr, by rw [h.1.1.regs r hr, h.2.1.regs r hr, hv r hr]⟩)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 160⟩]

theorem publicKey_verified (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target publicKey (Sig.scratchContract PPC64LE.abi Spec.Ed448.publicKeySig "frame" .u8 160
      (Curry.const (fun _ => True) _) (Proof.Ed448.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (pk_ok hl) pk_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.publicKeyPost, pkC, PPC64LE.abi, PPC64LE.argRegs]
      [pkSat] using pkSat)

/-- A state satisfying `vg_ed448_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed448.publicKeyContract PPC64LE.abi (48 + 192)).pre s := by
  implies_sat [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 192 bytes, whose first 120 it zeroes before returning. -/
theorem publicKey_framed (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target publicKeyCode (Spec.Ed448.publicKeyContract PPC64LE.abi (48 + 192)) :=
  Verified.stackScratchWiped (sig := Spec.Ed448.publicKeySig) (nm := "frame") (e := .u8) (n := 160)
    (post := Proof.Ed448.WholeLocal.publicKeyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 192)
    (words := 15) (publicKey_verified hl) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Ed448.WholeLocal.publicKeyPost_local _)
    (Proof.Ed448.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed448.PPC64LE.Whole

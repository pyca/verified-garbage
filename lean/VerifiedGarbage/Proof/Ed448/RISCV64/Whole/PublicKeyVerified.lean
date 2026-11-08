module

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKey
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.PublicKey
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed448.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa

import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.HashCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Offset
/-!
# `vg_ed448_public_key` on RISC-V, verified

The code meets `publicKeyContract` with the frame (20 doublewords, so
aligned as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`), and 1168 bytes of stack for the callees' frames:
the proof against the contract's facts by register (`pkC`), which it
implies, and a state satisfying it; and, in a frame of 160 bytes whose first
120 it zeroes before returning (`Verified.stackScratchWiped`), the contract
itself. Only the pointers are public. The hash is related through its
constant-time and register-preservation proofs; the surrounding blocks are
checked by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64.Whole
open VG.Spec.Ed448 (bytesAt)

/-- The contract by register: `out` in `a0`, `seed` in `a1`, `scratch` in `a2`, the frame in `a3`. -/
def pkC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let seed : Region := ⟨s.gpr .a1, 57⟩
    let sc : Region := ⟨s.gpr .a2, 8192⟩
    let fr : Region := ⟨s.gpr .a3, 160⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧
      (below s.sp 1168).Disjoint out ∧ (below s.sp 1168).Disjoint seed ∧ (below s.sp 1168).Disjoint sc ∧
      (below s.sp 1168).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .a0) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .a1) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

theorem pk_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := publicKey_wp hl ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

private theorem pk_pre {s : State} (h : pkC.pre s) : PkPre s := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

private theorem pk_hashOk {s t : State} (hp : PkPre s) (h : PkInv s t) :
    HashOk .s9 .s10 0 [⟨.s8, 0, .imm 57⟩] t := by
  have h8 : t.gpr .s8 = s.gpr .a1 := h.regs _ (by decide)
  have h9 : t.gpr .s9 = s.gpr .a2 := h.regs _ (by decide)
  have h10 : t.gpr .s10 = s.gpr .a3 := h.regs _ (by decide)
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, by rw [h9]; exact hp.alC, by rw [h.sp]; exact hp.spal,
      by rw [h.sp]; exact hp.sp, ?_⟩
    · rw [h9, h.wr, hp.wr]; simp
    · rw [h9, h.sp]; exact hp.bC
  · intro p hp'
    simp only [List.mem_singleton] at hp'; subst p
    have hR : Piece.R t.gpr ⟨.s8, 0, .imm 57⟩ = ⟨s.gpr .a1, 57⟩ := by
      simp only [Piece.R, Piece.addr, Len.val, h8, BitVec.add_zero]
    exact ⟨by decide, by decide, (by change 57 < 2048; decide),
      by rw [hR, h.rd, hp.rd]; exact Covers.left (Covers.refl _),
      by rw [hR, h9]; exact hp.sC, by rw [hR, h.sp]; exact hp.bS⟩
  · rw [h10, BitVec.add_zero, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨⟨s.gpr .a3, 160⟩, by simp, 0, by simp, by change 0 + 114 ≤ 160; decide⟩
  · rw [h9, h10, BitVec.add_zero]
    exact hp.cF.symm.sub_left (Region.sub_prefix (by decide))
  · rw [h.sp, h10, BitVec.add_zero]
    exact hp.bF.sub_right (Region.sub_prefix (by decide))

theorem pk_ct : ConstantTime isa pkC.pre pkC.pub publicKey := by
  intro a b t u a' b' pa pb hpub e₁ e₂
  have ha := pk_pre pa
  have hb := pk_pre pb
  obtain ⟨p0, p1, p2, p3, psp⟩ := hpub
  have hv : ∀ r ∈ pkRegs, pkV a r = pkV b r := by
    intro r hr
    simp only [pkRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [p0, p1, p2, p3]
  have heq : ∀ x y, PkInv a x ∧ PkInv b y → ∀ r ∈ pkRegs, x.gpr r = y.gpr r := by
    intro x y h r hr
    rw [h.1.regs r hr, h.2.regs r hr]
    exact hv r hr
  have hs : RelCT isa (fun x y => x = a ∧ y = b)
      (.block (VG.Impl.Ed25519.RISCV64.Whole.saveRegs .a3 120 pkRegs ++
        [VG.Impl.Ed25519.RISCV64.Whole.mov .s7 .a0, VG.Impl.Ed25519.RISCV64.Whole.mov .s8 .a1,
         VG.Impl.Ed25519.RISCV64.Whole.mov .s9 .a2, VG.Impl.Ed25519.RISCV64.Whole.mov .s10 .a3]))
      (fun x y => PkInv a x ∧ PkInv b y) := by
    refine (relct_wp (ct_prog [.a0, .a1, .a2, .a3] ?_ ?_ (by taint_decide)) ?_).mono
      (fun _ _ h => h) (fun _ _ h => h)
    · intro x y ⟨rfl, rfl⟩; exact psp
    · intro x y ⟨rfl, rfl⟩ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [p0, p1, p2, p3]
    · intro x y ⟨rfl, rfl⟩; exact ⟨publicKey_setup ha, publicKey_setup hb⟩
  have hr : RelCT isa (fun x y => PkInv a x ∧ PkInv b y)
      (.seq (hash .s9 [⟨.s8, 0, .imm 57⟩] .s10 0)
        (.seq (.block (prune .s10 0 ++ [VG.Impl.Ed25519.RISCV64.Whole.mov .a0 .s7,
            .addi .a1 .s10 0, VG.Impl.Ed25519.RISCV64.Whole.mov .a2 .s9]))
          (.seq (.call "vg_ed448_scalar_base" Impl.Ed448.RISCV64.scalarBase)
            (.block (VG.Impl.Ed25519.RISCV64.Whole.restoreRegs .s10 120 pkRegs))))) (fun _ _ => True) := by
    refine hash_then (by taint_decide) ?_ pkRegs ?_ (by taint_decide)
    · intro x y h
      refine ⟨pk_hashOk ha h.1, pk_hashOk hb h.2, h.1.sp.trans (psp.trans h.2.sp.symm), fun r hr => ?_⟩
      exact heq x y h r ((by decide : ∀ r ∈ hashRegs .s9 .s10 [⟨.s8, 0, .imm 57⟩], r ∈ pkRegs) r hr)
    · intro x y h r hr
      exact ⟨pkRegs_pres r hr, heq x y h r hr⟩
  exact (RelCT.seq hs hr _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 160⟩]

theorem publicKey_verified (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified RISCV64.target publicKey (Sig.scratchContract RISCV64.abi Spec.Ed448.publicKeySig "frame" .u64 20
      (Curry.const (fun _ => True) _) (Proof.Ed448.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 1168) :=
  Verified.of_correct (pk_ok hl) pk_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.publicKeyPost, pkC, RISCV64.abi, RISCV64.argRegs]
      [pkSat] using pkSat)

/-- A state satisfying `vg_ed448_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSat with wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed448.publicKeyContract RISCV64.abi (1168 + 160)).pre s := by
  implies_sat [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig, Spec.Ed448.scratchWords, RISCV64.abi,
    RISCV64.argRegs] [pkFrameSat, pkSat] using pkFrameSat

/-- In its frame of 160 bytes, whose first 120 it zeroes before returning. -/
theorem publicKey_framed (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified RISCV64.target publicKeyCode (Spec.Ed448.publicKeyContract RISCV64.abi (1168 + 160)) :=
  Verified.stackScratchWiped (sig := Spec.Ed448.publicKeySig) (nm := "frame") (e := .u64) (n := 20)
    (post := Proof.Ed448.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) (wa := true) (stack := 1168) (bytes := 160)
    (words := 15) (publicKey_verified hl) (by decide) (by decide) (by decide)
    (Proof.Ed448.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed448.RISCV64.Whole

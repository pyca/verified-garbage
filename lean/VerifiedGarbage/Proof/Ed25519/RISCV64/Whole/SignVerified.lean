module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ByRegister
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyVerified
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# `vg_ed25519_sign_cached` on RISC-V, verified

The code meets `signCachedContract` with the frame (36 doublewords, so
aligned as the contract's `u64` buffers are) as one more argument
(`Sig.scratchContract`) and 208 bytes of stack for the callees' frames: the
proof against the contract's facts by register (`signC`), which it implies,
and a state satisfying it. In a frame of 288 bytes on the stack whose first
224 it zeroes before returning (`Verified.stackScratchWipedC`), it meets the
contract itself. The comb's table is the static `combConsts` (`abi.withConsts`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combWords combConsts)
open VG.Proof.Ed25519.RISCV64 (combWords_length)

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def signSat (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x2100 | .a3 => 0x3000 | .a5 => 0x4000 | .a6 => 0x8000 | _ => 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 32⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩]

theorem signR_implies : signR.Implies (Sig.scratchContract RISCV64.abi Spec.Ed25519.signCachedSig "frame" .u64 36
    (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, RISCV64.abi, RISCV64.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, RISCV64.abi, RISCV64.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, RISCV64.abi, RISCV64.argRegs]
      sat := by
        obtain ⟨m, hm⟩ : ∃ m : Mem, bytesAt m 0x2100 32 = Spec.Ed25519.publicKey (bytesAt m 0x2000 32) :=
          ⟨_, Proof.Ed25519.WholeLocal.sat_pk⟩
        refine ⟨signSat m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          RISCV64.abi, RISCV64.argRegs, signSat]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- The seed and public key of `satMem` below `0x100000`, the comb's table above. -/
@[irreducible] def signMem : Mem := fun a => if a.toNat < 0x100000 then Proof.Ed25519.WholeLocal.satMem a else tblMem a

theorem signMem_held : ∀ i < combWords.length,
    signMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [combWords_length] at hi
  rw [← tblMem_held i (by rw [combWords_length]; exact hi)]
  refine Mem.readW_congr fun j hj => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [signMem, e, show ¬ 0x100000 + 8 * i + j < 0x100000 by omega, ↓reduceIte]

theorem signMem_bytes {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x100000) :
    bytesAt signMem p n = bytesAt Proof.Ed25519.WholeLocal.satMem p n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [signMem, e, show p.toNat + i < 0x100000 by omega, ↓reduceIte]

theorem signMem_pk : bytesAt signMem 0x2100 32 = Spec.Ed25519.publicKey (bytesAt signMem 0x2000 32) := by
  rw [signMem_bytes (by decide), signMem_bytes (by decide)]
  exact Proof.Ed25519.WholeLocal.sat_pk

/-- `signSat` with the table. -/
def signSatC : State :=
  { signSat signMem with rd := (signSat signMem).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem signC_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) Spec.Ed25519.signCachedSig "frame" .u64 36
    (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208).pre signSatC := by
  have hl := combWords_length
  have held := signMem_held
  have hm := signMem_pk
  change (Sig.scratchContract (RISCV64.abi.withConsts [(combSym, combWords)]) Spec.Ed25519.signCachedSig "frame"
    .u64 36 (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208).pre signSatC
  generalize combWords = W' at hl held ⊢
  generalize e : signSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem signC_implies : signC.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts) Spec.Ed25519.signCachedSig "frame" .u64 36
    (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := signR) signR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨signSatC, signC_sat⟩

theorem signCached_verified : Verified RISCV64.target signCached (Sig.scratchContract (RISCV64.abi.withConsts combConsts) Spec.Ed25519.signCachedSig "frame" .u64 36
    (Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (sign_ok base_ok) (signCached_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, h4, h5, h6, hsp⟩, hsy⟩ =>
    ⟨hsp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) signC_implies

/-- A state satisfying `vg_ed25519_sign_cached`'s precondition, without the frame. -/
def signFrameSat : State := { signSatC with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSat_pre : ∃ s, (Spec.Ed25519.signCachedContract (RISCV64.abi.withConsts combConsts)
    (208 + 288)).pre s := by
  refine ⟨signFrameSat, ?_⟩
  have hl := combWords_length
  have held := signMem_held
  have hm := signMem_pk
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : signFrameSat = s
  sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 288 bytes, whose first 224 it zeroes before returning. -/
theorem signCached_framed :
    Verified RISCV64.target signCachedCode
      (Spec.Ed25519.signCachedContract (RISCV64.abi.withConsts combConsts) (208 + 288)) :=
  Verified.stackScratchWipedC (sig := Spec.Ed25519.signCachedSig) (nm := "frame") (e := .u64) (n := 36)
    (pre := Proof.Ed25519.WholeLocal.signCachedPre RISCV64.abi.ptrBits)
    (post := Proof.Ed25519.WholeLocal.signCachedPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 288)
    (words := 28) signCached_verified (by decide) (by decide) (by decide)
    (Proof.Ed25519.WholeLocal.signCachedPostOut_local _) signFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole

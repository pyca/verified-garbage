module

import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesVerified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Cast5.ModeMem
public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq

/-!
# CAST5's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWipedC`, for contracts under the calling convention
with the table), since it holds a block of data, the chaining value and our
caller's registers: 208 bytes, the frame's 32-byte header and the 176 of
working space. The code uses no other stack: it calls nothing.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.Modes

open VG VG.PPC64LE
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.PPC64LE (ecbSatMem ecbSatMem_held ecbConsts_eq)

/-- A state satisfying the functions' precondition, with the table: the
subkeys at `0x1000`, 16 rounds, the IV at `0x2000`, no data at `0x3000`. -/
def frameSatC : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩]
  syms _ := 0x100000

theorem frame_sat (post : Spec.Cast5.cbcChainedSig.Post abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract (abi.withConsts ecbConsts) (Proof.Cast5.cbcChainedPre abi.ptrBits)
      post true (0 + 208)).pre s := by
  refine ⟨frameSatC, ?_⟩
  have held := ecbSatMem_held
  have hl := Proof.Cast5.s1234_length
  generalize e : frameSatC = s
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcEncryptChained)
      (Spec.Cast5.cbcEncryptChainedContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Proof.Cast5.cbcChainedPre abi.ptrBits)
    (post := Proof.Cast5.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cbcEncryptChained_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcEncChainedPost_local _) (Proof.Cast5.cbcEncChainedPostOut_local _) (frame_sat _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cbcDecryptChained)
      (Spec.Cast5.cbcDecryptChainedContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Proof.Cast5.cbcChainedPre abi.ptrBits)
    (post := Proof.Cast5.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cbcDecryptChained_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcDecChainedPost_local _) (Proof.Cast5.cbcDecChainedPostOut_local _) (frame_sat _)

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.ofb)
      (Spec.Cast5.ofbContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.ofbPre abi.ptrBits)
    (post := Proof.Cast5.ofbPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    ofb_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbPost_local _) (Proof.Cast5.ofbPostOut_local _) (frame_sat _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.cfbPre abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cfbEncrypt_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncPost_local _) (Proof.Cast5.cfbEncPostOut_local _) (frame_sat _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 Impl.Cast5.PPC64LE.cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.cfbPre abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cfbDecrypt_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecPost_local _) (Proof.Cast5.cfbDecPostOut_local _) (frame_sat _)

end VG.Proof.Cast5.PPC64LE.Modes

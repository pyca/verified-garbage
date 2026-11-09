module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Fn
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs

/-!
# AES-GCM decryption out of place, RISC-V: `Verified`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_open_to` decrypts
from `src` straight to `dst` in one pass (`OpenTo/Fn.lean`, `OpenTo/CT.lean`),
proved with its working space as a last argument, after the others on the
stack (`openTo_verified`, against `Sig.scratchContract`), and then in a frame
that allocates it (`openTo_framed`, `Verified.stackScratchArgs`), as
`vg_aes_gcm_open` (`Proof/AesGcm/RISCV64/Verified.lean`). The frame copies
the arguments passed on the stack, which needs the contract to read the
memory on entry only within the function's buffers (`openToPre_local`,
`openToPost_local`, `openToLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.OpenTo

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.OpenTo
open VG.Proof.AesGcm (agree_of le15 openResult_local bytesAt_congr)

/-! ## Locality -/

variable (pb : Nat)

theorem openToPre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 11
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact h

/-- The twelve words of `vg_aes_gcm_open_to`'s arguments, named. -/
theorem words_eq : ∀ vs : List (BitVec 64), vs.length = (Spec.Gcm.openToSig.words pb).length →
    ∃ ctx rd nonce nl aad al src len dst dl tag tl,
      vs = [ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl] := by
  intro vs hlen
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨src, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem openToPost_local : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₁ m' r →
      Curry.apply (Spec.Gcm.openToSig.words pb) (Proof.AesGcm.openToRoundsPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ := words_eq pb vs hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Proof.AesGcm.openToRoundsPost pb) _ m₂ m' r
  dsimp only [Curry.apply, Proof.AesGcm.openToRoundsPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  rw [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
    (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
  exact h hr

theorem openToLeak_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openToSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openToSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₁ =
      Curry.apply (Spec.Gcm.openToSig.words pb) (Spec.Gcm.openToLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, rd, nonce, nl, aad, al, src, len, dst, dl, tag, tl, rfl⟩ := words_eq pb vs hlen
  simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
    (Spec.Gcm.openToLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb]
      (Spec.Gcm.openToLeak pb) _ m₂
  dsimp only [Curry.apply, Spec.Gcm.openToLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (agree_of hb.1) (agree_of hb.2.1) (agree_of hb.2.2.1)
      (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

/-! ## With the working space as an argument -/

theorem openTo_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : openToRISCV64.pre s) :
    ∃ t s', Exec isa openTo s t s' ∧ abiPreserved s s' ∧ openToRISCV64.post s s' :=
  openTo_wp hs

/-- `tag` at `0x5000`, `dst` at `0x7000` and the working space at `0x6000`,
the stack arguments; no nonce, additional data, text or tag. -/
def toSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x70 else bif Nat.beq a.toNat 0x9011 then 0x50 else
    bif Nat.beq a.toNat 0x9021 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 40⟩]
  wr := [⟨0x7000, 0⟩, ⟨0x6000, 2560⟩]

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and the public data include the leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem openTo_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target openTo
      (Sig.scratchContract RISCV64.abi Spec.Gcm.openToSig "work" .u64 320 (Spec.Gcm.openToPre 64)
        (Proof.AesGcm.openToRoundsPost 64) true 2048 (some (Spec.Gcm.openToLeak 64))) :=
  Verified.of_correct openTo_correct openTo_ct
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToPre, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Proof.AesGcm.openToRoundsPost, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop]
        simp only [openToRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToLeak, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range,
          List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
          exacts [a0, a1, a2, a3, a4]
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Gcm.openToSig,
          Spec.Gcm.openToPre, openToRISCV64, openToPreR, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
          stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toSat }

/-! ## With the working space on the stack -/

/-- A state satisfying `vg_aes_gcm_open_to`'s precondition, without the
working space: `dst`, `dst_len`, `tag` and `tag_len` alone on the stack. -/
def toFrameSat : State :=
  { toSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 32⟩],
               wr := [⟨0x7000, 0⟩] }

theorem toFrameSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract RISCV64.abi 4656).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Proof.AesGcm.openToRoundsPost, Spec.Gcm.openToLeak, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr,
    List.getD, List.range, List.range.loop]
    [toFrameSat, toSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using toFrameSat

/-- `open_to`, whose `dst`, `dst_len`, `tag` and `tag_len` arrive on the
stack, as `open`'s `tag` and `tag_len` do. -/
theorem openTo_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2608 4 openTo)
      (Proof.AesGcm.openToRoundsContract RISCV64.abi 4656) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openToSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openToPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.openToRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2608) (m := 4) (leak := some (Spec.Gcm.openToLeak RISCV64.abi.ptrBits))
    openTo_verified (by decide) (by decide) (openToPre_local _) (openToPost_local _)
    toFrameSat_pre (hleak := openToLeak_local _)

end VG.Proof.AesGcm.RISCV64.OpenTo

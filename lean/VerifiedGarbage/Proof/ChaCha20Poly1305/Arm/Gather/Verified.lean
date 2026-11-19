module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
public import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm.SealGather
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Verified
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm.SealGather
meta import VerifiedGarbage.Proof.AesGcm.Arm.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `ChaCha20Poly1305.Arm.Gather.CT`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.Arm.Gather.Fn`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.Arm.Gather.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 696 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): `(key = r0, nonce = r1, aad = r2, aad_len = r3,
src = [sp], src_count = [sp + 4], dst = [sp + 8], len = [sp + 12],
tag = [sp + 16])`. Addresses are 32-bit, as memory takes them through
`State.addr`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : BitVec 32 := s.gpr .r0
abbrev Nn : BitVec 32 := s.gpr .r1
abbrev Ad : BitVec 32 := s.gpr .r2
abbrev AL : Nat := (s.gpr .r3).toNat
abbrev Src : BitVec 32 := stackArg s 0
abbrev Cnt : Nat := (stackArg s 1).toNat
abbrev Dst : BitVec 32 := stackArg s 2
abbrev L : Nat := (stackArg s 3).toNat
abbrev Tg : BitVec 32 := stackArg s 4

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack arguments and the stack
below the stack pointer. -/
abbrev kR : Region := ⟨State.addr (K s), 32⟩
abbrev nR : Region := ⟨State.addr (Nn s), 12⟩
abbrev aR : Region := ⟨State.addr (Ad s), AL s⟩
abbrev dsR : Region := ⟨State.addr (Src s), Cnt s * 8⟩
abbrev lsR : List Region := Sig.listed 32 s.mem .u8 (State.addr (Src s)) (Cnt s)
abbrev dR : Region := ⟨State.addr (Dst s), L s⟩
abbrev tgR : Region := ⟨State.addr (Tg s), 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 20⟩
abbrev stkR : Region := ⟨State.addr s.sp - BitVec.ofNat 64 696, 696⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 32 s.mem (State.addr (Src s)) i
abbrev pt (i : Nat) : List Byte := gathered 32 s.mem (State.addr (Src s)) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 32 ∧ (Nn s).toNat + 12 ≤ 2 ^ 32 ∧ (Ad s).toNat + AL s ≤ 2 ^ 32 ∧
    (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32) ∧
    (Dst s).toNat + L s ≤ 2 ^ 32 ∧ (Tg s).toNat + 16 ≤ 2 ^ 32 ∧
    696 ≤ s.sp.toNat ∧ s.sp.toNat + 20 ≤ 2 ^ 32 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧ (∀ i < 5, stackArg s₁ i = stackArg s₂ i) ∧
    ∀ i < Cnt s₁ * 8,
      s₁.mem (State.addr (Src s₁) + BitVec.ofNat 64 i) = s₂.mem (State.addr (Src s₁) + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (State.addr (K s)) 32) (bytesAt s.mem (State.addr (Nn s)) 12)
      (bytesAt s.mem (State.addr (Ad s)) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (State.addr (Dst s)) (L s), bytesAt s'.mem (State.addr (Tg s)) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherArm : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.Arm.Gather

end

end

/-! ### `ChaCha20Poly1305.Arm.Gather.Callee`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls `vg_chacha20_poly1305_seal` as an artifact (`SealFn`), with its
working space in a frame of its own, so what the proof needs of it is its
shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 664 bytes of
stack): its precondition from the layout the call gives it (`callPre`,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- `vg_chacha20_poly1305_seal`, by its shared contract, whose frames use at
most the 664 bytes below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified Arm.target code (Spec.ChaCha20Poly1305.sealContract Arm.abi 664)
  depth : armStack code ≤ 664

/-- What a call of `vg_chacha20_poly1305_seal(key = r0, nonce = r1, aad = r2,
aad_len = r3, data = [sp], len = [sp + 4], tag = [sp + 8])` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), 32⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  let tag : Region := ⟨State.addr (stackArg s 2), 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 12⟩
  let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩
  s.rd = [key, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 12 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 16 ≤ 2 ^ 32 ∧ 664 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨a₂₃, a₂₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀,
    a₂₁, a₂₂⟩

/-- Its postcondition. -/
theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).post s s') :
    encrypt (bytesAt s.mem (State.addr (s.gpr .r0)) 32) (bytesAt s.mem (State.addr (s.gpr .r1)) 12)
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) =
      (bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat,
        bytesAt s'.mem (State.addr (stackArg s 2)) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Spec.ChaCha20Poly1305.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  exact h

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧
    ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨a₅, a₁, a₂, a₃, a₄, a₆ 0 (by decide), a₆ 1 (by decide), a₆ 2 (by decide)⟩

end VG.Proof.ChaCha20Poly1305.Arm.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 32 bytes at `P = sp - 32`, lays out in it the call's
stack arguments, our return address and `r0`–`r3` (`entered_wp`), gathers
the slices to `dst` (`gathered_wp`, AES-GCM's gathering), reloads `r0`–`r3`
(`ready_wp`) and calls `vg_chacha20_poly1305_seal` on them in place
(`called_wp`, by its shared contract); the call keeps our frame, so the
return address comes back from it (`ret_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Arm.FrameStack VG.Impl.ChaCha20Poly1305.Arm.SealGather VG.WriteBytes
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)
open VG.Proof.AesGcm.Arm (in_left add_ofNat_zero covers_of_mem covers_cons covers_append' covers_prefix covers_nil)
open VG.Proof.AesGcm.Arm.Gather (GatherPre gather_wp gatherRegs WP.run WP.split)

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 52 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 52) : State.addr (P + BitVec.ofNat 32 d) = State.addr P + BitVec.ofNat 64 d :=
  addr_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 52) (he : e + 4 ≤ 52) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 52) (h : 4 ≤ e) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr P) 32 = m.readW (State.addr P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_ofNat_zero] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 52) (h : 4 ≤ d) :
    (m.writeW (State.addr P) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_ofNat_zero] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our return address and
`r0`–`r3` at `P + 12` … `P + 28`, and the three words at `P + 40`, `P + 44`
and `P + 48` (`dst`, `len`, `tag`) at `P` … `P + 8`. -/
def eMem (m : Mem) (P : BitVec 32) (lr r0 r1 r2 r3 : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (State.addr (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
  w (w ((w (w (w (w (w m 12 lr) 16 r0) 20 r1) 24 r2) 28 r3).writeW (State.addr P) (r 40)) 4 (r 44)) 8 (r 48)

theorem entry_ok (a : State) (hP : a.sp.toNat + 52 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 32 → InRegions a.wr (State.addr (a.sp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 32 ≤ d → d + 4 ≤ 52 → InRegions (a.rd ++ a.wr) (State.addr (a.sp + BitVec.ofNat 32 d)) 4) :
    WP isa entry a fun e =>
      e.mem = eMem a.mem a.sp (a.gpr .lr) (a.gpr .r0) (a.gpr .r1) (a.gpr .r2) (a.gpr .r3) ∧
      e.gpr .r0 = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 32)) 32 ∧
      e.gpr .r2 = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 40)) 32 ∧
      e.gpr .lr = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 36)) 32 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r12 → r ≠ .lr → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  have hw0 : InRegions a.wr (State.addr a.sp) 4 := by simpa only [add_ofNat_zero] using hw 0 (by decide)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := entryWords) ?_
  refine WP.run ⟨_, by
    arun [Impl.AesGcm.Arm.SealGather.setFp, entryWords, hw 12 (by decide), hw 16 (by decide),
      hw 20 (by decide), hw 24 (by decide), hw 28 (by decide), hw0, hw 4 (by decide), hw 8 (by decide),
      hr 32 (by decide) (by decide), hr 36 (by decide) (by decide), hr 40 (by decide) (by decide),
      hr 44 (by decide) (by decide), hr 48 (by decide) (by decide), add_ofNat_zero, rdw hP, rdw0 hP, rd0w hP],
    rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, rfl, rfl, rfl, fun r h₀ h₂ h₁₂ hl => by simp [gpr_setReg, h₀, h₂, h₁₂, hl], rfl, rfl, rfl⟩

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 52 ≤ 2 ^ 32) (lr r0 r1 r2 r3 : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨State.addr P, 32⟩] m (eMem m P lr r0 r1 r2 r3) := by
  have c (d : Nat) (hd : d + 4 ≤ 32) : (⟨State.addr P, 32⟩ : Region).Contains (State.addr (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  have c0 : (⟨State.addr P, 32⟩ : Region).Contains (State.addr P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨State.addr P, 32⟩ : Region)
  exact ((((((((Frame.refl _ m).writeW hm _ (c 12 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _
    (c 20 (by decide))).writeW hm _ (c 24 (by decide))).writeW hm _ (c 28 (by decide))).writeW hm _ c0).writeW hm _
    (c 4 (by decide))).writeW hm _ (c 8 (by decide))

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P lr r0 r1 r2 r3
    let r (m : Mem) (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
    e.readW (State.addr P) 32 = r m 40 ∧ r e 4 = r m 44 ∧ r e 8 = r m 48 ∧ r e 12 = lr ∧ r e 16 = r0 ∧
      r e 20 = r1 ∧ r e 24 = r2 ∧ r e 28 = r3 := by
  simp (disch := first | decide | omega_arith) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega_arith) hd

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 696 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.sp - BitVec.ofNat 32 32
abbrev Bs : Addr := State.addr s.sp - BitVec.ofNat 64 696
abbrev FR : Region := ⟨State.addr (Pf s), 32⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (State.addr (Dst s)) (pt s (Cnt s))

end

/-- What `gatherPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hP : (Pf s).toNat + 52 ≤ 2 ^ 32
  hPn : (Pf s).toNat = s.sp.toNat - 32
  hBn : (Bs s).toNat + 716 ≤ 2 ^ 32
  hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 664
  sa : ∀ i, i < 5 → s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 (32 + 4 * i))) 32 = stackArg s i
  w₁ : 696 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, w₂, hgl,
    -⟩ := id hs
  have hPn : (Pf s).toNat = s.sp.toNat - 32 := sub_toNat' (by omega_arith)
  have hB : Bs s = State.addr (s.sp - BitVec.ofNat 32 696) := (addr_sub' (by omega_arith)).symm
  have hBn : (Bs s).toNat = s.sp.toNat - 696 := by
    rw [hB]; simp only [State.addr, BitVec.toNat_setWidth]
    rw [sub_toNat' (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 664 := by
    rw [addr_sub' (by omega_arith), show State.addr s.sp = Bs s + BitVec.ofNat 64 696 from (BitVec.sub_add_cancel _ _).symm,
      add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨hs, by omega_arith, hPn, by omega_arith, hA0, fun i hi => ?_, w₁, hgl⟩
  show _ = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 696) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 696⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 52) : State.addr (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (664 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 696⟩ := by
  show Region.Sub ⟨State.addr (Pf s), 32⟩ _; rw [h.hA0]; exact stk_sub s 664 32 (by decide)

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

omit h in
theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 696, 20⟩ := by
  show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 20⟩ : Region) = _
  rw [Nat.mul_zero, add_ofNat_zero, BitVec.sub_add_cancel]

/-- The words of the stack arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 32 ≤ d) (h₂ : d + 4 ≤ 52) (rs : List Region) :
    InRegions (s.rd ++ rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_left _ h.argIn, by
    rw [hArg, h.hA (by omega_arith)]; exact contains_off _ (by omega_arith) (by omega_arith) (by omega_arith)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 32) (rs : List Region) :
    InRegions (FR s :: rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega_arith)]; exact Offset.contains_base _ h₂ (by omega_arith)⟩

theorem sa' (i d : Nat) (hi : i < 5) (hd : d = 32 + 4 * i) :
    s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = stackArg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _ _ _ _

/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 696⟩) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  eMem_frame h.hP _ _ _ _ _ x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (h.fr_sub x hc)

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 32 (State.addr (Src s)) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 →
    s.mem x = eM s x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bl, -⟩ := h.pre
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact bds.symm
  · exact (bl r hr).symm

theorem hpt : Spec.Gcm.gathered 32 (eM s) (State.addr (Src s)) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 4 ≤ 32) :
    (gM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  rw [h.hA (by omega_arith)]
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact bd.sub_left (stk_sub s _ 4 (by omega_arith))

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r0 : e.gpr .r0 = Src s
  r2 : e.gpr .r2 = Dst s
  lr : e.gpr .lr = stackArg s 1
  gpr : ∀ r, r ∉ gatherRegs → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa entry (allocated 32 s) (Entered s) := by
  refine WP.mono (entry_ok (allocated 32 s) h.hP (fun d hd => h.inFr d hd _)
      (fun d h₁ h₂ => h.inArg d h₁ h₂ _)) fun e ⟨me, r0e, r2e, lre, ge, spe, rde, wre⟩ => ?_
  refine ⟨me, r0e.trans (h.sa' 0 32 (by decide) rfl), r2e.trans (h.sa' 2 40 (by decide) rfl),
    lre.trans (h.sa' 1 36 (by decide) rfl), fun r hr => ?_, spe, rde, wre⟩
  simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h₀, -, h₂, -, h₁₂, hl⟩ := hr
  exact ge r h₀ h₂ h₁₂ hl

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { r0 := he.r0
          lr := by rw [he.lr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          r2 := he.r2
          hcnt := (stackArg s 1).isLt
          dw := ods
          fitD := od
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem (List.mem_append_left _ (by rw [he.rd]; show dsR s ∈ s.rd; rw [rd]; simp))
          lsr := fun r hr => covers_of_mem (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd]; show r ∈ s.rd; rw [rd]; simp [hr]))
          lfit := fun r hr => ol r (by rw [hls] at hr; exact hr)
          dw' := covers_of_mem (by rw [he.wr, wr]; simp)
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → g.gpr r = s.gpr r
  sp : g.sp = Pf s
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.AesGcm.Arm.SealGather.gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hg => (kg.gpr r hg).trans (he.gpr r hg), kg.sp.trans he.sp, kg.rd.trans he.rd,
    kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gM s
  r0 : c.gpr .r0 = s.gpr .r0
  r1 : c.gpr .r1 = s.gpr .r1
  r2 : c.gpr .r2 = s.gpr .r2
  r3 : c.gpr .r3 = s.gpr .r3
  gpr : ∀ r, r ∉ gatherRegs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa callArgs g (Ready s) := by
  have hr (d : Nat) (hd : d + 4 ≤ 32) : InRegions (g.rd ++ g.wr) (State.addr (g.sp + BitVec.ofNat 32 d)) 4 := by
    rw [hg.sp, hg.wr]; exact in_left (h.inFr d hd _)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := argWords) ?_
  refine WP.run ⟨_, by
    arun [Impl.AesGcm.Arm.SealGather.setFp, argWords, add_ofNat_zero, hr 16 (by decide), hr 20 (by decide),
      hr 24 (by decide), hr 28 (by decide)], rfl⟩ fun c hc => ?_
  subst hc
  obtain ⟨-, -, -, -, w16, w20, w24, w28⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  have rd (d : Nat) (hd : d + 4 ≤ 32) : g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 d)) 32 =
      (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [hg.mem, hg.sp, h.gFrame d hd]
  refine ⟨hg.mem, ?_, ?_, ?_, ?_, fun r hr => ?_, hg.sp, hg.rd, hg.wr⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 16 (by decide)]; exact w16
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 20 (by decide)]; exact w20
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 24 (by decide)]; exact w24
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 28 (by decide)]; exact w28
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₀, h₁, h₂, h₃, h₁₂, hl⟩ := hr
    simp only [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, ↓reduceIte]
    exact hg.gpr r (by simp [gatherRegs, h₀, h₁, h₂, h₃, h₁₂, hl])

/-- The callee's stack arguments: words of our frame. -/
theorem Ready.word {s c : State} (hc : Ready s c) (rd' wr' : List Region) (i : Nat) :
    stackArg ((c.callEntry).withRegions rd' wr') i = (gM s).readW (State.addr (Pf s + BitVec.ofNat 32 (4 * i))) 32 := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, hc.mem, hc.sp]

theorem Ready.args {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    stackArg c' 0 = Dst s ∧ stackArg c' 1 = stackArg s 3 ∧ stackArg c' 2 = Tg s := by
  obtain ⟨w0, w4, w8, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  simp only [hc.word]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mul_zero, h.gFrame 0 (by decide), add_ofNat_zero]; exact w0.trans (h.sa' 2 40 (by decide) rfl)
  · rw [h.gFrame 4 (by decide)]; exact w4.trans (h.sa' 3 44 (by decide) rfl)
  · rw [h.gFrame 8 (by decide)]; exact w8.trans (h.sa' 4 48 (by decide) rfl)

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    c'.gpr .r0 = s.gpr .r0 ∧ c'.gpr .r1 = s.gpr .r1 ∧ c'.gpr .r2 = s.gpr .r2 ∧ c'.gpr .r3 = s.gpr .r3 := by
  simp only [State.withRegions_gpr]
  exact ⟨by rw [c.callEntry_gpr (by decide), hc.r0], by rw [c.callEntry_gpr (by decide), hc.r1],
    by rw [c.callEntry_gpr (by decide), hc.r2], by rw [c.callEntry_gpr (by decide), hc.r3]⟩

section
variable (s : State)

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, ⟨Bs s + BitVec.ofNat 64 664, 12⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, -, -, -, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2⟩ := hc.args h (rdC s) (wrC s)
  have sad0 : stackArgAddr ((c.callEntry).withRegions (rdC s) (wrC s)) 0 = Bs s + BitVec.ofNat 64 664 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp, Nat.mul_zero, add_ofNat_zero, h.hA0]
  have hPn := h.hPn
  have hP := h.hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
      c0, c1, c2, c3, a0, a1, a2, sad0, hc.sp, h.hA0, BitVec.add_sub_cancel]
    have stkArg : (⟨Bs s, 664⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 664, 12⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 664) (e := 664) (k := 12) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    refine ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, (bd.sub_left (stk_sub s 664 12 (by decide))).symm,
      (bt.sub_left (stk_sub s 664 12 (by decide))).symm, bk.sub_left (Region.sub_prefix (by decide)),
      bn.sub_left (Region.sub_prefix (by decide)), ba.sub_left (Region.sub_prefix (by decide)),
      bd.sub_left (Region.sub_prefix (by decide)), bt.sub_left (Region.sub_prefix (by decide)), stkArg,
      ok, on, oa, od, ot, by omega_arith, by omega_arith⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 664, 32⟩] (c.rd ++ c.wr) := by
      rw [← h.hA0]; exact covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, wr]; exact List.mem_cons_of_mem _ h'))
    exact covers_append' (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (covers_prefix hfr (by decide)) covers_nil))))
      (covers_cons (hw' (by simp)) (covers_cons (hw' (by simp)) covers_nil))
  · rw [hc.wr, wr]
    exact covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp)) covers_nil)

/-- After the call. -/
structure Called (s s' : State) : Prop where
  ra : s'.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr
  out : encrypt (bytesAt (gM s) (State.addr (K s)) 32) (bytesAt (gM s) (State.addr (Nn s)) 12)
      (bytesAt (gM s) (State.addr (Ad s)) (AL s)) (bytesAt (gM s) (State.addr (Dst s)) (L s)) =
    (bytesAt s'.mem (State.addr (Dst s)) (L s), bytesAt s'.mem (State.addr (Tg s)) 16)
  gpr : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = Pf s
  rd : s'.rd = s.rd
  wr : s'.wr = FR s :: s.wr

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.name F.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2⟩ := hc.args h (rdC s) (wrC s)
  have hdep := F.depth
  have hPn := h.hPn
  have w₁ := h.w₁
  refine WP.callF (n := F.name) F.verified.1 (sealSpec_pre hcp) hcov hw (by rw [hc.sp]; omega_arith)
    fun s' rd' wr' sp' fr' pres' post' => ?_
  have hpost := sealSpec_post post'
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, a0, a1, a2,
    hc.mem, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr := by
    obtain ⟨-, -, -, w12, -⟩ :=
      eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
    have e : c.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr := by
      rw [hc.mem, h.gFrame 12 (by decide)]; exact w12
    rw [← e, h.hA (by decide)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, bt, -⟩ := h.pre
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact bd.symm.sub_right (stk_sub s _ 4 (by decide)) |>.symm
    · exact bt.symm.sub_right (stk_sub s _ 4 (by decide)) |>.symm
    · simp only [belowA, hc.sp]
      rw [addr_sub' (by omega_arith), h.hA0, add_ofNat_sub_ofNat _ (show armStack F.code ≤ 664 by omega_arith)]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by decide) (by have := h.hBn; omega_arith)
  have hpres : ∀ r ∈ preserved, r ≠ .lr → r ∉ gatherRegs := by decide
  exact ⟨ra, hpost, fun r hr hl => by rw [pres' r hr hl, hc.gpr r (hpres r hr hl)],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr⟩

/-- The return address back in `lr`, and the frame freed, whatever its bytes
then hold. -/
theorem ret_wp {s s' : State} (h : Lay s) (hc : Called s s') :
    WP isa Impl.ChaCha20Poly1305.Arm.SealGather.ret s' fun z => ∀ m u, Frame [FR s] z.mem m →
      abiPreserved s { freed 32 z with mem := m, unknowns := u } ∧
        gatherPost s { freed 32 z with mem := m, unknowns := u } := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, -, -, -, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  have hr : InRegions (s'.rd ++ s'.wr) (State.addr (s'.sp + BitVec.ofNat 32 12)) 4 := by
    rw [hc.sp, hc.wr]; exact in_left (h.inFr 12 (by decide) _)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := [Instr.ldr .lr .r12 12]) ?_
  refine WP.run ⟨_, by arun [Impl.AesGcm.Arm.SealGather.setFp, add_ofNat_zero, hr], rfl⟩ fun z hz => ?_
  subst hz
  intro ml ul hfl
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩ <;> dsimp only
  · -- The callee-saved registers.
    have h12 : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    simp only [freed, gpr_setReg, h12, ↓reduceIte]
    by_cases hl : r = .lr
    · subst hl; simp only [↓reduceIte]; rw [hc.sp]; exact hc.ra
    · simp only [hl, ↓reduceIte]; exact hc.gpr r hr hl
  · -- The stack pointer.
    simp only [freed, sp_setReg, hc.sp]
    exact BitVec.sub_add_cancel _ _
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt ml (State.addr (Dst s)) (L s), bytesAt ml (State.addr (Tg s)) 16)
    rw [bytesAt_frame hfl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact bd.symm.sub_right h.fr_sub) (by omega_arith),
      bytesAt_frame hfl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact bt.symm.sub_right h.fr_sub) (by decide)]
    have hfc : Frame [FR s, dR s] s.mem (gM s) :=
      (h.eM_frame.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 696⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right h.fr_sub
      · exact h₂
    have hk : bytesAt (gM s) (State.addr (K s)) 32 = bytesAt s.mem (State.addr (K s)) 32 :=
      bytesAt_frame hfc (apart bk kd) (by omega_arith)
    have hn : bytesAt (gM s) (State.addr (Nn s)) 12 = bytesAt s.mem (State.addr (Nn s)) 12 :=
      bytesAt_frame hfc (apart bn nd) (by omega_arith)
    have ha : bytesAt (gM s) (State.addr (Ad s)) (AL s) = bytesAt s.mem (State.addr (Ad s)) (AL s) :=
      bytesAt_frame hfc (apart ba ad) (by omega_arith)
    have hd : bytesAt (gM s) (State.addr (Dst s)) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; omega_arith)
    have := hc.out
    rw [hk, hn, ha, hd] at this
    exact this

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  have w₁ := h.w₁
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hc) fun s' hs' => ?_)
  exact ret_wp h hs'

end VG.Proof.ChaCha20Poly1305.Arm.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace, related piece by piece
from given states (`Eq2`, `Proof/AesGcm/Arm/Gather/LoopCT.lean`): the
frame's words are read and written through `r12` at the stack pointer, the
same in both runs (`rel_fp`); the gathering is constant time by
`gather_rel`; and the call is constant time by its callee's contract, whose
public arguments agree (`sealGather_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm.SealGather
open VG.Proof.AesGcm.Arm.Gather (Eq2 TT rel_seq rel_fp rel_alloc ct_of gather_rel)

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q0, q1, q2, q3, qsp, qa, hdesc⟩ := hq
  have a0 := qa 0 (by decide)
  have a1 := qa 1 (by decide)
  have a2 := qa 2 (by decide)
  have a3 := qa 3 (by decide)
  have a4 := qa 4 (by decide)
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_fp (l := entryWords) (show Pf σ₁ = Pf σ₂ from hP) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← a0, ← a1, ← a2, ← a3] at g₂
  have hd : ∀ j < Cnt σ₁ * 8,
      e₁.mem (State.addr (Src σ₁) + BitVec.ofNat 64 j) = e₂.mem (State.addr (Src σ₁) + BitVec.ofNat 64 j) := by
    intro j hj
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₁, -, -, -, -, -, -, -, ods, -⟩ := p₁
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₂, -⟩ := p₂
    have hx : (dsR σ₁).Contains (State.addr (Src σ₁) + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by omega_using [hj, ods])
    have hx₂ : (dsR σ₂).Contains (State.addr (Src σ₁) + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← a0, ← a1]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE bds₁.symm hx, h₂.keepE bds₂.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂) fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_fp (l := argWords) (by rw [hg₁.sp, hg₂.sp, hP]) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, Bs, q0, q1, q2, q3, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a2, a3, a4]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r0₁, r1₁, r2₁, r3₁⟩ := hc₁.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨r0₂, r1₂, r2₂, r3₂⟩ := hc₂.callGpr (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₁, s1₁, s2₁⟩ := hc₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂⟩ := hc₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
      subst ha hb
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩,
        cv₁, cw₁, cv₂, cw₂⟩
      · rw [r0₁, r0₂, q0]
      · rw [r1₁, r1₂, q1]
      · rw [r2₁, r2₂, q2]
      · rw [r3₁, r3₂, q3]
      · simp only [State.withRegions_sp, State.callEntry_sp, hc₁.sp, hc₂.sp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a2
        · rw [s1₁, s1₂]; exact a3
        · rw [s2₁, s2₂]; exact a4)
    (called_wp F h₁ hc₁) (called_wp F h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address.
  exact rel_fp (l := [Instr.ldr .lr .r12 12]) (by rw [hz₁.sp, hz₂.sp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.Arm.Gather

end

end

/-! ### `ChaCha20Poly1305.Arm.Scrub`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on ARMv7, without secret residue

`seal`, `open` and `open_to`, with either arithmetic of Poly1305 (`umaal`),
keep their working space in a frame, which they wipe. Their postconditions
read the memory on return only within the data, the tag and the destination
(`Arm.Scrub.PostOut`; `open_to`'s where its precondition holds), so each is
registered followed by a wipe of all the stack its contract reserves
(`Arm.Scrub.scrubRegF`), and by instructions that set the registers a callee
may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Impl.ChaCha20Poly1305.Arm

/-- `Arm.Scrub.postOut_of_local`, for a postcondition that reads the memory
on return only within the buffers where the precondition holds (one that
reads an output buffer by a length the precondition equates with the
buffer's). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- `seal`'s postcondition reads the memory on return only within the
buffers: the data and the tag. -/
theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

theorem frameOk_664 : FrameOk 664 := by decide

theorem frameOk_672 : FrameOk 672 := by decide

theorem seal_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)) ≤ 664 := by
  cases umaal <;> lit_decide

theorem open_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)) ≤ 664 := by
  cases umaal <;> lit_decide

theorem openTo_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)) ≤ 672 := by
  cases umaal <;> lit_decide

theorem seal_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)) = true := by
  cases umaal <;> lit_decide

def sealReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.sealApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal)
      verified := seal_framed }
    (seal_armStack umaal) (seal_noIcall umaal) frameOk_664 (sealOut _) rfl

theorem open_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)) = true := by
  cases umaal <;> lit_decide

def openReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.openZeroApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («open» umaal)
      verified := open_framed }
    (open_armStack umaal) (open_noIcall umaal) frameOk_664 (openOut _) rfl

theorem openTo_noIcall (umaal : Bool) :
    noIcall (Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)) = true := by
  cases umaal <;> lit_decide

def openToReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.openToApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 (openTo umaal)
      verified := openTo_framed }
    (openTo_armStack umaal) (openTo_noIcall umaal) frameOk_672 (openToOut _) rfl

/-! ## `seal`, as `seal_gather` calls it -/

/-- `vg_chacha20_poly1305_seal`'s code, as its registration emits it
(`sealReg`): with its working space in a frame, and scrubbed. -/
def sealCode (umaal : Bool) : Prog isa :=
  scrubF 0 664 (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 («seal» umaal))

theorem sealCode_eq (umaal : Bool) (suffix : String) : (sealReg umaal suffix).code = sealCode umaal := rfl

theorem sealCode_verified (umaal : Bool) :
    Verified Arm.target (sealCode umaal) (Spec.ChaCha20Poly1305.sealContract Arm.abi 664) :=
  ((sealReg umaal "").verified).verified

theorem sealCode_armStack (umaal : Bool) : armStack (sealCode umaal) ≤ 664 := by
  cases umaal <;> lit_decide

end VG.Proof.ChaCha20Poly1305.Arm.Scrub

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 696 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherArm`, `gather_implies`), and so the code, calling
`vg_chacha20_poly1305_seal` by its shared contract (`sealFn`), is `Verified`
against it (`sealGather_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack VG.Impl.ChaCha20Poly1305.Arm.SealGather

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherArm.pre s) :
    ∃ t s', Exec isa (sealGather F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherArm.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i w₁ w₂ kd bk bn ba bd bt ok on oa od ot hgl hrd hwr pw bl fl
  obtain ⟨kt, nd, nt, ad, at_, dt, dds, ⟨dl, darg⟩, tds, ⟨tl, targ⟩, -⟩ := pw
  obtain ⟨bds, bls, barg⟩ := bl
  obtain ⟨ods, ol⟩ := fl
  exact ⟨hrd, hwr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr => ⟨(dl r hr).symm, (tl r hr).symm⟩,
    dt, darg, targ, bk, bn, ba, bds, bls, barg, bd, bt, ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, h⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    List.append_eq] at hp
  obtain ⟨qsp, q0, q1, q2, q3, a0, a1, a2, a3, a4, hd⟩ := hp
  refine ⟨q0, q1, q2, q3, qsp, fun i hi => ?_, hd⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`. -/
def gatherSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := bif Nat.beq a.toNat 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [gatherSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax]
    using gatherSat

theorem gather_implies : gatherArm.Implies (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified Arm.target (sealGather F.name F.code) (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi 696) :=
  Verified.of_correct (k := gatherArm) (sealGather_correct F) (sealGather_ct F) gather_implies

/-- `vg_chacha20_poly1305_seal`, with either arithmetic of Poly1305, by its
shared contract: the code its registration emits (`Scrub.sealReg`), whose
frames use at most the 664 bytes of stack its contract gives it. -/
def sealFn (umaal : Bool) : SealFn :=
  ⟨sealName umaal, Scrub.sealCode umaal, Scrub.sealCode_verified umaal, Scrub.sealCode_armStack umaal⟩

/-! ## Without secret residue -/

open VG.Arm.Scrub in
/-- `seal_gather`'s postcondition reads the memory on return only within
`dst` and `tag`. -/
theorem sealGatherPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.ChaCha20Poly1305.sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.ChaCha20Poly1305.sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb) vs m m₁ r →
      Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.ChaCha20Poly1305.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.ChaCha20Poly1305.sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro h₁ h₂
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
  exact h h₁ h₂

theorem gatherOut (stack : Nat) :
    VG.Arm.Scrub.PostOut (Spec.ChaCha20Poly1305.sealGatherContract Arm.abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 32) :=
  VG.Arm.Scrub.postOut_of_local VG.Arm.Scrub.ScrubAbi.plain (sealGatherPost_out _)

theorem frameOk_696 : VG.Arm.Scrub.FrameOk 696 := by decide

theorem gather_armStack (umaal : Bool) :
    armStack (sealGather (sealFn umaal).name (sealFn umaal).code) ≤ 696 := by
  cases umaal <;> lit_decide

/-- `seal_gather`, calling `seal` with either arithmetic of Poly1305, followed
by a wipe of the stack its contract reserves, and by instructions that set
the registers a callee may change and the flags to constants. -/
theorem gather_noIcall (umaal : Bool) :
    VG.Arm.noIcall (sealGather (sealFn umaal).name (sealFn umaal).code) = true := by
  cases umaal <;> lit_decide

def gatherReg (umaal : Bool) (suffix : String) : Registration Spec.ChaCha20Poly1305.sealGatherApi Arm.target :=
  VG.Arm.Scrub.scrubRegF {
      suffix := suffix
      code := sealGather (sealFn umaal).name (sealFn umaal).code
      verified := sealGather_verified (sealFn umaal) }
    (gather_armStack umaal) (gather_noIcall umaal) frameOk_696 (gatherOut _) rfl

end VG.Proof.ChaCha20Poly1305.Arm.Gather

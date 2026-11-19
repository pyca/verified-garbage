module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Verified
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Callee
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
import VerifiedGarbage.Proof.Framework.X86.Rel2
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
meta import VerifiedGarbage.Proof.AesGcm.X86.Gather.LoopCT
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86.Env
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Aes.X86.VariantProof
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86.Gather.Callee
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! ### `ChaCha20Poly1305.X86.Gather.CT`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.X86.Gather.Fn`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.X86.Gather.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 824 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): cdecl, `(key, nonce, aad, aad_len, src, src_count,
dst, len, tag)` at `[esp + 4]` on, which the function may overwrite.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86
open VG.Proof.AesGcm.X86 (w64)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : BitVec 32 := arg s 0
abbrev Nn : BitVec 32 := arg s 1
abbrev Ad : BitVec 32 := arg s 2
abbrev AL : Nat := (arg s 3).toNat
abbrev Src : BitVec 32 := arg s 4
abbrev Cnt : Nat := (arg s 5).toNat
abbrev Dst : BitVec 32 := arg s 6
abbrev L : Nat := (arg s 7).toNat
abbrev Tg : BitVec 32 := arg s 8

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the arguments, the return address
and the stack below it. -/
abbrev kR : Region := ⟨w64 (K s), 32⟩
abbrev nR : Region := ⟨w64 (Nn s), 12⟩
abbrev aR : Region := ⟨w64 (Ad s), AL s⟩
abbrev dsR : Region := ⟨w64 (Src s), Cnt s * 8⟩
abbrev lsR : List Region := Sig.listed 32 s.mem .u8 (w64 (Src s)) (Cnt s)
abbrev dR : Region := ⟨w64 (Dst s), L s⟩
abbrev tgR : Region := ⟨w64 (Tg s), 16⟩
abbrev argR : Region := ⟨argAddr s 0, 36⟩
abbrev retR : Region := ⟨w64 (s.gpr .esp), 4⟩
abbrev stkR : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 824, 824⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 32 s.mem (w64 (Src s)) i
abbrev pt (i : Nat) : List Byte := gathered 32 s.mem (w64 (Src s)) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ∧ s.wr = [dR s, tgR s, argR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (kR s).Disjoint (argR s) ∧
    (nR s).Disjoint (dR s) ∧ (nR s).Disjoint (tgR s) ∧ (nR s).Disjoint (argR s) ∧
    (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧ (aR s).Disjoint (argR s) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (dR s).Disjoint r) ∧
    (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (tgR s).Disjoint r) ∧
    (tgR s).Disjoint (argR s) ∧ (dsR s).Disjoint (argR s) ∧ (∀ r ∈ lsR s, r.Disjoint (argR s)) ∧
    (retR s).Disjoint (kR s) ∧ (retR s).Disjoint (nR s) ∧ (retR s).Disjoint (aR s) ∧
    (retR s).Disjoint (dR s) ∧ (retR s).Disjoint (tgR s) ∧ (retR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (retR s).Disjoint r) ∧ (retR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧ (stkR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 32 ∧ (Nn s).toNat + 12 ≤ 2 ^ 32 ∧ (Ad s).toNat + AL s ≤ 2 ^ 32 ∧
    (Dst s).toNat + L s ≤ 2 ^ 32 ∧ (Tg s).toNat + 16 ≤ 2 ^ 32 ∧
    (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32) ∧
    824 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the stack pointer, the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 9, arg s₁ i = arg s₂ i) ∧
    ∀ i < Cnt s₁ * 8, s₁.mem (w64 (Src s₁) + BitVec.ofNat 64 i) = s₂.mem (w64 (Src s₁) + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (w64 (K s)) 32) (bytesAt s.mem (w64 (Nn s)) 12) (bytesAt s.mem (w64 (Ad s)) (AL s))
      (pt s (Cnt s)) =
    (bytesAt s'.mem (w64 (Dst s)) (L s), bytesAt s'.mem (w64 (Tg s)) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherX86 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.X86.Gather

end

end

/-! ### `ChaCha20Poly1305.X86.Gather.Callee`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an instance of `vg_chacha20_poly1305_seal` as an artifact (`SealFn`),
with its working space in a frame of its own, so what the proof needs of it
is its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 772 bytes
of stack): its precondition from the layout the call gives it (`callPre`,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86
open VG.Proof.AesGcm.X86 (w64 toNat_w64)
open VG.Proof.AesGcm.X86.Gather (sw32)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An instance of `vg_chacha20_poly1305_seal`, by its shared contract, which
never writes `esp` and whose calls and frames use at most the 772 bytes
below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Spec.ChaCha20Poly1305.sealContract X86.abi 772)
  noSp : NoSp code
  depth : stackUse code ≤ 772

/-- What a call of `vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, data,
len, tag)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨w64 (arg s 0), 32⟩
  let nonce : Region := ⟨w64 (arg s 1), 12⟩
  let aad : Region := ⟨w64 (arg s 2), (arg s 3).toNat⟩
  let data : Region := ⟨w64 (arg s 4), (arg s 5).toNat⟩
  let tag : Region := ⟨w64 (arg s 6), 16⟩
  let args : Region := ⟨argAddr s 0, 28⟩
  let ret : Region := ⟨w64 (s.gpr .esp), 4⟩
  let stk : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 772, 772⟩
  772 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32 ∧
    s.rd = [key, nonce, aad] ∧ s.wr = [data, tag, args] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ key.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint args ∧ data.Disjoint tag ∧
    data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint key ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
    ret.Disjoint args ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint args ∧
    (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 12 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 16 ≤ 2 ^ 32

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.ChaCha20Poly1305.sealContract X86.abi 772).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩

/-- Its postcondition. -/
theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract X86.abi 772).post s s') :
    encrypt (bytesAt s.mem (w64 (arg s 0)) 32) (bytesAt s.mem (w64 (arg s 1)) 12)
        (bytesAt s.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (w64 (arg s 4)) (arg s 5).toNat) =
      (bytesAt s'.mem (w64 (arg s 4)) (arg s 5).toNat, bytesAt s'.mem (w64 (arg s 6)) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Spec.ChaCha20Poly1305.sealPost,
    X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil,
    Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64] at h
  exact h

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i) :
    (Spec.ChaCha20Poly1305.sealContract X86.abi 772).pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide),
    a₂ 5 (by decide), a₂ 6 (by decide)⟩

end VG.Proof.ChaCha20Poly1305.X86.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 48 bytes at `P = esp - 48` (`WP.alloc`), keeps our
caller's `ebx`, `esi` and `edi` in it and lays out the call's seven arguments
(`entered_wp`), gathers the slices to `dst` (`gathered_wp`, AES-GCM's
gathering), calls `vg_chacha20_poly1305_seal` on them in place (`called_wp`,
by its shared contract), which keeps our frame above its arguments, and
restores the registers (`ret_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.ChaCha20Poly1305.X86.SealGather VG.WriteBytes
open VG.Impl.AesGcm.X86.SealGather (sp gather restore)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)
open VG.Proof.AesGcm.X86 (w64 w64_add toNat_w64 add_zero32 setMem gpr_setMem mem_setMem rd_setMem wr_setMem)
open VG.Proof.AesGcm.X86.Gather (GatherPre gather_wp gatherRegs allocated freed WP.alloc allocated_esp allocated_gpr
  allocated_mem allocated_rd allocated_wr)

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 88 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 88) : w64 (P + BitVec.ofNat 32 d) = w64 P + BitVec.ofNat 64 d :=
  w64_add (by omega_arith)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 88) (he : e + 4 ≤ 88) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 =
      m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega_arith), aP hP (by omega_arith)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_arith) (by omega_arith)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 88) (h : 4 ≤ e) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 P) 32 = m.readW (w64 P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_zero32] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 88) (h : 4 ≤ d) :
    (m.writeW (w64 P) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 = m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_zero32] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our caller's `ebx`, `esi`
and `edi` at `P + 36` … `P + 44`, and our arguments `key`, `nonce`, `aad`,
`aad_len`, `dst`, `len` and `tag` (at `P + 52` … `P + 64` and `P + 76` …
`P + 84`) at `P` … `P + 24`. -/
def eMem (m : Mem) (P : BitVec 32) (ebx esi edi : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (w64 (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w (w ((w (w (w m 36 ebx) 40 esi) 44 edi).writeW (w64 P) (r 52)) 4 (r 56)) 8 (r 60)) 12 (r 64))
    16 (r 76)) 20 (r 80)) 24 (r 84)

theorem entry_ok (a : State) (hP : (a.gpr .esp).toNat + 88 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 88 → InRegions (a.rd ++ a.wr) (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4) :
    WP isa (.block entry) a fun e =>
      e.mem = eMem a.mem (a.gpr .esp) (a.gpr .ebx) (a.gpr .esi) (a.gpr .edi) ∧
      e.gpr .esi = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 68)) 32 ∧
      e.gpr .ebx = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 72)) 32 ∧
      e.gpr .edx = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 76)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .esi → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  have hw0 : InRegions a.wr (w64 (a.gpr .esp)) 4 := by simpa only [add_zero32] using hw 0 (by decide)
  refine WP.of_runBlock ⟨_, by
    xrun [entry, sp, hw 36 (by decide), hw 40 (by decide), hw 44 (by decide), hw0, hw 4 (by decide),
      hw 8 (by decide), hw 12 (by decide), hw 16 (by decide), hw 20 (by decide), hw 24 (by decide),
      hr 52 (by decide) (by decide), hr 56 (by decide) (by decide), hr 60 (by decide) (by decide),
      hr 64 (by decide) (by decide), hr 68 (by decide) (by decide), hr 72 (by decide) (by decide),
      hr 76 (by decide) (by decide), hr 80 (by decide) (by decide), hr 84 (by decide) (by decide), add_zero32,
      rdw hP, rdw0 hP, rd0w hP], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg]; rfl
  · regs []
  · regs []
  · regs []
  · simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]
  · simp only [rd_setMem, rd_setReg]
  · simp only [wr_setMem, wr_setReg]

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 88 ≤ 2 ^ 32) (ebx esi edi : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨w64 P, 48⟩] m (eMem m P ebx esi edi) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨w64 P, 48⟩ : Region).Contains (w64 (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega_arith)]; exact Offset.contains_base _ hd (by omega_arith)
  have c0 : (⟨w64 P, 48⟩ : Region).Contains (w64 P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨w64 P, 48⟩ : Region)
  unfold eMem; dsimp only
  refine Frame.writeW ?_ hm _ (c 24 (by decide)); refine Frame.writeW ?_ hm _ (c 20 (by decide))
  refine Frame.writeW ?_ hm _ (c 16 (by decide)); refine Frame.writeW ?_ hm _ (c 12 (by decide))
  refine Frame.writeW ?_ hm _ (c 8 (by decide)); refine Frame.writeW ?_ hm _ (c 4 (by decide))
  refine Frame.writeW ?_ hm _ c0; refine Frame.writeW ?_ hm _ (c 44 (by decide))
  refine Frame.writeW ?_ hm _ (c 40 (by decide)); refine Frame.writeW ?_ hm _ (c 36 (by decide))
  exact Frame.refl _ _

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P ebx esi edi
    let r (m : Mem) (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
    e.readW (w64 P) 32 = r m 52 ∧ r e 4 = r m 56 ∧ r e 8 = r m 60 ∧ r e 12 = r m 64 ∧ r e 16 = r m 76 ∧
      r e 20 = r m 80 ∧ r e 24 = r m 84 ∧ r e 36 = ebx ∧ r e 40 = esi ∧ r e 44 = edi := by
  simp (disch := first | decide | omega_arith) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub_toNat32 {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) : (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
    show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

theorem w64_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    w64 (x - BitVec.ofNat 32 k) = w64 x - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_w64, sub_toNat32 hk, BitVec.toNat_sub, toNat_w64, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by have := x.isLt; omega_arith)]
  have := x.isLt
  rw [show 2 ^ 64 - k + x.toNat = (x.toNat - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega_arith) hd

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 824 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 48
abbrev Bs : Addr := w64 (s.gpr .esp) - BitVec.ofNat 64 824
abbrev FR : Region := ⟨w64 (Pf s), 48⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (w64 (Dst s)) (pt s (Cnt s))

end

/-- What `gatherPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  rd : s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s
  wr : s.wr = [dR s, tgR s, argR s]
  kd : (kR s).Disjoint (dR s)
  kt : (kR s).Disjoint (tgR s)
  nd : (nR s).Disjoint (dR s)
  nt : (nR s).Disjoint (tgR s)
  ad : (aR s).Disjoint (dR s)
  at_ : (aR s).Disjoint (tgR s)
  dt : (dR s).Disjoint (tgR s)
  dds : (dR s).Disjoint (dsR s)
  dls : ∀ r ∈ lsR s, (dR s).Disjoint r
  ed : (retR s).Disjoint (dR s)
  et : (retR s).Disjoint (tgR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tgR s)
  bds : (stkR s).Disjoint (dsR s)
  bls : ∀ r ∈ lsR s, (stkR s).Disjoint r
  ok : (K s).toNat + 32 ≤ 2 ^ 32
  on : (Nn s).toNat + 12 ≤ 2 ^ 32
  oa : (Ad s).toNat + AL s ≤ 2 ^ 32
  od : (Dst s).toNat + L s ≤ 2 ^ 32
  ot : (Tg s).toNat + 16 ≤ 2 ^ 32
  ods : (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32
  ol : ∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32
  w₁ : 824 ≤ (s.gpr .esp).toNat
  hgl : gl s (Cnt s) = L s
  hP : (Pf s).toNat + 88 ≤ 2 ^ 32
  hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48
  hBn : (Bs s).toNat + 864 ≤ 2 ^ 32
  hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 776
  hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 824
  sa : ∀ i, i < 9 → s.mem.readW (w64 (Pf s + BitVec.ofNat 32 (52 + 4 * i))) 32 = arg s i

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, -, nd, nt, -, ad, at_, -, dt, dds, dls, -, -, -, -, -, -, -, -, -, ed, et, -, -, -,
    bk, bn, ba, bd, bt, bds, bls, -, ok, on, oa, od, ot, ods, ol, w₁, w₂, hgl, -⟩ := hs
  have hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48 := sub_toNat32 (by omega_arith)
  have hB : Bs s = w64 (s.gpr .esp - BitVec.ofNat 32 824) := (w64_sub (by omega_arith)).symm
  have hBn : (Bs s).toNat = (s.gpr .esp).toNat - 824 := by rw [hB, toNat_w64, sub_toNat32 (by omega_arith)]
  have hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 824 := (BitVec.sub_add_cancel _ _).symm
  have hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 776 := by
    rw [w64_sub (by omega_arith), hE, add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, ed, et, bk, bn, ba, bd, bt, bds, bls, ok, on, oa, od, ot,
    ods, ol, w₁, hgl, by omega_arith, hPn, by omega_arith, hA0, hE, fun i hi => ?_⟩
  show _ = s.mem.readW (w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i))) 32
  rw [show 52 + 4 * i = 48 + (4 + 4 * i) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 824) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 824⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 88) : w64 (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (776 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 824⟩ := by
  show Region.Sub ⟨w64 (Pf s), 48⟩ _; rw [h.hA0]; exact stk_sub s 776 48 (by decide)

theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 828, 36⟩ := by
  show (⟨w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)), 36⟩ : Region) = _
  have := h.hPn
  have := h.hP
  rw [w64_add (by omega_arith), h.hE, Offset.add_ofNat_add_ofNat]

theorem argIn : argR s ∈ s.wr := by rw [h.wr]; simp

/-- The words of the arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 88) (rs : List Region) :
    InRegions (rs ++ s.wr) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_right _ h.argIn, by
    rw [h.hArg, h.hA (by omega_arith)]; exact contains_off _ (by omega_arith) (by omega_arith) (by omega_arith)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 48) (rs : List Region) :
    InRegions (FR s :: rs) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega_arith)]; exact Offset.contains_base _ h₂ (by omega_arith)⟩

theorem sa' (i d : Nat) (hi : i < 9) (hd : d = 52 + 4 * i) :
    s.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = arg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _ _

/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 824⟩) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.eM_frame x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (h.fr_sub x hc)

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 32 (w64 (Src s)) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 →
    s.mem x = eM s x := by
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bls r hr).symm

theorem hpt : Spec.Gcm.gathered 32 (eM s) (w64 (Src s)) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 4 ≤ 48) :
    (gM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
  rw [h.hA (by omega_arith)]
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact h.bd.sub_left (stk_sub s _ 4 (by omega_arith))

end Lay

/-! ## The phases -/

theorem covers_of_mem' {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩


/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  esi : e.gpr .esi = Src s
  ebx : e.gpr .ebx = arg s 5
  edx : e.gpr .edx = Dst s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .esp → e.gpr r = s.gpr r
  esp : e.gpr .esp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 48 s) (Entered s) := by
  have ae : (allocated 48 s).gpr .esp = Pf s := allocated_esp 48 s
  refine WP.mono (entry_ok (allocated 48 s) (by rw [ae]; exact h.hP)
      (fun d hd => by rw [ae, allocated_wr]; exact h.inFr d hd _)
      (fun d h₁ h₂ => by
        rw [ae, allocated_rd, allocated_wr, show s.rd ++ FR s :: s.wr = (s.rd ++ [FR s]) ++ s.wr by simp]
        exact h.inArg d h₁ h₂ _)) fun e ⟨me, esi, ebx, edx, ge, rde, wre⟩ => ?_
  rw [ae] at me esi ebx edx
  simp only [allocated_mem] at me esi ebx edx
  rw [allocated_gpr _ _ (by decide), allocated_gpr _ _ (by decide), allocated_gpr _ _ (by decide)] at me
  refine ⟨me, esi.trans (h.sa' 4 68 (by decide) rfl), ebx.trans (h.sa' 5 72 (by decide) rfl),
    edx.trans (h.sa' 6 76 (by decide) rfl), fun r hr hsp => ?_, ?_, rde, wre⟩
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₀, h₁, -, h₃, h₄, -⟩ := hr
    rw [ge r h₀ h₁ h₃ h₄, allocated_gpr _ _ hsp]
  · rw [ge _ (by decide) (by decide) (by decide) (by decide), ae]

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { esi := he.esi
          ebx := by rw [he.ebx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          edx := he.edx
          hcnt := (arg s 5).isLt
          dw := h.ods
          fitD := h.od
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact h.hgl
          dsr := covers_of_mem' (List.mem_append_left _ (by rw [he.rd, h.rd]; simp))
          lsr := fun r hr => covers_of_mem' (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd, h.rd]; simp [hr]))
          lfit := fun r hr => h.ol r (by rw [hls] at hr; exact hr)
          dw' := covers_of_mem' (by rw [he.wr, h.wr]; simp)
          dsd := h.dds.symm
          lsd := fun r hr => (h.dls r (by rw [hls] at hr; exact hr)).symm }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .esp → g.gpr r = s.gpr r
  esp : g.gpr .esp = Pf s
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hg hsp => (kg.gpr r hg).trans (he.gpr r hg hsp),
    (kg.gpr _ (by decide)).trans he.esp, kg.rd.trans he.rd, kg.wr.trans he.wr⟩

section
variable (s : State)

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes:
its arguments are the first 28 bytes of our frame. -/
abbrev rdC : List Region := [kR s, nR s, aR s]
abbrev wrC : List Region := [dR s, tgR s, ⟨Bs s + BitVec.ofNat 64 776, 28⟩]

end

section
variable {s g : State} (h : Lay s) (hg : Gathered s g)
include h hg

theorem Gathered.espN : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 48 := by rw [hg.esp]; exact h.hPn

/-- The callee's stack pointer, below its return address. -/
theorem Gathered.cesp (rd wr : List Region) :
    w64 ((g.callEntry.withRegions rd wr).gpr .esp) = Bs s + BitVec.ofNat 64 772 := by
  have := h.w₁
  have := h.hPn
  simp only [State.withRegions_gpr, State.callEntry_esp, hg.esp]
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, w64_sub (by omega_arith), h.hA0, add_ofNat_sub_ofNat _ (by decide)]

theorem Gathered.cargAddr (rd wr : List Region) :
    argAddr (g.callEntry.withRegions rd wr) 0 = Bs s + BitVec.ofNat 64 776 := by
  have e : argAddr (g.callEntry.withRegions rd wr) 0 = argAddr g.callEntry 0 := rfl
  rw [e, argAddr_callEntry, hg.esp, Nat.mul_zero, add_zero32]; exact h.hA0

/-- The callee's arguments: words of our frame. -/
theorem Gathered.args (rd wr : List Region) :
    let c := g.callEntry.withRegions rd wr
    arg c 0 = K s ∧ arg c 1 = Nn s ∧ arg c 2 = Ad s ∧ arg c 3 = arg s 3 ∧ arg c 4 = Dst s ∧ arg c 5 = arg s 7 ∧
      arg c 6 = Tg s := by
  have := h.w₁
  have := h.hP
  have := h.hPn
  have e (j : Nat) (hj : j < 7) : arg (g.callEntry.withRegions rd wr) j =
      (eM s).readW (w64 (Pf s + BitVec.ofNat 32 (4 * j))) 32 := by
    show arg g.callEntry j = _
    rw [arg_callEntry (by rw [hg.esp]; omega_arith) (by rw [hg.esp]; omega_arith), hg.mem, hg.esp,
      h.gFrame (4 * j) (by omega_arith)]
  obtain ⟨w0, w4, w8, w12, w16, w20, w24, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), Nat.mul_zero, add_zero32]; exact w0.trans (h.sa' 0 52 (by decide) rfl)
  · rw [e 1 (by decide)]; exact w4.trans (h.sa' 1 56 (by decide) rfl)
  · rw [e 2 (by decide)]; exact w8.trans (h.sa' 2 60 (by decide) rfl)
  · rw [e 3 (by decide)]; exact w12.trans (h.sa' 3 64 (by decide) rfl)
  · rw [e 4 (by decide)]; exact w16.trans (h.sa' 6 76 (by decide) rfl)
  · rw [e 5 (by decide)]; exact w20.trans (h.sa' 7 80 (by decide) rfl)
  · rw [e 6 (by decide)]; exact w24.trans (h.sa' 8 84 (by decide) rfl)

/-- What the call needs. -/
theorem Gathered.call :
    callPre (g.callEntry.withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (g.rd ++ g.wr) ∧
      Covers (wrC s) g.wr := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hg.args h (rdC s) (wrC s)
  have cesp := hg.cesp h (rdC s) (wrC s)
  have carg := hg.cargAddr h (rdC s) (wrC s)
  have hesp := hg.espN h
  have := h.w₁
  have := h.hP
  have := h.hBn
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, a0, a1, a2, a3, a4, a5, a6, cesp, carg,
      BitVec.add_sub_cancel]
    have espc : ((g.callEntry.withRegions (rdC s) (wrC s)).gpr .esp).toNat = (s.gpr .esp).toNat - 52 := by
      simp only [State.withRegions_gpr, State.callEntry_esp]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat32 (by omega_arith), hesp]; omega_arith
    have stkArg : (⟨Bs s, 772⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 776, 28⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 772) (e := 776) (k := 28) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    have retArg : (⟨Bs s + BitVec.ofNat 64 772, 4⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 776, 28⟩ :=
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    have sb (d n : Nat) (hd : d + n ≤ 824) {r : Region} (hr : (stkR s).Disjoint r) :
        (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
    refine ⟨by omega_arith, by omega_arith, trivial, trivial, h.kd, h.kt, (sb 776 28 (by decide) h.bk).symm, h.nd, h.nt,
      (sb 776 28 (by decide) h.bn).symm, h.ad, h.at_, (sb 776 28 (by decide) h.ba).symm, h.dt,
      (sb 776 28 (by decide) h.bd).symm, (sb 776 28 (by decide) h.bt).symm,
      sb 772 4 (by decide) h.bk, sb 772 4 (by decide) h.bn, sb 772 4 (by decide) h.ba,
      sb 772 4 (by decide) h.bd, sb 772 4 (by decide) h.bt, retArg,
      h.bk.sub_left (Region.sub_prefix (by decide)), h.bn.sub_left (Region.sub_prefix (by decide)),
      h.ba.sub_left (Region.sub_prefix (by decide)), h.bd.sub_left (Region.sub_prefix (by decide)),
      h.bt.sub_left (Region.sub_prefix (by decide)), stkArg, h.ok, h.on, h.oa, h.od, h.ot⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (g.rd ++ g.wr) := by
      refine covers_of_mem' (List.mem_append_left _ ?_)
      rw [hg.rd, h.rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 776, 48⟩] (g.rd ++ g.wr) := by
      rw [← h.hA0]; exact covers_of_mem' (List.mem_append_right _ (by rw [hg.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (g.rd ++ g.wr) :=
      covers_of_mem' (List.mem_append_right _ (by
        rw [hg.wr, h.wr]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
        rcases h' with rfl | rfl <;> simp))
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hw' (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hw' (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hfr a n ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  · intro a n ⟨r, hr, hc⟩
    rw [hg.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, hc⟩
    · exact ⟨_, by simp, hc⟩
    · refine ⟨FR s, List.mem_cons_self .., ?_⟩
      show Region.Contains ⟨w64 (Pf s), 48⟩ a n
      rw [h.hA0]; simp only [Region.Contains] at hc ⊢; omega_arith

end

/-- After the call. -/
structure Called (s z : State) : Prop where
  ebx : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 36)) 32 = s.gpr .ebx
  esi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 40)) 32 = s.gpr .esi
  edi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 44)) 32 = s.gpr .edi
  ret : z.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32
  out : encrypt (bytesAt (gM s) (w64 (K s)) 32) (bytesAt (gM s) (w64 (Nn s)) 12)
      (bytesAt (gM s) (w64 (Ad s)) (AL s)) (bytesAt (gM s) (w64 (Dst s)) (L s)) =
    (bytesAt z.mem (w64 (Dst s)) (L s), bytesAt z.mem (w64 (Tg s)) 16)
  ebp : z.gpr .ebp = s.gpr .ebp
  esp : z.gpr .esp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (F : SealFn) {s g : State} (h : Lay s) (hg : Gathered s g) :
    WP isa (.call F.name F.code) g (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hg.call h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hg.args h (rdC s) (wrC s)
  have hdep := F.depth
  have hesp := hg.espN h
  have := h.w₁
  have := h.hBn
  have e4 : w64 (g.gpr .esp - 4) = Bs s + BitVec.ofNat 64 772 := by
    have := hg.cesp h (rdC s) (wrC s)
    simpa only [State.withRegions_gpr, State.callEntry_esp] using this
  refine WP.call F.verified.1 F.noSp (by omega_arith) (sealSpec_pre hcp) hcov hw
    fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, _, post'⟩ => ?_
  have hpost := sealSpec_post post'
  rw [a0, a1, a2, a3, a4, a5, a6, m₂] at hpost
  -- The callee's memory on entry: ours, with its return address below our frame.
  have fc : Frame [⟨Bs s + BitVec.ofNat 64 772, 4⟩] g.mem (g.callEntry.withRegions (rdC s) (wrC s)).mem := by
    show Frame _ g.mem (g.mem.writeW (w64 (g.gpr .esp - 4)) (g.unknowns 0))
    rw [e4]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have apart {r : Region} (hr : (stkR s).Disjoint r) :
      ∀ r' ∈ [(⟨Bs s + BitVec.ofNat 64 772, 4⟩ : Region)], r.Disjoint r' := by
    intro r' hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact (hr.sub_left (stk_sub s 772 4 (by decide))).symm
  rw [bytesAt_frame fc (apart h.bk) (by omega_arith), bytesAt_frame fc (apart h.bn) (by omega_arith),
    bytesAt_frame fc (apart h.ba) (by have := h.oa; omega_arith), bytesAt_frame fc (apart h.bd) (by have := h.od; omega_arith),
    hg.mem] at hpost
  -- What the call kept: the frame above its arguments, and our return address.
  have hbelow : below (g.gpr .esp) (stackUse F.code + 4) =
      ⟨Bs s + BitVec.ofNat 64 (776 - (stackUse F.code + 4)), stackUse F.code + 4⟩ := by
    show (⟨w64 (g.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)), _⟩ : Region) = _
    rw [w64_sub (by omega_arith), hg.esp, h.hA0, add_ofNat_sub_ofNat _ (by omega_arith)]
  have kept (d : Nat) (h₁ : 812 ≤ d) (h₂ : d + 4 ≤ 824 ∨ d = 824) :
      s'.mem.readW (Bs s + BitVec.ofNat 64 d) 32 = g.mem.readW (Bs s + BitVec.ofNat 64 d) 32 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · by_cases hd : d + 4 ≤ 824
      · exact (h.bd.sub_left (stk_sub s d 4 hd)).symm.symm
      · have e : Bs s + BitVec.ofNat 64 d = w64 (s.gpr .esp) := by
          rw [h.hE, show d = 824 by omega_arith]
        rw [e]; exact h.ed
    · by_cases hd : d + 4 ≤ 824
      · exact (h.bt.sub_left (stk_sub s d 4 hd)).symm.symm
      · have e : Bs s + BitVec.ofNat 64 d = w64 (s.gpr .esp) := by
          rw [h.hE, show d = 824 by omega_arith]
        rw [e]; exact h.et
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain ⟨-, -, -, -, -, -, -, w36, w40, w44⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)
  have saved (d : Nat) (hd : 36 ≤ d) (hd' : d + 4 ≤ 48) :
      s'.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [← h.gFrame d hd', ← hg.mem, h.hA (by omega_arith), kept _ (by omega_arith) (.inl (by omega_arith))]
  refine ⟨(saved 36 (by decide) (by decide)).trans w36, (saved 40 (by decide) (by decide)).trans w40,
    (saved 44 (by decide) (by decide)).trans w44, ?_, hpost, ?_, ?_, rd'.trans hg.rd, wr'.trans hg.wr⟩
  · -- The return address: neither the entry, nor the copy, nor the call wrote it.
    rw [h.hE, kept 824 (by decide) (.inr rfl), hg.mem, ← h.hE]
    rw [h.frame_gM.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ed) (by decide)]
    refine h.eM_frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint ⟨w64 (s.gpr .esp), 4⟩ ⟨w64 (Pf s), 48⟩
    rw [h.hE, h.hA0]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by omega_arith)
  · rw [cs' .ebp (by decide), hg.gpr .ebp (by decide) (by decide)]
  · rw [cs' .esp (by decide), hg.esp]

/-- Our caller's registers back from the frame, and the frame freed. -/
theorem ret_wp {s z : State} (h : Lay s) (hz : Called s z) :
    WP isa (.block restore) z fun z' => ∀ m u, Frame [below (s.gpr .esp) 48] z'.mem m →
      abiPreserved s { freed 48 z' with mem := m, unknowns := u } ∧
        gatherPost s { freed 48 z' with mem := m, unknowns := u } := by
  have hr (d : Nat) (hd : d + 4 ≤ 48) : InRegions (z.rd ++ z.wr) (w64 (z.gpr .esp + BitVec.ofNat 32 d)) 4 := by
    rw [hz.esp, hz.wr]
    obtain ⟨r, hr, hc⟩ := h.inFr d hd s.wr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.of_runBlock ⟨_, by xrun [restore, sp, hr 36 (by decide), hr 40 (by decide), hr 44 (by decide)],
    fun m u fl => ?_⟩
  obtain hfr : ∀ {r : Region}, (stkR s).Disjoint r → ∀ r' ∈ [below (s.gpr .esp) 48], r.Disjoint r' :=
    fun h₁ r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'
      exact h₁.symm.sub_right h.fr_sub
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [freed]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simp [gpr_setReg, hz.esp, hz.ebx]
    · simp [gpr_setReg, hz.esp, hz.esi]
    · simp [gpr_setReg, hz.esp, hz.edi]
    · simp [gpr_setReg, hz.ebp]
    · simp [gpr_setReg, hz.esp]; exact BitVec.sub_add_cancel _ _
  · show m.readW _ _ = _
    rw [fl.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      show Region.Disjoint ⟨w64 (s.gpr .esp), 4⟩ ⟨w64 (Pf s), 48⟩
      rw [h.hE, h.hA0]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by omega_arith)) (by decide)]
    simp only [freed, mem_setReg]; exact hz.ret
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt m (w64 (Dst s)) (L s), bytesAt m (w64 (Tg s)) 16)
    rw [bytesAt_frame fl (hfr h.bd) (by have := h.od; omega_arith), bytesAt_frame fl (hfr h.bt) (by decide)]
    show encrypt _ _ _ _ = (bytesAt z.mem (w64 (Dst s)) (L s), bytesAt z.mem (w64 (Tg s)) 16)
    have hfc : Frame [FR s, dR s] s.mem (gM s) :=
      (h.eM_frame.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right h.fr_sub
      · exact h₂
    have hk : bytesAt (gM s) (w64 (K s)) 32 = bytesAt s.mem (w64 (K s)) 32 :=
      bytesAt_frame hfc (apart h.bk h.kd) (by omega_arith)
    have hn : bytesAt (gM s) (w64 (Nn s)) 12 = bytesAt s.mem (w64 (Nn s)) 12 :=
      bytesAt_frame hfc (apart h.bn h.nd) (by omega_arith)
    have ha : bytesAt (gM s) (w64 (Ad s)) (AL s) = bytesAt s.mem (w64 (Ad s)) (AL s) :=
      bytesAt_frame hfc (apart h.ba h.ad) (by have := h.oa; omega_arith)
    have hd : bytesAt (gM s) (w64 (Dst s)) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; have := h.od; omega_arith)
    have := hz.out
    rw [hk, hn, ha, hd] at this
    exact this

/-- The body of the frame never writes `esp`. -/
theorem body_noSp (F : SealFn) :
    NoSp (.seq (.block entry) (.seq gather (.seq (.call F.name F.code) (.block restore))) :
      Prog isa) := by
  have he : NoSp (.block entry : Prog isa) := NoSp.of_all (by decide +kernel)
  have hg : NoSp gather := NoSp.of_all (by decide +kernel)
  have hr : NoSp (.block restore : Prog isa) := NoSp.of_all (by decide +kernel)
  intro i hi
  simp only [instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi | hi
  exacts [he i hi, hg i hi, F.noSp i hi, hr i hi]

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega_arith) (body_noSp F) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (called_wp F h hg) fun z hz => ?_)
  exact ret_wp h hz

end VG.Proof.ChaCha20Poly1305.X86.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and descriptors agree (`gatherPub`) leak the same trace, related
piece by piece from given states (`Eq2`,
`Proof/AesGcm/X86/Gather/LoopCT.lean`): the frame's words and our arguments
are read and written at `esp`, the same in both runs (the taint analysis
from `esp`); the gathering is constant time by `gather_rel`; and the call is
constant time by its callee's contract, whose public arguments agree
(`sealGather_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86.SealGather
open VG.Proof.AesGcm.X86 (w64)
open VG.Proof.AesGcm.X86.Gather (rel_alloc gather_rel)
open VG.X86 (Eq2 TT rel_seq rel_taint ct_of)

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, qa, hdesc⟩ := hq
  have a (i : Nat) (hi : i < 9) := qa i hi
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_taint [.esp] (by simp [hP]) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← a 4 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide)] at g₂
  have hd : ∀ j < Cnt σ₁ * 8,
      e₁.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) = e₂.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
    have hx₂ : (dsR σ₂).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← a 4 (by decide), ← a 5 (by decide)]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE h₁.bds.symm hx, h₂.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂) fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, ← a 0 (by decide), ← a 1 (by decide), ← a 2 (by decide),
      ← a 3 (by decide)]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, Bs, ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide), qsp]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hg₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hg₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨s0₁, s1₁, s2₁, s3₁, s4₁, s5₁, s6₁⟩ := hg₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂, s3₂, s4₂, s5₂, s6₂⟩ := hg₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, fun i hi => ?_⟩, cv₁, cw₁, cv₂, cw₂,
        by rw [hg₁.esp, hg₂.esp, hP]⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, hg₁.esp, hg₂.esp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a 0 (by decide)
        · rw [s1₁, s1₂]; exact a 1 (by decide)
        · rw [s2₁, s2₂]; exact a 2 (by decide)
        · rw [s3₁, s3₂]; exact a 3 (by decide)
        · rw [s4₁, s4₂]; exact a 6 (by decide)
        · rw [s5₁, s5₂]; exact a 7 (by decide)
        · rw [s6₁, s6₂]; exact a 8 (by decide))
    (called_wp F h₁ hg₁) (called_wp F h₂ hg₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- Our caller's registers back.
  exact rel_taint [.esp] (by simp [hz₁.esp, hz₂.esp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20Poly1305.X86.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 824 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherX86`, `gather_implies`), and so the code, calling an
instance of `vg_chacha20_poly1305_seal` by its shared contract (`sealFn`), is
`Verified` against it (`sealGather_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86.SealGather
open VG.Proof.AesGcm.X86 (w64 toNat_w64)
open VG.Proof.AesGcm.X86.Gather (sw32)

theorem sealGather_correct (F : SealFn) (s : State) (hs : gatherX86.pre s) :
    ∃ t s', Exec isa (sealGather F.name F.code) s t s' ∧ abiPreserved s s' ∧ gatherX86.post s s' := by
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

/-- The pairs of the slices, read only, and the arguments, writable. -/
theorem pairFacts_ro_w (l : List Region) (a : Region) :
    Sig.conj (Sig.pairFacts (l.map (fun r => (r, false)) ++ [(a, true)])) ↔ ∀ r ∈ l, r.Disjoint a := by
  induction l with
  | nil => simp [Sig.pairFacts, Sig.conj]
  | cons r l ih =>
    simp only [List.map_cons, List.cons_append, Sig.pairFacts, List.filterMap_append, List.filterMap_map,
      Function.comp_def, Bool.false_or, Sig.conj_append, ih, List.forall_mem_cons]
    simp [List.filterMap_cons, Sig.conj, Sig.conj_cons, filterMap_none']

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86.abi] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append, List.append_nil,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons, Sig.pairFacts, argBytes, argVal, ↓reduceIte, Nat.reduceEqDiff,
    Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64, List.append_eq,
    pairFacts_ro_w] at *
  rename_i w₁ w₂ hrd hwr kd pw ek en ea ed et bl ok on oa od ot fl hgl
  obtain ⟨kt, karg, nd, nt, narg, ad, at_, aarg, dt, dds, ⟨dls, darg⟩, tds, ⟨tls, targ⟩, dsarg, lsarg⟩ := pw
  obtain ⟨eds, ⟨els, earg⟩, bk, bn, ba, bd, bt, bds, bls, barg⟩ := bl
  obtain ⟨ods, ol⟩ := fl
  exact ⟨hrd, hwr, kd, kt, karg, nd, nt, narg, ad, at_, aarg, dt, dds, dls, darg, tds, tls, targ, dsarg, lsarg,
    ek, en, ea, ed, et, eds, els, earg, bk, bn, ba, bd, bt, bds, bls, barg, ok, on, oa, od, ot, ods, ol, w₁,
    by omega_using [w₂], hgl, h⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv,
    List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv,
    List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64] at hp
  obtain ⟨qsp, a0, a1, a2, a3, a4, a5, a6, a7, a8, hd⟩ := hp
  refine ⟨qsp, fun i hi => ?_, hd⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [hi]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8]

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; its nine argument slots at `0x8004`. -/
def gatherSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x8005 then 0x10 else bif Nat.beq a.toNat 0x8009 then 0x20 else bif Nat.beq a.toNat 0x800d then 0x30
    else bif Nat.beq a.toNat 0x8015 then 0x40 else bif Nat.beq a.toNat 0x801d then 0x41 else bif Nat.beq a.toNat 0x8025 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x4100, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 36⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [gatherSat, X86.arg, X86.argAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherX86.Implies (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified (F : SealFn) :
    Verified X86.target (sealGather F.name F.code) (Spec.ChaCha20Poly1305.sealGatherContract X86.abi 824) :=
  Verified.of_correct (k := gatherX86) (sealGather_correct F) (sealGather_ct F) gather_implies

open VG.Proof.ChaCha20.X86 VG.Impl.StackScratch.X86 in
/-- The instance of `vg_chacha20_poly1305_seal` calling the implementation
`v` of `vg_chacha20_xor`, with its working space in a frame of its own. -/
def sealFn (v : XorImpl) : SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
  code := withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee)
  verified := Proof.ChaCha20Poly1305.X86.seal_framed v
  noSp := by
    have hs := NoSp.of_all (Proof.ChaCha20Poly1305.X86.seal_noEsp v)
    have ha : NoSp (.block (setArgs 740 7) : Prog isa) := NoSp.of_all (by decide +kernel)
    have hw : NoSp (.block (wipe (8 + 4 * 7) 176) : Prog isa) := NoSp.of_all (by decide +kernel)
    intro i hi
    simp only [withStackScratchWiped, withStackScratch, instrs, List.mem_cons, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi | hi | hi) | rfl
    · rfl
    · exact ha i hi
    · exact hs i hi
    · exact hw i hi
    · rfl
  depth := by
    have := Proof.ChaCha20Poly1305.X86.seal_stackUse v
    simp only [withStackScratchWiped, withStackScratch, stackUse, frameBytes, Nat.zero_max, Nat.max_zero]
    exact Nat.le_trans (Nat.add_le_add_right this 740) (by decide)

open VG.Proof.ChaCha20.X86 in
/-- No instruction of the code, or of the instance it calls, writes `esp`
but its frames' push and pop. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGather (sealFn v).name (sealFn v).code).all (fun i => !X86.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86.isa.writesSp i) = true :=
    Proof.ChaCha20Poly1305.X86.withStackScratchWiped_spSafe
      (Proof.ChaCha20Poly1305.X86.seal_spSafe v)
  have he : (Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) = true := by decide +kernel
  have hg : Impl.AesGcm.X86.SealGather.gather.all (fun i => !X86.isa.writesSp i) = true := by decide +kernel
  have hr : (Code.block Impl.AesGcm.X86.SealGather.restore : Prog isa).all (fun i => !X86.isa.writesSp i) = true :=
    by decide +kernel
  show (!X86.isa.writesSp (.alloc 48) && ((Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) &&
      (Impl.AesGcm.X86.SealGather.gather.all (fun i => !X86.isa.writesSp i) &&
        ((sealFn v).code.all (fun i => !X86.isa.writesSp i) &&
        (Code.block Impl.AesGcm.X86.SealGather.restore : Prog isa).all (fun i => !X86.isa.writesSp i)))) &&
      !X86.isa.writesSp (.free 48)) = true
  rw [he, hg, hc, hr]; rfl

end VG.Proof.ChaCha20Poly1305.X86.Gather

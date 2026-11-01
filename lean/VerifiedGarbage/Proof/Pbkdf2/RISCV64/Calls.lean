module

public import VerifiedGarbage.Impl.Pbkdf2.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# PBKDF2-HMAC's iteration on RISC-V: the contracts

Untrusted: the contracts the proof is written against.

* `cmpK H CW` is the RISC-V contract of a compression function of the
  Merkle–Damgård hash function `H` (any `Md`, of 64- or 128-byte blocks),
  with `CW` bytes of scratch space: SHA-256's, SHA-512's, MD5's and SHA-1's
  contracts imply it (`CalleeOk`).
* `OutOk H D out` is what the iteration needs of the code writing the digest
  (`It.out`).
* `iterK S Wi` is the iteration's: `Proof.Pbkdf2.iterateContract` of the
  streaming hash function `S` with `Wi` bytes of scratch space, on RISC-V,
  with no stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd wp_mv wp_li)
open VG.Impl.Pbkdf2.RISCV64 (It mov)
open VG.Proof.MdStream (Md)
open VG.WriteBytes (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

variable {B N L : Nat}

/-- `compress(state, blocks, n, scratch)` of `H`: compresses the `n` blocks at
`blocks` into the `N`-byte hash value at `state`. -/
def cmpK (H : Md B N L) (CW : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, N⟩
    let blocks : Region := ⟨s.gpr .a1, B * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, CW⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .a0) = H.compressBlocks (H.stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1)
      (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- What the iteration needs of the compression function it calls: that it
is correct, and pushes no frames. -/
structure CalleeOk (H : Md B N L) (CW : Nat) (code : Prog isa) : Prop where
  verified : ∀ s, (cmpK H CW).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (cmpK H CW).post s s'
  noFrames : code.noFrames = true

/-- The code writing the digest: the first `D` bytes of the digest of the
hash value at `s1`, to `s3`, writing only `t1`, `t2` and `t4`. -/
def OutOk (H : Md B N L) (D : Nat) (out : List Instr) : Prop :=
  ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .s1) N → InRegions s.wr (s.gpr .s3) D →
    Region.Disjoint ⟨s.gpr .s1, N⟩ ⟨s.gpr .s3, D⟩ →
    WP isa (.block out) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((H.digest (H.stateAt s.mem (s.gpr .s1))).take D)

/-- The iteration's contract, with `Wi` bytes of scratch space and no stack. -/
def iterK (S : StreamingHash) (Wi : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .a1, S.digestBytes⟩
    let t : Region := ⟨s.gpr .a3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .a4, Wi⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch
  post s s' := ∀ k0, k0.length = S.H.blockSize → S.Repr s.mem (s.gpr .a0) (xorPad k0 ipad) →
    S.Repr s.mem (s.gpr .a0 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .a3) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) ((s.gpr .a2).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .a1) S.digestBytes) (bytesAt s.mem (s.gpr .a3) S.digestBytes)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- Compressing the block at `s3` into the hash value at `s1`, with scratch
space at `s2`: the callee-saved registers are kept. -/
theorem compressAt_ok {H : Md B N L} {CW : Nat} {P : It} (hf : CalleeOk H CW P.cmpC)
    {s : State} {st scr src : Addr}
    (h1 : s.gpr .s1 = st) (h2 : s.gpr .s2 = scr) (h3 : s.gpr .s3 = src)
    (d₁ : Region.Disjoint ⟨st, N⟩ ⟨scr, CW⟩) (d₂ : Region.Disjoint ⟨src, B⟩ ⟨st, N⟩)
    (d₃ : Region.Disjoint ⟨src, B⟩ ⟨scr, CW⟩)
    (hc : RISCV64.Covers [⟨src, B⟩, ⟨st, N⟩, ⟨scr, CW⟩] (s.rd ++ s.wr))
    (hw : RISCV64.Covers [⟨st, N⟩, ⟨scr, CW⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, CW⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa P.compressAt s Q := by
  unfold It.compressAt mov
  refine WP.seq (wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_li (imm := 1) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => WP.block_nil ?_)
  have e0 : s₄.gpr .a0 = st := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
  have e1 : s₄.gpr .a1 = src := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h3]
  have e2 : s₄.gpr .a2 = BitVec.ofNat 64 1 := by
    rw [u₄.other _ (by decide), u₃.gpr]
  have e3 : s₄.gpr .a3 = scr := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h2]
  have keep : ∀ r ∈ preserved, s₄.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
      revert r; decide
    rw [u₄.other _ this.2.2.2, u₃.other _ this.2.2.1, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₄ : s₄.sp = s.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₄.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₄.callEntry.gpr .a1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₄.callEntry.gpr .a2 = BitVec.ofNat 64 1 :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₄.callEntry.gpr .a3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := cmpK H CW) hf.verified
    (rd := [⟨src, B * 1⟩]) (wr := [⟨st, N⟩, ⟨scr, CW⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [cmpK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat, Nat.mul_one]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₄, wr₄]; simpa using hc
  · rw [wr₄]; exact hw
  · intro s' hrd hwr hsp hf' hcs _ hpost
    simp only [cmpK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, Md.compressBlocks_one, m₄] at hpost
    exact hQ s' (hrd.trans rd₄) (hwr.trans wr₄) (fun r hr => (hcs r hr).trans (keep r hr))
      (hsp.trans sp₄) (m₄ ▸ hf') hpost

end VG.Proof.Pbkdf2.RISCV64

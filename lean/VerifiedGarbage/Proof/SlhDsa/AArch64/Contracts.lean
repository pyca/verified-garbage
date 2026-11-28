module

public import VerifiedGarbage.Proof.SlhDsa.Internal
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Contract
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Layout

/-!
# SLH-DSA (SHAKE) on AArch64: the contracts of the internal functions

Untrusted: only verified code calls these functions
(`Impl/SlhDsa/AArch64/`), so their contracts are the callers' proofs'
business. They are x86-64's (`Proof/SlhDsa/X86_64/Contracts.lean`) in
AAPCS64's registers: each function takes the working space `scratch` in
`x0` (`S`), 64 KiB laid out as `Impl/SlhDsa/AArch64/Layout.lean` says, and
the caller has set up in it what `Env` says: `SK.seed` (but for
verification), and in every lane `PK.seed` and the layer and tree addresses
`a16` of the tree. There is no table of round constants (the two-way
permutation reads its own). Each may change the parts of `scratch` that its
changes list, and its output buffer, and keeps the rest, `Env` with it, as
it was. None uses the stack: their calls (`bl`) store nothing there, and
each keeps its return address in its frame in `scratch` (`Layout.oFrame`).

What a function keeps across its calls is outside their changes: its saved
registers in its own frame (frame 0 is `wotsLeaves4`'s, 1 `xmssTree`'s and
`xmssPk`'s, 2 `forsSign`'s and `forsPk`'s, 3 `levels`'), its public values in
callee-saved registers (`x19`–`x27`, which every callee restores), and what
the functions the Rust code calls keep at `oTop`, the keys, the digest and
the sponge's state, which no internal function changes.

The values are the specification's (`Spec/SlhDsa.lean`), through the
definitions of `Proof/SlhDsa/Internal.lean`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)

variable (p : Params)

/-- The size of `scratch`. -/
def scratchLen : Nat := 65536

/-- `S + o`. -/
abbrev at' (S : Addr) (o : Nat) : Addr := S + BitVec.ofNat 64 o

/-- What the caller has set up in `scratch` at `S`, in the memory `m`: in
each of the eight lanes `PK.seed` then the tree's 16 bytes `a16`. -/
structure Env (m : Mem) (S : Addr) (pkSeed a16 : List Byte) : Prop where
  seedA : ∀ k < 4, bytesAt m (at' S (Layout.laneA k)) p.n = pkSeed
  seedB : ∀ k < 4, bytesAt m (at' S (Layout.laneB k)) p.n = pkSeed
  adrsA : ∀ k < 4, bytesAt m (at' S (Layout.laneA k + p.n)) 16 = a16
  adrsB : ∀ k < 4, bytesAt m (at' S (Layout.laneB k + p.n)) 16 = a16

/-- `SK.seed` at its place. -/
def SkAt (m : Mem) (S : Addr) (skSeed : List Byte) : Prop := bytesAt m (at' S Layout.oSkSeed) p.n = skSeed

/-- The lanes but their `PK.seed` and `a16`: from byte `n + 16` of each. -/
def laneTails (S : Addr) : List Region :=
  (List.range 4).flatMap (fun k =>
    [⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩,
      ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩])

/-- The parts of `scratch` the internal functions may change: what
`thash4` writes of its work, the frames, the lanes but their `PK.seed` and
`a16`, the digits, the nodes, the subtree roots, the message, the FORS
indices. Not `oTop`, the keys, the digest or the sponge's state. -/
def changes (S : Addr) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S Layout.oVars, 4 * Layout.frameLen⟩] ++ laneTails p S ++
  [⟨at' S Layout.oDigits, 128⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨at' S Layout.oRoots, 1024⟩,
    ⟨at' S Layout.oMsg, 64⟩, ⟨at' S Layout.oFidx, 320⟩]

/-- The regions of a function with `scratch` at `S`, the writable buffer
`out` (outside the part of `scratch` below `oSigTmp`, which it may be
after) and the read-only `rd`, at the state `s`. -/
structure Regions (s : State) (S : Addr) (rd : List Region) (out : Region) : Prop where
  rd_eq : s.rd = rd
  wr_eq : s.wr = [⟨S, scratchLen⟩, out]
  scr_fit : S.toNat + scratchLen ≤ 2 ^ 64
  out_fit : out.base.toNat + out.len ≤ 2 ^ 64
  out_scr : out.Disjoint ⟨S, Layout.oSigTmp⟩
  rd_fit : ∀ r ∈ rd, r.base.toNat + r.len ≤ 2 ^ 64
  rd_scr : ∀ r ∈ rd, r.Disjoint ⟨S, scratchLen⟩

/-! ## `wotsLeaves4(scratch = x0, kp = x1, idx = x2, sig = x3)` -/

/-- The digit `i` at `oDigits`. -/
def digitAt (m : Mem) (S : Addr) (i : Nat) : Nat := (m (at' S (Layout.oDigits + i))).toNat

/-- What `wotsLeaves4` may change in `scratch`, for the key pairs from `kp`:
what `thash4` writes of its work, frame 0, the lanes but their `PK.seed` and
`a16`, and the four nodes. -/
def wotsChanges (S : Addr) (kp : Nat) : List Region :=
  [⟨S, workUsed⟩, ⟨at' S (Layout.oFrame 0), Layout.frameLen⟩] ++ laneTails p S ++
  [⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩]

def wots4Contract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    Regions s S [] ⟨s.gpr .x3, p.len * p.n⟩ ∧
      (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .x1).toNat % 4 = 0 ∧ ((s.gpr .x1).toNat + 4) * p.n ≤ 32 * Layout.nodeSlots ∧
      (s.gpr .x2).toNat < 2 ^ 32 ∧ ∀ i < p.len, digitAt s.mem S i < 16
  post s s' :=
    let S := s.gpr .x0
    let kp := (s.gpr .x1).toNat
    let idx := (s.gpr .x2).toNat
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      Env p s'.mem S pkSeed a16 ∧
      (∀ k < 4, bytesAt s'.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      (kp ≤ idx ∧ idx < kp + 4 → ∀ i < p.len,
        bytesAt s'.mem (s.gpr .x3 + BitVec.ofNat 64 (i * p.n)) p.n =
          wotsChainAt p skSeed pkSeed a16 idx i (digitAt s.mem S i)) ∧
      (¬ (kp ≤ idx ∧ idx < kp + 4) → bytesAt s'.mem (s.gpr .x3) (p.len * p.n) = bytesAt s.mem (s.gpr .x3) (p.len * p.n)) ∧
      Frame (wotsChanges p S kp ++ [⟨s.gpr .x3, p.len * p.n⟩]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-! ## `levels(scratch = x0, nodes = x1, count = x2, z₀ = x3, auth = x4, idx = x5)`

With frame 3's variables 0 to 3 `capBase`, `adrsBase`, `type` and `kp`
(`Tree.setParams`); `count = 2^h` for the number `h` of heights. Every
caller's nodes are at `oN` (FORS copies its subtrees' roots there first). -/

/-- Variable `i` of frame `f`, as the caller stored it. -/
def varAt (m : Mem) (S : Addr) (f i : Nat) : BitVec 64 := m.readW (at' S (Layout.oVar f i)) 64

/-- The `c` nodes at `a`. -/
def nodesAt (m : Mem) (a : Addr) (c : Nat) : List (List Byte) :=
  (List.range c).map fun i => bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n

/-- The number of heights `levels` computes, `h` for `count = 2^h`. -/
def heightsOf (s : State) : Nat := (s.gpr .x2).toNat.log2

/-- What `levels` may change in `scratch`, for `count` nodes at `nodes`:
what `thash4` writes of its work, frame 3, the fields and messages of the
lanes `A`, and the nodes, with the 8 after them. -/
def levelsChanges (S nodes : Addr) (count : Nat) : List Region :=
  (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
  [⟨S, workUsed⟩, ⟨at' S (Layout.oFrame 3), Layout.frameLen⟩, ⟨nodes, (count + 8) * p.n⟩]

def levelsContract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    let h := heightsOf s
    Regions s S [] ⟨s.gpr .x4, h * p.n⟩ ∧
      (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      s.gpr .x1 = at' S Layout.oN ∧
      1 ≤ h ∧ (s.gpr .x3).toNat + h ≤ 14 ∧ (s.gpr .x2).toNat = 2 ^ h ∧
      ((s.gpr .x2).toNat + 8) * p.n ≤ 32 * Layout.nodeSlots ∧
      (s.gpr .x5).toNat < 2 ^ 32 ∧ (varAt s.mem S 3 0).toNat < 2 ^ 32 ∧ (varAt s.mem S 3 1).toNat < 2 ^ 32 ∧
      (varAt s.mem S 3 2).toNat < 2 ^ 32 ∧ (varAt s.mem S 3 3).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .x0
    let z₀ := (s.gpr .x3).toNat
    let h := heightsOf s
    let auth := s.gpr .x4
    let L := nodesAt p s.mem (s.gpr .x1) (s.gpr .x2).toNat
    let up := upNodes p
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      let ty := (varAt s.mem S 3 2).toNat
      let kp := (varAt s.mem S 3 3).toNat
      let base := (varAt s.mem S 3 1).toNat
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (s.gpr .x1) p.n = (up pkSeed a16 ty kp base z₀ L h).getD 0 [] ∧
      (∀ r < h, bytesAt s'.mem (auth + BitVec.ofNat 64 (r * p.n)) p.n =
        xorB (bytesAt s.mem (auth + BitVec.ofNat 64 (r * p.n)) p.n)
          (pick p.n (up pkSeed a16 ty kp base z₀ L r) ((varAt s.mem S 3 0).toNat / 2 ^ (z₀ + r))
            (s.gpr .x5).toNat (z₀ + r))) ∧
      Frame (levelsChanges p S (s.gpr .x1) (s.gpr .x2).toNat ++ [⟨auth, h * p.n⟩]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-! ## `xmssTree(scratch = x0, idx = x1, sig = x2)` -/

def xmssContract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    Regions s S [] ⟨s.gpr .x2, p.xmssSigLen⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .x1).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .x0
    let idx := (s.gpr .x1).toNat
    let M := bytesAt s.mem (at' S Layout.oMsg) p.n
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n = xmssNode p skSeed 0 p.hp pkSeed (treeAdrs a16) ∧
      (idx < 2 ^ p.hp → bytesAt s'.mem (s.gpr .x2) p.xmssSigLen = xmssSign p M skSeed idx pkSeed (treeAdrs a16)) ∧
      Frame (changes p S ++ [⟨s.gpr .x2, p.xmssSigLen⟩]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-! ## `forsSign(scratch = x0, sig = x1, kp = x2)` -/

/-- The message digest `md` at `oDigest`. -/
def mdAt (m : Mem) (S : Addr) : List Byte := bytesAt m (at' S Layout.oDigest) p.mdLen

def forsContract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    Regions s S [] ⟨s.gpr .x1, p.forsSigLen⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .x2).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .x0
    let kp := (s.gpr .x2).toNat
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      let sigF := forsSign p (mdAt p s.mem S) skSeed pkSeed (forsAdrs a16 kp)
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (s.gpr .x1) p.forsSigLen = sigF ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n = forsPkFromSig p sigF (mdAt p s.mem S) pkSeed (forsAdrs a16 kp) ∧
      Frame (changes p S ++ [⟨s.gpr .x1, p.forsSigLen⟩]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-! ## Verification: `xmssPk(scratch = x0, idx = x1, sig = x2)` and
`forsPk(scratch = x0, sig = x1, kp = x2)`, with the signature read-only

Every input of verification is public, and the code branches on the
signature, the message at `oMsg` and the digest: the contracts say they are
public. -/

def xmssPkContract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    Regions s S [⟨s.gpr .x2, p.xmssSigLen⟩] ⟨S, 0⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .x1).toNat < 2 ^ p.hp
  post s s' :=
    let S := s.gpr .x0
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n =
        xmssPkFromSig p (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x2) p.xmssSigLen)
          (bytesAt s.mem (at' S Layout.oMsg) p.n) pkSeed (treeAdrs a16) ∧
      Frame (changes p S) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ bytesAt s₁.mem (s₁.gpr .x2) p.xmssSigLen = bytesAt s₂.mem (s₂.gpr .x2) p.xmssSigLen ∧
    bytesAt s₁.mem (at' (s₁.gpr .x0) Layout.oMsg) p.n = bytesAt s₂.mem (at' (s₂.gpr .x0) Layout.oMsg) p.n

def forsPkContract : Contract isa where
  pre s :=
    let S := s.gpr .x0
    Regions s S [⟨s.gpr .x1, p.forsSigLen⟩] ⟨S, 0⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .x2).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .x0
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n =
        forsPkFromSig p (bytesAt s.mem (s.gpr .x1) p.forsSigLen) (mdAt p s.mem S) pkSeed
          (forsAdrs a16 (s.gpr .x2).toNat) ∧
      Frame (changes p S) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ bytesAt s₁.mem (s₁.gpr .x1) p.forsSigLen = bytesAt s₂.mem (s₂.gpr .x1) p.forsSigLen ∧
    bytesAt s₁.mem (at' (s₁.gpr .x0) Layout.oDigest) (p.mdLen + 2) =
      bytesAt s₂.mem (at' (s₂.gpr .x0) Layout.oDigest) (p.mdLen + 2)

end VG.Proof.SlhDsa.AArch64

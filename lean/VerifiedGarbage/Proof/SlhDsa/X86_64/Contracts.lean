module

public import VerifiedGarbage.Proof.SlhDsa.Internal
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Contract
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Layout

/-!
# SLH-DSA (SHAKE) on x86-64: the contracts of the internal functions

Untrusted: only verified code calls these functions
(`Impl/SlhDsa/X86_64/`), so their contracts are the callers' proofs'
business. Each function takes the working space `scratch` in `rdi` (`S`),
64 KiB laid out as `Impl/SlhDsa/X86_64/Layout.lean` says, and the caller
has set up in it what `Env` says: the table of the round constants of
`thash4`, `SK.seed` (but for verification), and in every lane `PK.seed` and
the layer and tree addresses `a16` of the tree. Each may change the parts of
`scratch` that `changes` lists, and its output buffer, and keeps the rest,
`Env` with it, as it was. Its calls take at most `stack` bytes below the
stack pointer.

The values are the specification's (`Spec/SlhDsa.lean`), through the
definitions of `Proof/SlhDsa/Internal.lean`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)

variable (p : Params)

/-- The size of `scratch`. -/
def scratchLen : Nat := 65536

/-- `S + o`. -/
abbrev at' (S : Addr) (o : Nat) : Addr := S + BitVec.ofNat 64 o

/-- What the caller has set up in `scratch` at `S`, in the memory `m`: the
round constants, `SK.seed` (`skSeed`, for the functions that need it), and
in each of the eight lanes `PK.seed` then the tree's 16 bytes `a16`. -/
structure Env (m : Mem) (S : Addr) (pkSeed a16 : List Byte) : Prop where
  rc : RcTable m S
  seedA : ∀ k < 4, bytesAt m (at' S (Layout.laneA k)) p.n = pkSeed
  seedB : ∀ k < 4, bytesAt m (at' S (Layout.laneB k)) p.n = pkSeed
  adrsA : ∀ k < 4, bytesAt m (at' S (Layout.laneA k + p.n)) 16 = a16
  adrsB : ∀ k < 4, bytesAt m (at' S (Layout.laneB k + p.n)) 16 = a16

/-- `SK.seed` at its place. -/
def SkAt (m : Mem) (S : Addr) (skSeed : List Byte) : Prop := bytesAt m (at' S Layout.oSkSeed) p.n = skSeed

/-- The parts of `scratch` the internal functions may change: `thash4`'s
work but its table, the frames, the lanes but their `PK.seed` and `a16`,
the digits, the nodes, the subtree roots, the message, the FORS indices. -/
def changes (S : Addr) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S Layout.oVars, 768⟩] ++
  (List.range 4).flatMap (fun k =>
    [⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩,
      ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩]) ++
  [⟨at' S Layout.oDigits, 128⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨at' S Layout.oRoots, 1024⟩,
    ⟨at' S Layout.oMsg, 64⟩, ⟨at' S Layout.oFidx, 320⟩]

/-- The regions of a function with `scratch` at `S`, the writable buffer
`out` of `outLen` bytes (outside the part of `scratch` below `oSigTmp`,
which it may be after) and the read-only `rd`, from a state whose stack
pointer is `sp`, with `stack` bytes below it for its calls. -/
structure Regions (stack : Nat) (s : State) (S : Addr) (rd : List Region) (out : Region) : Prop where
  rd_eq : s.rd = rd
  wr_eq : s.wr = [⟨S, scratchLen⟩, out]
  scr_fit : S.toNat + scratchLen ≤ 2 ^ 64
  out_fit : out.base.toNat + out.len ≤ 2 ^ 64
  out_scr : out.Disjoint ⟨S, Layout.oSigTmp⟩
  rd_fit : ∀ r ∈ rd, r.base.toNat + r.len ≤ 2 ^ 64
  rd_scr : ∀ r ∈ rd, r.Disjoint ⟨S, scratchLen⟩
  ret_scr : (retR s).Disjoint ⟨S, scratchLen⟩
  ret_out : (retR s).Disjoint out
  ret_rd : ∀ r ∈ rd, (retR s).Disjoint r
  stk_scr : (below (s.gpr .rsp) stack).Disjoint ⟨S, scratchLen⟩
  stk_out : (below (s.gpr .rsp) stack).Disjoint out
  stk_rd : ∀ r ∈ rd, (below (s.gpr .rsp) stack).Disjoint r

/-! ## `wotsLeaves4(scratch = rdi, kp = rsi, idx = rdx, sig = rcx)` -/

/-- The digit `i` at `oDigits`. -/
def digitAt (m : Mem) (S : Addr) (i : Nat) : Nat := (m (at' S (Layout.oDigits + i))).toNat

/-- What `wotsLeaves4` may change in `scratch`, for the key pairs from `kp`:
`thash4`'s work but its table, frame 0, the lanes but their `PK.seed` and
`a16`, and the four nodes. -/
def wotsChanges (S : Addr) (kp : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S Layout.oVars, 128⟩] ++
  (List.range 4).flatMap (fun k =>
    [⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩,
      ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩]) ++
  [⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩]

def wots4Contract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    Regions stack s S [] ⟨s.gpr .rcx, p.len * p.n⟩ ∧
      (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rsi).toNat % 4 = 0 ∧ ((s.gpr .rsi).toNat + 4) * p.n ≤ 32 * Layout.nodeSlots ∧
      (s.gpr .rdx).toNat < 2 ^ 32 ∧ ∀ i < p.len, digitAt s.mem S i < 16
  post s s' :=
    let S := s.gpr .rdi
    let kp := (s.gpr .rsi).toNat
    let idx := (s.gpr .rdx).toNat
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      Env p s'.mem S pkSeed a16 ∧
      (∀ k < 4, bytesAt s'.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      (kp ≤ idx ∧ idx < kp + 4 → ∀ i < p.len,
        bytesAt s'.mem (s.gpr .rcx + BitVec.ofNat 64 (i * p.n)) p.n =
          wotsChainAt p skSeed pkSeed a16 idx i (digitAt s.mem S i)) ∧
      (¬ (kp ≤ idx ∧ idx < kp + 4) → bytesAt s'.mem (s.gpr .rcx) (p.len * p.n) = bytesAt s.mem (s.gpr .rcx) (p.len * p.n)) ∧
      Frame (wotsChanges p S kp ++ [⟨s.gpr .rcx, p.len * p.n⟩, below (s.gpr .rsp) stack]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `levels(scratch = rdi, nodes = rsi, count = rdx, z₀ = rcx, auth = r8, idx = r9)`

With frame 4's variables 5 to 8 `capBase`, `adrsBase`, `type` and `kp`;
`count = 2^h` for the number `h` of heights. -/

/-- Variable `i` of frame `f`, as the caller stored it. -/
def varAt (m : Mem) (S : Addr) (f i : Nat) : BitVec 64 := m.readW (at' S (Layout.oVar f i)) 64

/-- The `c` nodes at `a`. -/
def nodesAt (m : Mem) (a : Addr) (c : Nat) : List (List Byte) :=
  (List.range c).map fun i => bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n

/-- The number of heights `levels` computes, `h` for `count = 2^h`. -/
def heightsOf (s : State) : Nat := (s.gpr .rdx).toNat.log2

/-- What `levels` may change in `scratch`, for `count` nodes at `nodes`:
`thash4`'s work but its table, frame 4, the fields and messages of the lanes
`A`, and the nodes, with the 8 after them. -/
def levelsChanges (S nodes : Addr) (count : Nat) : List Region :=
  (List.range 4).map (fun k => (⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩ : Region)) ++
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oFrame 4), 128⟩, ⟨nodes, (count + 8) * p.n⟩]

def levelsContract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    let h := heightsOf s
    Regions stack s S [] ⟨s.gpr .r8, h * p.n⟩ ∧
      (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rsi = at' S Layout.oN ∨ s.gpr .rsi = at' S Layout.oRoots) ∧
      1 ≤ h ∧ (s.gpr .rcx).toNat + h ≤ 14 ∧ (s.gpr .rdx).toNat = 2 ^ h ∧
      (s.gpr .rsi = at' S Layout.oN → ((s.gpr .rdx).toNat + 8) * p.n ≤ 32 * Layout.nodeSlots) ∧
      (s.gpr .rsi = at' S Layout.oRoots → ((s.gpr .rdx).toNat + 8) * p.n ≤ 1024) ∧
      (s.gpr .r9).toNat < 2 ^ 32 ∧ (varAt s.mem S 4 5).toNat < 2 ^ 32 ∧ (varAt s.mem S 4 6).toNat < 2 ^ 32 ∧
      (varAt s.mem S 4 7).toNat < 2 ^ 32 ∧ (varAt s.mem S 4 8).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .rdi
    let z₀ := (s.gpr .rcx).toNat
    let h := heightsOf s
    let auth := s.gpr .r8
    let L := nodesAt p s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
    let up := upNodes p
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      let ty := (varAt s.mem S 4 7).toNat
      let kp := (varAt s.mem S 4 8).toNat
      let base := (varAt s.mem S 4 6).toNat
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (s.gpr .rsi) p.n = (up pkSeed a16 ty kp base z₀ L h).getD 0 [] ∧
      (∀ r < h, bytesAt s'.mem (auth + BitVec.ofNat 64 (r * p.n)) p.n =
        xorB (bytesAt s.mem (auth + BitVec.ofNat 64 (r * p.n)) p.n)
          (pick p.n (up pkSeed a16 ty kp base z₀ L r) ((varAt s.mem S 4 5).toNat / 2 ^ (z₀ + r))
            (s.gpr .r9).toNat (z₀ + r))) ∧
      Frame (levelsChanges p S (s.gpr .rsi) (s.gpr .rdx).toNat ++ [⟨auth, h * p.n⟩, below (s.gpr .rsp) stack])
        s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `xmssTree(scratch = rdi, idx = rsi, sig = rdx)` -/

def xmssContract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    Regions stack s S [] ⟨s.gpr .rdx, p.xmssSigLen⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rsi).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .rdi
    let idx := (s.gpr .rsi).toNat
    let M := bytesAt s.mem (at' S Layout.oMsg) p.n
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n = xmssNode p skSeed 0 p.hp pkSeed (treeAdrs a16) ∧
      (idx < 2 ^ p.hp → bytesAt s'.mem (s.gpr .rdx) p.xmssSigLen = xmssSign p M skSeed idx pkSeed (treeAdrs a16)) ∧
      Frame (changes p S ++ [⟨s.gpr .rdx, p.xmssSigLen⟩, below (s.gpr .rsp) stack]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `forsSign(scratch = rdi, sig = rsi, kp = rdx)` -/

/-- The message digest `md` at `oDigest`. -/
def mdAt (m : Mem) (S : Addr) : List Byte := bytesAt m (at' S Layout.oDigest) p.mdLen

def forsContract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    Regions stack s S [] ⟨s.gpr .rsi, p.forsSigLen⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rdx).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .rdi
    let kp := (s.gpr .rdx).toNat
    ∀ pkSeed a16 skSeed, Env p s.mem S pkSeed a16 → SkAt p s.mem S skSeed →
      let sigF := forsSign p (mdAt p s.mem S) skSeed pkSeed (forsAdrs a16 kp)
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (s.gpr .rsi) p.forsSigLen = sigF ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n = forsPkFromSig p sigF (mdAt p s.mem S) pkSeed (forsAdrs a16 kp) ∧
      Frame (changes p S ++ [⟨s.gpr .rsi, p.forsSigLen⟩, below (s.gpr .rsp) stack]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Verification: `xmssPk(scratch = rdi, idx = rsi, sig = rdx)` and
`forsPk(scratch = rdi, sig = rsi, kp = rdx)`, with the signature read-only -/

def xmssPkContract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    Regions stack s S [⟨s.gpr .rdx, p.xmssSigLen⟩] ⟨S, 0⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rsi).toNat < 2 ^ p.hp
  post s s' :=
    let S := s.gpr .rdi
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n =
        xmssPkFromSig p (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rdx) p.xmssSigLen)
          (bytesAt s.mem (at' S Layout.oMsg) p.n) pkSeed (treeAdrs a16) ∧
      Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdx) p.xmssSigLen = bytesAt s₂.mem (s₂.gpr .rdx) p.xmssSigLen ∧
    bytesAt s₁.mem (at' (s₁.gpr .rdi) Layout.oMsg) p.n = bytesAt s₂.mem (at' (s₂.gpr .rdi) Layout.oMsg) p.n

def forsPkContract (stack : Nat) : Contract isa where
  pre s :=
    let S := s.gpr .rdi
    Regions stack s S [⟨s.gpr .rsi, p.forsSigLen⟩] ⟨S, 0⟩ ∧ (∃ pkSeed a16, Env p s.mem S pkSeed a16) ∧
      (s.gpr .rdx).toNat < 2 ^ 32
  post s s' :=
    let S := s.gpr .rdi
    ∀ pkSeed a16, Env p s.mem S pkSeed a16 →
      Env p s'.mem S pkSeed a16 ∧
      bytesAt s'.mem (at' S Layout.oMsg) p.n =
        forsPkFromSig p (bytesAt s.mem (s.gpr .rsi) p.forsSigLen) (mdAt p s.mem S) pkSeed
          (forsAdrs a16 (s.gpr .rdx).toNat) ∧
      Frame (changes p S ++ [below (s.gpr .rsp) stack]) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rsi) p.forsSigLen = bytesAt s₂.mem (s₂.gpr .rsi) p.forsSigLen ∧
    bytesAt s₁.mem (at' (s₁.gpr .rdi) Layout.oDigest) (p.mdLen + 2) =
      bytesAt s₂.mem (at' (s₂.gpr .rdi) Layout.oDigest) (p.mdLen + 2)

end VG.Proof.SlhDsa.X86_64

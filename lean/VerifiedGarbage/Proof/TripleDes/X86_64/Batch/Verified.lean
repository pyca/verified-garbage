module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Batch
public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call
public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.X86_64.Group
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Cfb
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Spec.TripleDes.Cfb
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Batch
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call
meta import VerifiedGarbage.Proof.Modes.Cbc
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Modes.X86_64.Copy
meta import VerifiedGarbage.Proof.Modes.X86_64.Group
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.Ctr
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.Cfb
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.X86_64.Setup
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# Triple DES-CBC and -CFB64 decryption on x86-64, many blocks at a time: verified

`Impl/TripleDes/X86_64/Batch.lean`'s functions, for any implementation of
the ECB functions they call (`EcbImpl`, `Batch/Call.lean`).

*One group.* `Lay`: where the function's arguments are, apart from each
other and from the stack its calls use. `Inv j`: the data loop before block
`j`: the first `j` blocks are the output's (`outB`), the others as on entry,
and word 0 of the scratch buffer is the chaining value `Cⱼ₋₁` (`cbcPrev`).
Both modes are the same but for what the ECB function is given (`inpB`,
`Cⱼ` or `Cⱼ₋₁`) and what its output is XORed with (`othB`, `Cⱼ₋₁` or `Cⱼ`).
`before_wp`: the code before the call copies the group's `c` blocks to words
`1 … c` of the scratch buffer, so that word `i ≤ c` holds `Cⱼ₊ᵢ₋₁`, and for
CFB words `0 … c - 1` to the data, which then holds `inpB`. `after_wp`: the
code after the call XORs word `i + 1` (CFB) or `i` (CBC), `othB`, into each
block, which holds `CIPH` or `CIPH⁻¹` of `inpB`, and makes word `c` word 0:
`Inv (j + c)`.

*Correct.* `contract cfb`: what the function does, with its arguments where
`decrypt` takes them (schedule = rdi, iv = rsi, data = rdx, n = rcx,
scratch = r8). `decrypt_wp`: the entry stores the callee-saved registers,
moves the IV to word 0 of the scratch buffer and the last ciphertext block
to the IV (`Inv 0`); the loop gives `Inv n` (`loop_wp`); the exit restores
the registers. The data then holds CBC's or CFB's decryption (`cbc_of_dinv`,
`cfb_of_dinv`).

*Constant time.* Two runs from states that agree on the public arguments
are related piece by piece (`RelCT`): the taint analysis covers the code
between the calls, from the registers that `Inv` pins to the public
arguments, and each call of the ECB function is constant time by its own
proof (`ecb_rel`). The ECB code restores the callee-saved registers from its
working space, which the analysis forgets after its stores of data, so the
analysis could not follow the call: correctness says what those registers
hold after it (`Called`).

*The contracts.* `cbc_framed` and `cfb_framed`: the shared contracts, with
the working space on the stack, zeroed on return: 2128 bytes, the 265 words
of the scratch buffer and 8 more; the stack below holds the ECB function's
return address and frame (1048 bytes).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64.Batch

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64 VG.Impl.TripleDes.X86_64.Batch
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Proof.Modes (cbcPrev DInv blocksOf over over_at over_out over_frame off_sub_not not_contains_off)
open VG.Proof.Modes.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)

/-- The ECB function's direction: encryption for CFB, decryption for CBC. -/
def dir (cfb : Bool) : Direction := if cfb then .encrypt else .decrypt

/-- The scratch buffer's words. -/
abbrev W : Nat := G + 9

theorem W_eq : W = 265 := rfl
theorem G_eq : G = 256 := rfl

/-- Where the arguments are: the schedule at `K`, the IV at `P`, `n` blocks
at `D`, the scratch buffer at `B`. -/
structure Lay (s₀ : State) (K P D B : Addr) (n : Nat) : Prop where
  rd : s₀.rd = [⟨K, 384⟩]
  wr : s₀.wr = [⟨P, 8⟩, ⟨D, 8 * n⟩, ⟨B, 8 * W⟩]
  kp : (⟨K, 384⟩ : Region).Disjoint ⟨P, 8⟩
  kd : (⟨K, 384⟩ : Region).Disjoint ⟨D, 8 * n⟩
  kb : (⟨K, 384⟩ : Region).Disjoint ⟨B, 8 * W⟩
  pd : (⟨P, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  pb : (⟨P, 8⟩ : Region).Disjoint ⟨B, 8 * W⟩
  db : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 8 * W⟩
  stkK : (below (s₀.gpr .rsp) stkN).Disjoint ⟨K, 384⟩
  stkP : (below (s₀.gpr .rsp) stkN).Disjoint ⟨P, 8⟩
  stkD : (below (s₀.gpr .rsp) stkN).Disjoint ⟨D, 8 * n⟩
  stkB : (below (s₀.gpr .rsp) stkN).Disjoint ⟨B, 8 * W⟩
  sp : stkN ≤ (s₀.gpr .rsp).toNat
  retP : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, 8⟩
  retD : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  retB : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨B, 8 * W⟩
  fitK : K.toNat + 384 ≤ 2 ^ 64
  fitP : P.toNat + 8 ≤ 2 ^ 64
  fitD : D.toNat + 8 * n ≤ 2 ^ 64
  fitB : B.toNat + 8 * W ≤ 2 ^ 64

/-- The regions the function writes. -/
abbrev frameRs (s₀ : State) (P D B : Addr) (n : Nat) : List Region :=
  [⟨B, 8 * W⟩, ⟨D, 8 * n⟩, ⟨P, 8⟩, below (s₀.gpr .rsp) stkN]

/-- The block the ECB function is given for block `j`: `Cⱼ` (CBC) or
`Cⱼ₋₁` (CFB). -/
def inpB (cfb : Bool) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  if cfb then cbcPrev 8 m₀ D iv j else bytesAt m₀ (D + BitVec.ofNat 64 (8 * j)) 8

/-- The block its output is XORed with: `Cⱼ₋₁` (CBC) or `Cⱼ` (CFB). -/
def othB (cfb : Bool) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) : List Byte :=
  if cfb then bytesAt m₀ (D + BitVec.ofNat 64 (8 * j)) 8 else cbcPrev 8 m₀ D iv j

theorem inpB_length (cfb : Bool) (m₀ : Mem) (D : Addr) (j : Nat) {P : Addr} :
    (inpB cfb m₀ D (bytesAt m₀ P 8) j).length = 8 := by
  unfold inpB; split
  · exact Proof.Modes.cbcPrev_length m₀ D (by simp [bytesAt]) j
  · simp [bytesAt]

/-- Output block `j`. -/
def outB (cfb : Bool) (k : Spec.TripleDes.Schedule) (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    List Byte :=
  Spec.Cbc.xor (blockCipher k (dir cfb) (inpB cfb m₀ D iv j)) (othB cfb m₀ D iv j)

/-- The registers the callee-saved registers are kept in, as `restoreRegs` loads them. -/
abbrev savedReg (i : Nat) : Reg := Core.savedRegs.getD i .rbx

/-- The data loop, before block `j`, from the state `s₀` on entry. -/
structure Inv (cfb : Bool) (s₀ : State) (K P D B : Addr) (n j : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = K
  r13 : s.gpr .r13 = B
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  dataR : s.gpr .r12 = D + BitVec.ofNat 64 (8 * j)
  leftR : s.gpr .r14 = BitVec.ofNat 64 (n - j)
  le : j ≤ n
  chain : ∀ u < 8, s.mem (B + BitVec.ofNat 64 u) = (cbcPrev 8 s₀.mem D (bytesAt s₀.mem P 8) j).getD u 0
  data : DInv 8 s₀.mem s.mem D n j
    (outB cfb (Spec.TripleDes.scheduleAt s₀.mem K) s₀.mem D (bytesAt s₀.mem P 8))
  frame : Frame (frameRs s₀ P D B n) s₀.mem s.mem
  iv : bytesAt s.mem P 8 = Spec.Cbc.next (bytesAt s₀.mem P 8) (blocksOf 8 s₀.mem D n)
  saved : ∀ i < 6, s.mem.readW (B + BitVec.ofNat 64 (8 * (G + 1 + i))) 64 = s₀.gpr (savedReg i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## Facts about the layout -/

section
variable {s₀ : State} {K P D B : Addr} {n : Nat}

theorem inR {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {l : Nat} (h : R.Contains a l) :
    InRegions rs a l := ⟨R, hR, h⟩

/-- Word `i` of the scratch buffer is writable. -/
theorem Lay.wB (L : Lay s₀ K P D B n) {i : Nat} (hi : i < W) :
    InRegions s₀.wr (B + BitVec.ofNat 64 (8 * i)) 8 :=
  inR (R := ⟨B, 8 * W⟩) (by rw [L.wr]; simp) (Offset.contains_base B (by omega) (by rw [W_eq] at hi; omega))

/-- Block `i` of the data is writable. -/
theorem Lay.wD (L : Lay s₀ K P D B n) {i : Nat} (hi : i < n) :
    InRegions s₀.wr (D + BitVec.ofNat 64 (8 * i)) 8 :=
  inR (R := ⟨D, 8 * n⟩) (by rw [L.wr]; simp) (Offset.contains_base D (by omega) (by have := L.fitD; omega))

end

/-- `cbcPrev` of the next block is the block. -/
theorem cbcPrev_succ (m₀ : Mem) (D : Addr) (iv : List Byte) (j : Nat) :
    cbcPrev 8 m₀ D iv (j + 1) = bytesAt m₀ (D + BitVec.ofNat 64 (8 * j)) 8 := by
  simp [cbcPrev]

/-- Three moves between registers, each source written by none before it. -/
theorem mov3_ok (s : State) {a b c x y z : Reg} (hay : a ≠ y) (haz : a ≠ z) (hbz : b ≠ z) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ s', runBlock isa [movR a x, movR b y, movR c z] s = some s' ∧ s'.gpr a = s.gpr x ∧ s'.gpr b = s.gpr y ∧
      s'.gpr c = s.gpr z ∧ (∀ r, r ≠ a → r ≠ b → r ≠ c → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s a x
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ b y
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ c z
  refine ⟨s₃, ?_, by rw [o₃ _ hac, o₂ _ hab, a₁], by rw [o₃ _ hbc, a₂, o₁ _ (Ne.symm hay)],
    by rw [a₃, o₂ _ (Ne.symm hbz), o₁ _ (Ne.symm haz)], fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1],
    by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  rw [show ([movR a x, movR b y, movR c z] : List Instr) = [movR a x] ++ ([movR b y] ++ [movR c z]) from rfl,
    runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]

/-! ## Before the call -/

/-- What the code before the call leaves, for the group of `c` blocks from
block `j`, from the state `s` before it. -/
structure Mid (cfb : Bool) (s₀ : State) (K P D B : Addr) (n j c : Nat) (s s' : State) : Prop where
  rdi : s'.gpr .rdi = K
  rsi : s'.gpr .rsi = D + BitVec.ofNat 64 (8 * j)
  rdx : s'.gpr .rdx = BitVec.ofNat 64 c
  keep : ∀ r ∈ [Reg.r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r
  words : ∀ t < 8 * (c + 1), s'.mem (B + BitVec.ofNat 64 t) =
    (cbcPrev 8 s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0
  inp : ∀ t < 8 * c, s'.mem (D + BitVec.ofNat 64 (8 * j + t)) =
    (inpB cfb s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0
  frame : Frame [⟨B, 8 * (c + 1)⟩, ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr



/-- The core's numbers. -/
theorem core_bw : core.bw = 1 := rfl
theorem core_bw' : 8 * core.bw = 8 := rfl
theorem core_buf : core.buf = 1 := rfl
theorem core_G : core.G = G := rfl

/-- A byte of a region apart from the one written. -/
theorem bytes1 {R' R : Region} {m m' : Mem} (hf : Frame [R'] m m') (hd : R.Disjoint R') (hR : R.len ≤ 2 ^ 64)
    {i : Nat} (hi : i < R.len) : m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  hf.bytes (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi

/-- The bytes a copy wrote. -/
theorem cp' {S T : Addr} {c : Nat} {s s' : State} (h : CopyInv core S T c s c s') (t : Nat)
    (ht : t < 8 * c) : s'.mem (T + BitVec.ofNat 64 t) = s.mem (S + BitVec.ofNat 64 t) :=
  h.copied t ht

/-- What the code before the call leaves before the call's arguments. -/
structure Mid4 (cfb : Bool) (s₀ : State) (K P D B : Addr) (n j c : Nat) (s s' : State) : Prop where
  r10 : s'.gpr .r10 = BitVec.ofNat 64 c
  keep : ∀ r ∈ [Reg.r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r
  words : ∀ t < 8 * (c + 1), s'.mem (B + BitVec.ofNat 64 t) =
    (cbcPrev 8 s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0
  inp : ∀ t < 8 * c, s'.mem (D + BitVec.ofNat 64 (8 * j + t)) =
    (inpB cfb s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0
  frame : Frame [⟨B, 8 * (c + 1)⟩, ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Mid4.mid {cfb : Bool} {s₀ : State} {K P D B : Addr} {n j c : Nat} {s s' : State}
    (h : Mid4 cfb s₀ K P D B n j c s s') (hK : s.gpr .r15 = K) (hA : s.gpr .r12 = D + BitVec.ofNat 64 (8 * j)) :
    WP isa (.block callArgs) s' (Mid cfb s₀ K P D B n j c s) := by
  obtain ⟨s₁, e₁, a₁, b₁, c₁, o₁, m₁, rd₁, wr₁⟩ := mov3_ok s' (a := .rdi) (b := .rsi) (c := .rdx) (x := .r15)
    (y := .r12) (z := .r10) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.of_runBlock ⟨s₁, e₁, by rw [a₁, h.keep .r15 (by simp), hK], by rw [b₁, h.keep .r12 (by simp), hA],
    by rw [c₁, h.r10], fun r hr => ?_, fun t ht => by rw [m₁]; exact h.words t ht,
    fun t ht => by rw [m₁]; exact h.inp t ht, by rw [m₁]; exact h.frame, by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
  rw [o₁ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  exact h.keep r hr

theorem before_wp (cfb : Bool) {s₀ : State} {K P D B : Addr} {n j : Nat} (L : Lay s₀ K P D B n)
    {s : State} (hi : Inv cfb s₀ K P D B n j s) (hj : j < n) :
    WP isa (before cfb) s (Mid cfb s₀ K P D B n j (min (n - j) G) s) := by
  have hfD := L.fitD
  have hfB := L.fitB
  have hW := W_eq
  have hGe := G_eq
  let cc := min (n - j) G
  have hcc : cc = min (n - j) G := rfl
  have hc0 : 0 < cc := by omega
  have hcG : cc ≤ G := by omega
  have hjc : j + cc ≤ n := by omega
  let A := D + BitVec.ofNat 64 (8 * j)
  have wrS : s.wr = s₀.wr := hi.wr
  have rdS : s.rd = s₀.rd := hi.rd
  -- `rcx := c`.
  unfold before
  refine WP.seq (WP.mono (groupCount_wp (c := core) (by rw [core_G]; decide) (by decide)
    (v := n - j) hi.leftR (by omega)) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [core_G] at c₁
  obtain ⟨s₂, e₂, a₂, b₂, t₂, o₂, m₂, rd₂, wr₂⟩ := xorArgs_ok (c := core) (by decide) (by decide) s₁
    (B := B) (by rw [o₁ _ (by decide), hi.base])
  rw [core_buf] at a₂
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁, rdS]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁, wrS]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  -- The blocks to words `1 … c`.
  have sepAT : Region.Disjoint ⟨A, 8 * cc⟩ ⟨B + BitVec.ofNat 64 8, 8 * cc⟩ :=
    (L.db.sub_left (Offset.sub_base D (by omega))).sub_right (Offset.sub_base B (by omega))
  refine WP.seq (WP.mono (copyBlocks_wp (c := core) (S := A) (T := B + BitVec.ofNat 64 8) (n := cc)
    (by decide) (by decide) hc0 (by rw [core_bw]; omega)
    (fun t ht => by
      rw [rd₂', wr₂', addr_add, ← Nat.mul_add]; rw [core_bw] at ht
      exact inRd (L.wD (by omega)))
    (fun t ht => by
      rw [wr₂', addr_add, show 8 + 8 * t = 8 * (1 + t) by omega]; rw [core_bw] at ht
      exact L.wB (by omega))
    (by rw [core_bw, Nat.mul_one]; exact sepAT) (by rw [a₂]) (by rw [b₂, o₁ _ (by decide)]; exact hi.dataR)
    (by rw [o₂ _ (by decide) (by decide) (by decide), c₁])) fun s₃ h₃ => ?_)
  have cp := cp' h₃
  have f₃ : Frame [⟨B + BitVec.ofNat 64 8, 8 * cc⟩] s₂.mem s₃.mem := h₃.frame
  -- Words `0 … c`: `Cⱼ₋₁ … Cⱼ₊ₖ₋₁`.
  have words₃ : ∀ t < 8 * (cc + 1), s₃.mem (B + BitVec.ofNat 64 t) =
      (cbcPrev 8 s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0 := by
    intro t ht
    by_cases h8 : t < 8
    · rw [show B + BitVec.ofNat 64 t = (⟨B, 8⟩ : Region).base + BitVec.ofNat 64 t from rfl,
        bytes1 f₃ (Offset.base_disjoint B (Nat.le_refl 8) (by omega)) (by show 8 ≤ 2 ^ 64; decide) h8, mem₂,
        show t / 8 = 0 by omega, Nat.add_zero, Nat.mod_eq_of_lt h8]
      exact hi.chain t h8
    · rw [show B + BitVec.ofNat 64 t = B + BitVec.ofNat 64 8 + BitVec.ofNat 64 (t - 8) by
          rw [addr_add]; congr 2; omega, cp _ (by omega), mem₂, addr_add, hi.data _ (by omega),
        ite_eq_right (by omega), show j + t / 8 = (j + t / 8 - 1) + 1 by omega, cbcPrev_succ, bytesAt_getD _ _ (Nat.mod_lt _ (by decide)),
        addr_add]
      exact congrArg (fun x => s₀.mem (D + BitVec.ofNat 64 x)) (show 8 * j + (t - 8) = 8 * (j + t / 8 - 1) + t % 8 by omega)
  -- The blocks, still the ciphertext's.
  have data₃ : ∀ t < 8 * cc, s₃.mem (D + BitVec.ofNat 64 (8 * j + t)) =
      (bytesAt s₀.mem (D + BitVec.ofNat 64 (8 * (j + t / 8))) 8).getD (t % 8) 0 := by
    intro t ht
    rw [← addr_add, show D + BitVec.ofNat 64 (8 * j) = (⟨D + BitVec.ofNat 64 (8 * j), 8 * cc⟩ : Region).base from rfl,
      bytes1 f₃ sepAT (by simp only; omega) ht, mem₂, addr_add, hi.data _ (by omega), ite_eq_right (by omega),
      bytesAt_getD _ _ (Nat.mod_lt _ (by decide)), addr_add]
    exact congrArg (fun x => s₀.mem (D + BitVec.ofNat 64 x)) (show 8 * j + t = 8 * (j + t / 8) + t % 8 by omega)
  have keep₃ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [h₃.regs r h1 h2 h3 h4, o₂ r h1 h2 h5, o₁ r h3]
  have r10₃ : s₃.gpr .r10 = BitVec.ofNat 64 cc := by
    rw [h₃.regs _ (by decide) (by decide) (by decide) (by decide), t₂, c₁]
  have fr₃ : Frame [⟨B, 8 * (cc + 1)⟩, ⟨D + BitVec.ofNat 64 (8 * j), 8 * cc⟩] s.mem s₃.mem := by
    rw [← mem₂]
    exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base B (by omega)⟩
  have keepL : ∀ r ∈ [Reg.r12, .r13, .r14, .r15, .rsp], s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  cases cfb
  · -- CBC: the ECB function deciphers the blocks.
    simp only [Bool.false_eq_true, ite_false]
    exact WP.seq (WP.block_nil (Mid4.mid ⟨r10₃, keepL, words₃, fun t ht => by
      rw [data₃ t ht]; rfl, fr₃, by rw [h₃.rd, rd₂, rd₁], by rw [h₃.wr, wr₂, wr₁]⟩ hi.r15 hi.dataR))
  · -- CFB: words `0 … c - 1` to the data, for the ECB function to encipher.
    simp only [ite_true]
    unfold shiftIn
    obtain ⟨s₄, e₄, a₄, b₄, c₄, o₄, m₄, rd₄, wr₄⟩ := mov3_ok s₃ (a := .rax) (b := .rbx) (c := .rcx) (x := .r12)
      (y := sb) (z := .r10) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have sepBA : Region.Disjoint ⟨B, 8 * cc⟩ ⟨D + BitVec.ofNat 64 (8 * j), 8 * cc⟩ :=
      ((L.db.sub_left (Offset.sub_base D (by omega))).sub_right (Region.sub_prefix (by omega))).symm
    refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, e₄, WP.mono (copyBlocks_wp (c := core) (S := B)
      (T := D + BitVec.ofNat 64 (8 * j)) (n := cc) (by decide) (by decide) hc0 (by rw [core_bw]; omega)
      (fun t ht => by
        rw [rd₄, wr₄, h₃.rd, h₃.wr, rd₂', wr₂']; rw [core_bw] at ht
        exact inRd (L.wB (by omega)))
      (fun t ht => by
        rw [wr₄, h₃.wr, wr₂', addr_add, ← Nat.mul_add]; rw [core_bw] at ht
        exact L.wD (by omega))
      (by rw [core_bw, Nat.mul_one]; exact sepBA)
      (by rw [a₄, keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.dataR])
      (by rw [b₄, keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hi.base])
      (by rw [c₄, r10₃])) fun s₅ h₅ => ?_⟩))
    have f₅ : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8 * cc⟩] s₄.mem s₅.mem := h₅.frame
    have mem₄ : s₄.mem = s₃.mem := m₄
    refine Mid4.mid ⟨by rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), o₄ _ (by decide) (by decide)
        (by decide), r10₃], fun r hr => ?_, fun t ht => ?_, fun t ht => ?_, ?_, by rw [h₅.rd, rd₄, h₃.rd, rd₂, rd₁],
      by rw [h₅.wr, wr₄, h₃.wr, wr₂, wr₁]⟩ hi.r15 hi.dataR
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      · rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), o₄ _ (by decide) (by decide) (by decide)]
        exact keepL _ (by simp)
    · rw [show B + BitVec.ofNat 64 t = (⟨B, 8 * (cc + 1)⟩ : Region).base + BitVec.ofNat 64 t from rfl,
        bytes1 f₅ ((L.db.sub_left (Offset.sub_base D (by omega))).sub_right (Region.sub_prefix (by omega))).symm
          (by simp only; omega) ht, mem₄]
      exact words₃ t ht
    · rw [← addr_add, cp' h₅ t ht, mem₄, words₃ t (by omega)]
      rfl
    · refine fr₃.trans ?_
      rw [← mem₄]
      exact f₅.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp

/-! ## The XOR -/

/-- XORing, after `j` of `n` words at `X` into those at `A`. -/
structure XorInv (X A : Addr) (n : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  done : ∀ t < 8 * j, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) ^^^ s₀.mem (X + BitVec.ofNat 64 t)
  rest : ∀ t, 8 * j ≤ t → t < 8 * n → s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨A, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBlocks_wp {X A : Addr} {n : Nat} {s₀ : State} (hn : 0 < n) (hfit : 8 * n < 2 ^ 63)
    (hX : ∀ t < n, InRegions (s₀.rd ++ s₀.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hA : ∀ t < n, InRegions s₀.wr (A + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 8 * n⟩ ⟨A, 8 * n⟩) (ha : s₀.gpr .rax = X) (hb : s₀.gpr .rbx = A)
    (hc : s₀.gpr .rcx = BitVec.ofNat 64 n) :
    WP isa xorBlocks s₀ fun s => XorInv X A n s₀ n s ∧ s.gpr .rbx = A + BitVec.ofNat 64 (8 * n) := by
  refine WP.mono (blockLoop_wp (c := core) _ (XorInv X A n s₀) (by decide) hn (by omega)
    (fun j s s' h hm hrd hwr hg => ⟨fun t ht => by rw [hm]; exact h.done t ht,
      fun t h1 h2 => by rw [hm]; exact h.rest t h1 h2, by rw [hm]; exact h.frame,
      fun r h1 h2 h3 h4 => by rw [hg r h1 h2 h3, h.regs r h1 h2 h3 h4], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩)
    (fun j hj s hi hax hbx => ?_) ⟨fun t ht => by omega, fun _ _ _ => rfl, Frame.refl _ _, fun _ _ _ _ _ => rfl,
      rfl, rfl⟩ ha hb hc) fun _ h => ⟨h.1, h.2.2⟩
  rw [core_bw'] at hax hbx
  have hXs : ∀ t < 8 * n, s.mem (X + BitVec.ofNat 64 t) = s₀.mem (X + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨X, 8 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have hlt : 8 * j + 8 ≤ 8 * n := by omega
  refine WP.mono (xorN_wp (k := 1) (t := .rbp) (rd := .rbx) (rs := .rax) (od := 0) (os := 0)
    (P := A + BitVec.ofNat 64 (8 * j)) (Q := X + BitVec.ofNat 64 (8 * j))
    ⟨by rw [hbx]; simp, by rw [hax]; simp, by decide, by decide,
      fun w hw => by rw [hi.wr, addr_add, show 8 * j + 8 * w = 8 * j by omega]; exact hA j hj,
      fun w hw => by rw [hi.rd, hi.wr, addr_add, show 8 * j + 8 * w = 8 * j by omega]; exact hX j hj,
      (hsep.symm.sub_left (Offset.sub_base A (by omega))).sub_right (Offset.sub_base X (by omega)),
      by decide⟩) fun s' h' => ?_
  have hm : ∀ t < 8 * n, s'.mem (A + BitVec.ofNat 64 t) =
      if 8 * j ≤ t ∧ t < 8 * j + 8 then s.mem (A + BitVec.ofNat 64 t) ^^^ s.mem (X + BitVec.ofNat 64 t)
      else s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [h'.mem]
    split
    · rename_i h1
      rw [show A + BitVec.ofNat 64 t = A + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (t - 8 * j) by
        rw [addr_add, show 8 * j + (t - 8 * j) = t by omega], over_at (by omega) (by decide), addr_add, addr_add,
        show 8 * j + (t - 8 * j) = t by omega]
    · exact over_out (off_sub_not A (by omega) (by omega) (by omega) (by omega))
  refine ⟨⟨fun t ht => ?_, fun t h1 h2 => ?_, hi.frame.trans fun x hx => ?_,
    fun r h1 h2 h3 h4 => by rw [h'.regs r h4, hi.regs r h1 h2 h3 h4], by rw [h'.rd, hi.rd], by rw [h'.wr, hi.wr]⟩,
    h'.regs _ (by decide), h'.regs _ (by decide), h'.regs _ (by decide)⟩
  · rw [hm t (by omega)]
    split
    · rw [hi.rest t (by omega) (by omega), hXs t (by omega)]
    · exact hi.done t (by omega)
  · rw [hm t h2, ite_eq_right (by omega)]
    exact hi.rest t (by omega) h2
  · rw [h'.mem]
    exact over_out fun h => hx _ (List.mem_singleton_self _)
      (Offset.sub_base A (n := 8) (show 8 * j + 8 ≤ 8 * n by omega) x (by simp only [Region.Contains]; omega))

/-! ## The call -/

theorem toNat_off {D : Addr} {x : Nat} (h : D.toNat + x < 2 ^ 64) : (D + BitVec.ofNat 64 x).toNat = D.toNat + x := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- The ECB function's arguments, from the code before it. -/
theorem Mid.callPre {cfb : Bool} {s₀ : State} {K P D B : Addr} {n j c : Nat} {s s' : State}
    (L : Lay s₀ K P D B n) (hi : Inv cfb s₀ K P D B n j s) (hjc : j + c ≤ n) (hc0 : 0 < c)
    (h : Mid cfb s₀ K P D B n j c s s') : EcbCallPre s' K (D + BitVec.ofNat 64 (8 * j)) c := by
  have hfD := L.fitD
  have hsp : s'.gpr .rsp = s₀.gpr .rsp := by rw [h.keep .rsp (by simp), hi.rsp]
  have subA : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  refine ⟨h.rdi, h.rsi, h.rdx, by rw [hsp]; exact L.sp, L.fitK,
    by rw [toNat_off (by omega)]; omega, L.kd.sub_right subA, by rw [hsp]; exact L.stkK,
    by rw [hsp]; exact L.stkD.sub_right subA, ?_, ?_⟩
  · rw [h.rd, h.wr, hi.rd, hi.wr, L.rd, L.wr]
    exact Covers.append (Covers.refl _) (Covers.one ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base D (by omega) (by omega)⟩)
  · rw [h.wr, hi.wr, L.wr]
    exact Covers.one ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base D (by omega) (by omega)⟩

/-- What the code before the call and the call leave. -/
structure Called (cfb : Bool) (s₀ : State) (K P D B : Addr) (n j c : Nat) (s s' : State) : Prop where
  keep : ∀ r ∈ [Reg.r12, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r
  words : ∀ t < 8 * (c + 1), s'.mem (B + BitVec.ofNat 64 t) =
    (cbcPrev 8 s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0
  out : ∀ t < 8 * c, s'.mem (D + BitVec.ofNat 64 (8 * j + t)) =
    (blockCipher (Spec.TripleDes.scheduleAt s₀.mem K) (dir cfb)
      (inpB cfb s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8))).getD (t % 8) 0
  frame : Frame [⟨B, 8 * (c + 1)⟩, ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩, below (s₀.gpr .rsp) stkN] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Called.of {cfb : Bool} {s₀ : State} {K P D B : Addr} {n j c : Nat} {s s₅ s₆ : State}
    (L : Lay s₀ K P D B n) (hi : Inv cfb s₀ K P D B n j s) (hjc : j + c ≤ n) (hcG : c ≤ G)
    (h : Mid cfb s₀ K P D B n j c s s₅)
    (hc : EcbCallPost (dir cfb) s₅ K (D + BitVec.ofNat 64 (8 * j)) c s₆) :
    Called cfb s₀ K P D B n j c s s₆ := by
  have hfD := L.fitD
  have hfB := L.fitB
  have hW := W_eq
  have hGe := G_eq
  have hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [h.keep .rsp (by simp), hi.rsp]
  have f := hc.frame
  rw [hsp] at f
  have subA : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have subB : Region.Sub ⟨B, 8 * (c + 1)⟩ ⟨B, 8 * W⟩ := Region.sub_prefix (by omega)
  have dB : ∀ r ∈ [(⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ : Region), below (s₀.gpr .rsp) stkN],
      Region.Disjoint ⟨B, 8 * (c + 1)⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (L.db.sub_left subA).symm.sub_left subB
    · exact (L.stkB.sub_right subB).symm
  -- The schedule: no write reaches it.
  have eK : Spec.TripleDes.scheduleAt s₅.mem K = Spec.TripleDes.scheduleAt s₀.mem K := by
    refine scheduleAt_congr fun i hi' => ?_
    rw [h.frame.bytes (R := ⟨K, 384⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.kb.sub_right subB
        · exact L.kd.sub_right subA) (by show 384 ≤ 2 ^ 64; decide) hi']
    exact hi.frame.bytes (R := ⟨K, 384⟩) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.kb
        · exact L.kd
        · exact L.kp
        · exact L.stkK.symm) (by show 384 ≤ 2 ^ 64; decide) hi'
  refine ⟨fun r hr => ?_, fun t ht => ?_, fun t ht => ?_, ?_, by rw [hc.rd, h.rd], by rw [hc.wr, h.wr]⟩
  · rw [hc.saved r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]),
      h.keep r hr]
  · rw [show B + BitVec.ofNat 64 t = (⟨B, 8 * (c + 1)⟩ : Region).base + BitVec.ofNat 64 t from rfl,
      f.bytes dB (by simp only; omega) ht]
    exact h.words t ht
  · have hu : t % 8 < 8 := Nat.mod_lt _ (by decide)
    have ht' : t / 8 < c := by omega
    rw [show 8 * j + t = 8 * j + (8 * (t / 8) + t % 8) by omega, ← addr_add, hc.out _ ht' _ hu, eK]
    rw [show Spec.TripleDes.bytesAt = bytesAt from rfl, addr_add,
      Proof.Modes.bytesAt_of_getD (xs := inpB cfb s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)) (inpB_length _ _ _ _)
        fun u hu' => by
          rw [addr_add, Nat.add_assoc, h.inp _ (by omega), show (8 * (t / 8) + u) / 8 = t / 8 by omega,
            show (8 * (t / 8) + u) % 8 = u by omega]]
  · exact (h.frame.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp).trans
      (f.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)

/-! ## After the call -/

/-- Which word is XORed into block `0`: `1` for CFB, `0` for CBC. -/
def off (cfb : Bool) : Nat := if cfb then 1 else 0

theorem off_le (cfb : Bool) : off cfb ≤ 1 := by unfold off; split <;> omega

theorem xorArgs_ok (cfb : Bool) (s : State) :
    ∃ s', runBlock isa (xorArgs cfb) s = some s' ∧ s'.gpr .rbx = s.gpr .r12 ∧ s'.gpr .r10 = s.gpr .rcx ∧
      s'.gpr .rax = s.gpr sb + BitVec.ofNat 64 (8 * off cfb) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, b₁, c₁, o₁, m₁, rd₁, wr₁⟩ := mov3_ok s (a := .rbx) (b := .r10) (c := .rax) (x := .r12)
    (y := .rcx) (z := sb) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  cases cfb
  · refine ⟨s₁, by simpa [xorArgs] using e₁, a₁, b₁, by rw [c₁]; simp [off], fun r h1 h2 h3 => o₁ r h2 h3 h1,
      m₁, rd₁, wr₁⟩
  · obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rax 8
    refine ⟨s₂, ?_, by rw [o₂ _ (by decide), a₁], by rw [o₂ _ (by decide), b₁],
      by rw [a₂, c₁]; rfl, fun r h1 h2 h3 => by rw [o₂ r h1, o₁ r h2 h3 h1],
      by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    rw [show xorArgs true = [movR .rbx .r12, movR .r10 .rcx, movR .rax sb] ++ [.alu .add .rax (.imm 8)] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]

/-- `rax := B + 8 c`, from `c` in `r10` and `B` in `sb`. -/
theorem wordC_ok (s : State) {c : Nat} {B : Addr} (hc : s.gpr .r10 = BitVec.ofNat 64 c) (hB : s.gpr sb = B) :
    ∃ s', runBlock isa [movR .rax .r10, .shift .shl .rax 3, .alu .add .rax (.reg sb)] s = some s' ∧
      s'.gpr .rax = B + BitVec.ofNat 64 (8 * c) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rax .r10
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := shlImm_ok s₁ .rax (k := 3) (by decide)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addReg_ok s₂ .rax sb
  refine ⟨s₃, ?_, ?_, fun r h => by rw [o₃ r h, o₂ r h, o₁ r h], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁]⟩
  · rw [show ([movR .rax .r10, .shift .shl .rax 3, .alu .add .rax (.reg sb)] : List Instr) =
      [movR .rax .r10] ++ ([.shift .shl .rax 3] ++ [.alu .add .rax (.reg sb)]) from rfl, runBlock_app, e₁,
      Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [a₃, a₂, a₁, o₂ _ (by decide), o₁ _ (by decide), hc, hB, BitVec.add_comm]
    congr 1
    rw [BitVec.shiftLeft_eq_mul_twoPow, show (BitVec.twoPow 64 3) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul,
      BitVec.mul_comm]

/-- Byte `u` of a XOR of blocks of 8 bytes. -/
theorem xor_getD {a b : List Byte} (ha : a.length = 8) (hb : b.length = 8) {u : Nat} (hu : u < 8) :
    (Spec.Cbc.xor a b).getD u 0 = a.getD u 0 ^^^ b.getD u 0 := by
  have h3 : u < (Spec.Cbc.xor a b).length := by simp [Spec.Cbc.xor, ha, hb, hu]
  rw [← List.getElem_eq_getD (h := h3) 0, ← List.getElem_eq_getD (h := by omega) 0,
    ← List.getElem_eq_getD (h := by omega) 0]
  simp only [Spec.Cbc.xor, List.getElem_zipWith]

theorem othB_length (cfb : Bool) (m₀ : Mem) (D : Addr) (j : Nat) {P : Addr} :
    (othB cfb m₀ D (bytesAt m₀ P 8) j).length = 8 := by
  unfold othB; split
  · simp [bytesAt]
  · exact Proof.Modes.cbcPrev_length m₀ D (by simp [bytesAt]) j

/-- Word `off + i` of the scratch buffer, after the copy: `othB` of block `j + i`. -/
theorem word_othB (cfb : Bool) (m₀ : Mem) (D : Addr) (iv : List Byte) (j t : Nat) :
    (cbcPrev 8 m₀ D iv (j + (8 * off cfb + t) / 8)).getD ((8 * off cfb + t) % 8) 0 =
      (othB cfb m₀ D iv (j + t / 8)).getD (t % 8) 0 := by
  cases cfb
  · simp [off, othB]
  · simp only [off, othB, ite_true]
    rw [show j + (8 * 1 + t) / 8 = (j + t / 8) + 1 by omega, show (8 * 1 + t) % 8 = t % 8 by omega, cbcPrev_succ]

/-- A byte of the data outside a region of the scratch buffer. -/
theorem notB {s₀ : State} {K P D B : Addr} {n : Nat} (L : Lay s₀ K P D B n) {i l : Nat} (hi : i < 8 * n)
    (hl : l ≤ 8 * W) : ¬ (⟨B, l⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 := fun h =>
  (L.db.sub_right (Region.sub_prefix hl)) _ (Offset.contains_base D (by omega) (by have := L.fitD; omega)) h

theorem after_wp (cfb : Bool) {s₀ : State} {K P D B : Addr} {n j : Nat} (L : Lay s₀ K P D B n)
    {s s₆ : State} (hi : Inv cfb s₀ K P D B n j s) (hj : j < n)
    (hc : Called cfb s₀ K P D B n j (min (n - j) G) s s₆) :
    WP isa (after cfb) s₆ fun s' => s'.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧
      Inv cfb s₀ K P D B n (j + min (n - j) G) s' := by
  have hfD := L.fitD
  have hfB := L.fitB
  have hW := W_eq
  have hGe := G_eq
  have hoff := off_le cfb
  generalize hcc : min (n - j) G = c at hc ⊢
  have hc0 : 0 < c := by omega
  have hcG : c ≤ G := by omega
  have hjc : j + c ≤ n := by omega
  unfold after
  obtain ⟨s₇, e₇, b₇, o₇, m₇, rd₇, wr₇⟩ := movR_ok s₆ sb .r13
  refine WP.seq (WP.of_runBlock ⟨s₇, e₇, ?_⟩)
  have B₇ : s₇.gpr sb = B := by rw [b₇, hc.keep .r13 (by simp), hi.r13]
  have l₇ : s₇.gpr .r14 = BitVec.ofNat 64 (n - j) := by rw [o₇ _ (by decide), hc.keep .r14 (by simp), hi.leftR]
  refine WP.seq (WP.mono (groupCount_wp (c := core) (by rw [core_G]; decide) (by decide) (v := n - j) l₇
    (by omega)) fun s₈ ⟨c₈, o₈, m₈, rd₈, wr₈⟩ => ?_)
  rw [core_G, hcc] at c₈
  obtain ⟨s₉, e₉, b₉, t₉, a₉, o₉, m₉, rd₉, wr₉⟩ := xorArgs_ok cfb s₈
  refine WP.seq (WP.of_runBlock ⟨s₉, e₉, ?_⟩)
  have A₉ : s₉.gpr .rbx = D + BitVec.ofNat 64 (8 * j) := by
    rw [b₉, o₈ _ (by decide), o₇ _ (by decide), hc.keep .r12 (by simp), hi.dataR]
  have X₉ : s₉.gpr .rax = B + BitVec.ofNat 64 (8 * off cfb) := by rw [a₉, o₈ _ (by decide), B₇]
  have C₉ : s₉.gpr .rcx = BitVec.ofNat 64 c := by rw [o₉ _ (by decide) (by decide) (by decide), c₈]
  have T₉ : s₉.gpr .r10 = BitVec.ofNat 64 c := by rw [t₉, c₈]
  have mem₉ : s₉.mem = s₆.mem := by rw [m₉, m₈, m₇]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈, wr₇, hc.wr, hi.wr]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈, rd₇, hc.rd, hi.rd]
  have subA : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have subX : Region.Sub ⟨B + BitVec.ofNat 64 (8 * off cfb), 8 * c⟩ ⟨B, 8 * W⟩ := Offset.sub_base B (by omega)
  have sepXA : Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * off cfb), 8 * c⟩ ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ :=
    ((L.db.sub_left subA).symm.sub_left subX)
  refine WP.seq (WP.mono (xorBlocks_wp (X := B + BitVec.ofNat 64 (8 * off cfb)) (A := D + BitVec.ofNat 64 (8 * j))
    (n := c) hc0 (by omega)
    (fun t ht => by rw [rd₉', wr₉', addr_add, ← Nat.mul_add]; exact inRd (L.wB (by omega)))
    (fun t ht => by rw [wr₉', addr_add, ← Nat.mul_add]; exact L.wD (by omega))
    sepXA X₉ A₉ C₉) fun s₁₀ ⟨x₁₀, rbx₁₀⟩ => ?_)
  have k₁₀ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → r ≠ sb → s₁₀.gpr r = s₆.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [x₁₀.regs r h1 h2 h3 h4, o₉ r h1 h2 h5, o₈ r h3, o₇ r h6]
  have r10₁₀ : s₁₀.gpr .r10 = BitVec.ofNat 64 c := by
    rw [x₁₀.regs _ (by decide) (by decide) (by decide) (by decide), T₉]
  have sb₁₀ : s₁₀.gpr sb = B := by
    rw [x₁₀.regs _ (by decide) (by decide) (by decide) (by decide), o₉ _ (by decide) (by decide) (by decide),
      o₈ _ (by decide), B₇]
  obtain ⟨s₁₁, e₁₁, a₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := wordC_ok s₁₀ r10₁₀ sb₁₀
  unfold finish
  rw [List.append_assoc]
  refine WP.block_append (WP.of_runBlock ⟨s₁₁, e₁₁, ?_⟩)
  rw [show copyW .rbp sb .rax 0 0 0 = (List.range 1).flatMap (copyW .rbp sb .rax 0 0) from rfl]
  refine WP.block_append (WP.mono (copyN_wp (k := 1) (t := .rbp) (rd := sb) (rs := .rax) (od := 0) (os := 0)
    (P := B) (Q := B + BitVec.ofNat 64 (8 * c))
    ⟨by rw [o₁₁ _ (by decide), sb₁₀]; simp, by rw [a₁₁]; simp, by decide, by decide,
      fun w hw => by rw [wr₁₁, x₁₀.wr, wr₉', show w = 0 by omega]; simpa using L.wB (i := 0) (by omega),
      fun w hw => by rw [rd₁₁, wr₁₁, x₁₀.rd, x₁₀.wr, rd₉', wr₉', show w = 0 by omega, addr_add]
                     exact inRd (L.wB (by omega)),
      Offset.base_disjoint B (by omega) (by omega), by decide⟩) fun s₁₂ h₁₂ => ?_)
  obtain ⟨s₁₃, e₁₃, d₁₃, l₁₃, z₁₃, o₁₃, m₁₃, rd₁₃, wr₁₃⟩ := advance_ok (c := core) (by decide) (by decide) s₁₂
  have k₁₂ : ∀ r, r ≠ .rax → r ≠ .rbp → s₁₂.gpr r = s₁₁.gpr r ∧ s₁₁.gpr r = s₁₀.gpr r := fun r h1 h2 =>
    ⟨h₁₂.regs r h2, o₁₁ r h1⟩
  have mem₁₃ : s₁₃.mem = over s₁₀.mem B 8 fun i => s₁₀.mem (B + BitVec.ofNat 64 (8 * c) + BitVec.ofNat 64 i) := by
    rw [m₁₃, h₁₂.mem, m₁₁]
  -- The bytes the group wrote.
  have out : ∀ t < 8 * c, s₁₀.mem (D + BitVec.ofNat 64 (8 * j + t)) =
      (outB cfb (Spec.TripleDes.scheduleAt s₀.mem K) s₀.mem D (bytesAt s₀.mem P 8) (j + t / 8)).getD (t % 8) 0 := by
    intro t ht
    rw [← addr_add, x₁₀.done t ht, mem₉, addr_add, hc.out t ht, addr_add, hc.words _ (by omega), word_othB, outB,
      xor_getD (blockCipher_length _ _ _) (othB_length _ _ _ _) (Nat.mod_lt _ (by decide))]
  have fG : Frame [⟨B, 8 * (c + 1)⟩, ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩, below (s₀.gpr .rsp) stkN]
      s.mem s₁₃.mem := by
    rw [mem₁₃]
    refine (hc.frame.trans ?_).trans ((over_frame _ _ _ _).sub fun r hr => ?_)
    · rw [← mem₉]
      exact x₁₀.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨B, 8 * (c + 1)⟩, by simp, Region.sub_prefix (by omega)⟩
  have keep : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → r ≠ .r10 → r ≠ sb → r ≠ .r12 → r ≠ .r14 →
      s₁₃.gpr r = s₆.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [o₁₃ r h7 h8, (k₁₂ r h1 h4).1, (k₁₂ r h1 h4).2, k₁₀ r h1 h2 h3 h4 h5 h6]
  have r14₁₂ : s₁₂.gpr .r14 = BitVec.ofNat 64 (n - j) := by
    rw [(k₁₂ _ (by decide) (by decide)).1, (k₁₂ _ (by decide) (by decide)).2,
      k₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hc.keep .r14 (by simp), hi.leftR]
  have r10₁₂ : s₁₂.gpr .r10 = BitVec.ofNat 64 c := by
    rw [(k₁₂ _ (by decide) (by decide)).1, (k₁₂ _ (by decide) (by decide)).2, r10₁₀]
  have subB : Region.Sub ⟨B, 8 * (c + 1)⟩ ⟨B, 8 * W⟩ := Region.sub_prefix (by omega)
  have hrsp : s₆.gpr .rsp = s₀.gpr .rsp := by rw [hc.keep .rsp (by simp), hi.rsp]
  have dP : ∀ r ∈ [(⟨B, 8 * (c + 1)⟩ : Region), ⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩, below (s₀.gpr .rsp) stkN],
      Region.Disjoint ⟨P, 8⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.pb.sub_right subB
    · exact L.pd.sub_right subA
    · exact L.stkP.symm
  refine WP.of_runBlock ⟨s₁₃, e₁₃, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hjc, fun u hu => ?_, fun i hi' => ?_, ?_, ?_,
    fun i hi6 => ?_, by rw [rd₁₃, h₁₂.rd, rd₁₁, x₁₀.rd, rd₉'], by rw [wr₁₃, h₁₂.wr, wr₁₁, x₁₀.wr, wr₉']⟩⟩
  · rw [z₁₃]
    show some (s₁₂.gpr .r14 - s₁₂.gpr .r10 == 0) = _
    rw [r14₁₂, r10₁₂, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hc.keep .r15 (by simp), hi.r15]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hc.keep .r13 (by simp), hi.r13]
  · rw [o₁₃ _ (by decide) (by decide), (k₁₂ _ (by decide) (by decide)).1, (k₁₂ _ (by decide) (by decide)).2, sb₁₀]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrsp]
  · refine d₁₃.trans ?_
    rw [(k₁₂ _ (by decide) (by decide)).1, (k₁₂ _ (by decide) (by decide)).2, rbx₁₀, addr_add, Nat.mul_add]
  · refine l₁₃.trans ?_
    show s₁₂.gpr .r14 - s₁₂.gpr .r10 = _
    rw [r14₁₂, r10₁₂, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · -- The chaining value: word `c`, the group's last ciphertext block.
    rw [mem₁₃, over_at hu (by decide), addr_add,
      show B + BitVec.ofNat 64 (8 * c + u) = (⟨B, 8 * (c + 1)⟩ : Region).base + BitVec.ofNat 64 (8 * c + u) from rfl,
      bytes1 x₁₀.frame ((L.db.sub_left subA).symm.sub_left subB) (by simp only; omega) (by simp only; omega), mem₉,
      hc.words _ (by omega), show (8 * c + u) / 8 = c by omega, show (8 * c + u) % 8 = u by omega]
  · -- The data.
    have e1 : s₁₃.mem (D + BitVec.ofNat 64 i) = s₁₀.mem (D + BitVec.ofNat 64 i) := by
      rw [mem₁₃]; exact over_out fun h => notB L hi' (l := 8) (by omega) (by simp only [Region.Contains]; omega)
    by_cases hin : 8 * j ≤ i ∧ i < 8 * j + 8 * c
    · obtain ⟨t, rfl⟩ : ∃ t, i = 8 * j + t := ⟨i - 8 * j, by omega⟩
      rw [e1, out t (by omega), ite_eq_left (by omega), show (8 * j + t) / 8 = j + t / 8 by omega,
        show (8 * j + t) % 8 = t % 8 by omega]
    · have hA' : ¬ (⟨D + BitVec.ofNat 64 (8 * j), 8 * c⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 :=
        not_contains_off D (by omega) (by omega) (by omega) (by omega)
      rw [e1, x₁₀.frame _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hA'), mem₉,
        hc.frame _ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact notB L hi' (by omega)
          · exact hA'
          · exact fun h => L.stkD _ h (Offset.contains_base D (by omega) (by omega))), hi.data i hi']
      by_cases h8 : i < 8 * j
      · rw [ite_eq_left h8, ite_eq_left (by omega)]
      · rw [ite_eq_right h8, ite_eq_right (by omega)]
  · exact hi.frame.trans (fG.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, subB⟩
      · exact ⟨_, by simp, subA⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  · rw [← hi.iv]
    unfold bytesAt
    exact List.map_congr_left fun u hu => fG.bytes (R := ⟨P, 8⟩) dP (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hu)
  · rw [← hi.saved i hi6]
    refine fG.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base B (by omega) (by omega)
    · exact (L.db.sub_left subA).symm.sub_left (Offset.sub_base B (by omega))
    · exact (L.stkB.sub_right (Offset.sub_base B (by omega))).symm

/-! ## The groups -/

theorem group_wp (v : EcbImpl) (cfb : Bool) {s₀ : State} {K P D B : Addr} {n j : Nat} (L : Lay s₀ K P D B n)
    {s : State} (hi : Inv cfb s₀ K P D B n j s) (hj : j < n) :
    WP isa (group cfb (v.name (dir cfb)) (v.code (dir cfb))) s fun s' =>
      s'.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧ Inv cfb s₀ K P D B n (j + min (n - j) G) s' := by
  have hGe := G_eq
  exact WP.seq (WP.mono (before_wp cfb L hi hj) fun s₅ hm =>
    WP.seq (WP.mono (ecb_call v (dir cfb) (hm.callPre L hi (by omega) (by omega))) fun s₆ hc =>
      after_wp cfb L hi hj (Called.of L hi (by omega) (by omega) hm hc)))

theorem loop_wp (v : EcbImpl) (cfb : Bool) {s₀ : State} {K P D B : Addr} {n j : Nat} (L : Lay s₀ K P D B n)
    {s : State} (hi : Inv cfb s₀ K P D B n j s) (hj : j < n) :
    WP isa (.loop (group cfb (v.name (dir cfb)) (v.code (dir cfb))) .ne) s (Inv cfb s₀ K P D B n n) := by
  have hGe := G_eq
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ j < n ∧ Inv cfb s₀ K P D B n j s) (fun m s hs => ?_)
    (n - j) s ⟨j, rfl, hj, hi⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  refine WP.mono (group_wp v cfb L hi hj) fun s' ⟨z, h⟩ => ?_
  by_cases hd : n - (j + min (n - j) G) = 0
  · refine .inl ⟨by simp [X86_64.eval, z, hd], ?_⟩
    rwa [show j + min (n - j) G = n by omega] at h
  · exact .inr ⟨by simp [X86_64.eval, z, hd], n - (j + min (n - j) G), by omega, _, rfl, by omega, h⟩

/-! ## The whole function, correct -/

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64 VG.Impl.TripleDes.X86_64.Batch
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Proof.Modes (cbcPrev DInv blocksOf over over_at over_out over_frame cbcOut fbIn fbOut fbStep)
open VG.Proof.Modes.X86_64
open VG.Spec.Aes (bytesAt)

/-- The function's precondition on x86-64: `Lay`'s facts, as a conjunction. -/
def preC (s : State) : Prop :=
  let K := s.gpr .rdi
  let P := s.gpr .rsi
  let D := s.gpr .rdx
  let B := s.gpr .r8
  let n := (s.gpr .rcx).toNat
  let stk := below (s.gpr .rsp) stkN
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [⟨K, 384⟩] ∧ s.wr = [⟨P, 8⟩, ⟨D, 8 * n⟩, ⟨B, 8 * W⟩] ∧
    (⟨K, 384⟩ : Region).Disjoint ⟨P, 8⟩ ∧ (⟨K, 384⟩ : Region).Disjoint ⟨D, 8 * n⟩ ∧
    (⟨K, 384⟩ : Region).Disjoint ⟨B, 8 * W⟩ ∧ (⟨P, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩ ∧
    (⟨P, 8⟩ : Region).Disjoint ⟨B, 8 * W⟩ ∧ (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 8 * W⟩ ∧
    stk.Disjoint ⟨K, 384⟩ ∧ stk.Disjoint ⟨P, 8⟩ ∧ stk.Disjoint ⟨D, 8 * n⟩ ∧ stk.Disjoint ⟨B, 8 * W⟩ ∧
    stkN ≤ (s.gpr .rsp).toNat ∧ ret.Disjoint ⟨P, 8⟩ ∧ ret.Disjoint ⟨D, 8 * n⟩ ∧ ret.Disjoint ⟨B, 8 * W⟩ ∧
    K.toNat + 384 ≤ 2 ^ 64 ∧ P.toNat + 8 ≤ 2 ^ 64 ∧ D.toNat + 8 * n ≤ 2 ^ 64 ∧ B.toNat + 8 * W ≤ 2 ^ 64

theorem Lay.of_preC {s : State} (h : preC s) :
    Lay s (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .rcx).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, i, j, k, l, m, o, p, q, r, t, u, v, w⟩

/-- The function's contract on x86-64. -/
def contract (cfb : Bool) : Contract isa where
  pre := preC
  post s s' :=
    let k := Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)
    let iv := bytesAt s.mem (s.gpr .rsi) 8
    let cs := blocksOf 8 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
    blocksOf 8 s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        (if cfb then Spec.Cfb.decrypt (Spec.TripleDes.cipher k) iv cs
         else Spec.Cbc.decrypt (Spec.TripleDes.invCipher k) iv cs) ∧
      bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next iv cs
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## The entry -/

theorem core_total : core.total = W := rfl
theorem core_slots : core.slots = G + 1 := rfl

theorem regs_ok : RegsOk regs := ⟨by decide, by decide, by decide⟩

theorem entry_wp (cfb : Bool) {s₀ : State} {K P D B : Addr} {n : Nat} (L : Lay s₀ K P D B n)
    (hK : s₀.gpr .rdi = K) (hP : s₀.gpr .rsi = P) (hD : s₀.gpr .rdx = D) (hB : s₀.gpr .r8 = B)
    (hn : (s₀.gpr .rcx).toNat = n) :
    WP isa prologue s₀ fun s => s.zf = some (decide (n = 0)) ∧ Inv cfb s₀ K P D B n 0 s := by
  have hfD := L.fitD
  have hfB := L.fitB
  have hW := W_eq
  have hGe := G_eq
  have wS : (⟨B, 8 * core.ctrSlots⟩ : Region) ∈ s₀.wr := by rw [L.wr]; simp [Core.ctrSlots, core_total]
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok (c := core) (by decide) (by decide) (r := regs) s₀ hB
    ⟨wS, by simp only [Core.ctrSlots, core_total]; omega⟩
  have subM : Region.Sub (modeRegion core B) ⟨B, 8 * W⟩ := Offset.sub_base B (by simp [core_slots]; omega)
  have dPB : Region.Disjoint ⟨P, 8⟩ ⟨B, 8⟩ := L.pb.sub_right (Region.sub_prefix (by omega))
  unfold prologue entry
  rw [show copyW .rax sb .rsi 0 0 0 = (List.range 1).flatMap (copyW .rax sb .rsi 0 0) from rfl]
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨sE, eE, WP.mono (copyN_wp (k := 1) (t := .rax) (rd := sb)
    (rs := .rsi) (od := 0) (os := 0) (P := B) (Q := P)
    ⟨by rw [bE]; simp, by rw [gE _ (by decide), hP]; simp, by decide, by decide,
      fun w hw => by rw [wrE, show w = 0 by omega]; simpa using L.wB (i := 0) (by omega),
      fun w hw => by
        rw [rdE, wrE, show w = 0 by omega]
        exact inRd (inR (R := ⟨P, 8⟩) (by rw [L.wr]; simp) (by simpa using Region.contains_self P 8)),
      dPB.symm, by decide⟩) fun sC hC => ?_⟩))
  have mC : sC.mem = over sE.mem B 8 fun i => sE.mem (P + BitVec.ofNat 64 i) := hC.mem
  have gC : ∀ x, x ≠ sb → x ≠ .rax → sC.gpr x = s₀.gpr x := fun x h1 h2 => by rw [hC.regs x h2, gE x h1]
  -- The P bytes are as on entry.
  have ePC : ∀ u < 8, sC.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [mC, show P + BitVec.ofNat 64 u = (⟨P, 8⟩ : Region).base + BitVec.ofNat 64 u from rfl,
      bytes1 (over_frame _ _ _ _) dPB (by show 8 ≤ 2 ^ 64; decide) hu,
      bytes1 fE (L.pb.sub_right subM) (by show 8 ≤ 2 ^ 64; decide) hu]
  have dDB : Region.Disjoint ⟨D, 8 * n⟩ ⟨B, 8⟩ := L.db.sub_right (Region.sub_prefix (by omega))
  have eDC : ∀ i < 8 * n, sC.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) := fun i hi => by
    rw [mC, show D + BitVec.ofNat 64 i = (⟨D, 8 * n⟩ : Region).base + BitVec.ofNat 64 i from rfl,
      bytes1 (over_frame _ _ _ _) dDB (by simp only; omega) hi,
      bytes1 fE (L.db.sub_right subM) (by simp only; omega) hi]
  refine WP.seq (WP.mono (cbcLastToIv_wp (c := core) (by decide) (by decide) regs_ok (s := sC) (m₀ := s₀.mem)
    (P := P) (D := D) (n := n) (by rw [gC _ (by decide) (by decide)]; exact hP)
    (by rw [gC _ (by decide) (by decide)]; exact hD)
    (by rw [gC _ (by decide) (by decide)]; exact hn) (by rw [hC.wr, wrE, L.wr]; simp [core_bw])
    (by rw [hC.wr, wrE, L.wr]; simp [core_bw]) L.pd hfD (fun i hi => eDC i hi))
    fun sL ⟨gL, fL, ivL, rdL, wrL⟩ => ?_)
  have fL' : Frame [⟨P, 8⟩] sC.mem sL.mem := fL
  have fCo : Frame [⟨B, 8⟩] sE.mem sC.mem := by rw [mC]; exact over_frame _ _ _ _
  have ivL' : bytesAt sL.mem P 8 = Spec.Cbc.next (bytesAt sC.mem P 8) (blocksOf 8 s₀.mem D n) := ivL
  have bPC : bytesAt sC.mem P 8 = bytesAt s₀.mem P 8 := by
    unfold bytesAt; exact List.map_congr_left fun u hu => ePC u (List.mem_range.mp hu)
  rw [bPC] at ivL'
  -- The arguments to the registers the calls keep.
  obtain ⟨s₁, e₁, a₁, b₁, c₁, o₁, m₁, rd₁, wr₁⟩ := mov3_ok sL (a := .r15) (b := .r13) (c := .r12) (x := .rdi)
    (y := sb) (z := .rdx) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r14 .rcx
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := testSelf_ok s₂ .r14
  refine WP.of_runBlock ⟨s₃, by
    rw [show setup = [movR .r15 .rdi, movR .r13 sb, movR .r12 .rdx] ++ ([movR .r14 .rcx] ++
      [.alu .test .r14 (.reg .r14)]) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
      Option.bind_some, e₃], ?_⟩
  have g₃' : ∀ x, x ≠ .r15 → x ≠ .r13 → x ≠ .r12 → x ≠ .r14 → s₃.gpr x = sL.gpr x := fun x h1 h2 h3 h4 => by
    rw [g₃, o₂ x h4, o₁ x h1 h2 h3]
  have gL' : ∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → sL.gpr x = s₀.gpr x := fun x h1 h2 h3 => by
    rw [gL x h2 h3, gC x h1 h2]
  have r14₃ : s₃.gpr .r14 = s₀.gpr .rcx := by
    rw [g₃, a₂, o₁ _ (by decide) (by decide) (by decide), gL' _ (by decide) (by decide) (by decide)]
  have mem₃ : s₃.mem = sL.mem := by rw [m₃, m₂, m₁]
  have dLB : ∀ (R : Region), R.Disjoint ⟨P, 8⟩ → R.len ≤ 2 ^ 64 → ∀ i < R.len,
      s₃.mem (R.base + BitVec.ofNat 64 i) = sC.mem (R.base + BitVec.ofNat 64 i) := fun R hR hl i hi => by
    rw [mem₃]; exact bytes1 fL' hR hl hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, fun u hu => ?_, fun i hi => ?_, ?_, ?_, fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁, rdL, hC.rd, rdE], by rw [wr₃, wr₂, wr₁, wrL, hC.wr, wrE]⟩
  · rw [z₃, show s₂.gpr .r14 = s₀.gpr .rcx by rw [← r14₃, g₃]]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← hn]
    exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  · rw [show s₃.gpr .r15 = s₁.gpr .r15 by rw [g₃, o₂ _ (by decide)], a₁, gL' _ (by decide) (by decide) (by decide), hK]
  · rw [show s₃.gpr .r13 = s₁.gpr .r13 by rw [g₃, o₂ _ (by decide)], b₁, gL _ (by decide) (by decide),
      hC.regs _ (by decide), bE]
  · rw [g₃' _ (by decide) (by decide) (by decide) (by decide), gL _ (by decide) (by decide), hC.regs _ (by decide),
      bE]
  · rw [g₃' _ (by decide) (by decide) (by decide) (by decide), gL' _ (by decide) (by decide) (by decide)]
  · rw [show s₃.gpr .r12 = s₁.gpr .r12 by rw [g₃, o₂ _ (by decide)], c₁,
      gL' _ (by decide) (by decide) (by decide), hD]; simp
  · rw [r14₃, Nat.sub_zero, ← hn]; simp
  · rw [show B + BitVec.ofNat 64 u = (⟨B, 8⟩ : Region).base + BitVec.ofNat 64 u from rfl,
      dLB _ dPB.symm (by show 8 ≤ 2 ^ 64; decide) u hu, mC, over_at hu (by decide), cbcPrev, ite_eq_left rfl,
      bytesAt_getD _ _ hu]
    exact bytes1 fE (L.pb.sub_right subM) (by show 8 ≤ 2 ^ 64; decide) hu
  · rw [show D + BitVec.ofNat 64 i = (⟨D, 8 * n⟩ : Region).base + BitVec.ofNat 64 i from rfl,
      dLB _ L.pd.symm (by simp only; omega) i hi, eDC i hi, ite_eq_right (by omega)]
  · rw [mem₃]
    refine ((fE.sub fun r hr => ?_).trans (fCo.sub fun r hr => ?_)).trans
      (fL'.sub fun r hr => ?_)
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact ⟨_, by simp, subM⟩
    · exact ⟨⟨B, 8 * W⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [mem₃]; exact ivL'
  · have sv := svE i hi
    rw [show wordAddr B (core.slots + i) = B + BitVec.ofNat 64 (8 * (G + 1 + i)) from rfl] at sv
    rw [mem₃, ← sv]
    refine (fL'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans
      (fCo.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact (L.pb.sub_right (Offset.sub_base B (by omega))).symm
    · exact Offset.disjoint_base B (by omega) (by omega)

/-! ## The output -/

theorem outB_cbc (k : Spec.TripleDes.Schedule) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    outB false k m₀ D iv = cbcOut 8 (Spec.TripleDes.invCipher k) m₀ D iv := rfl

theorem input_eq (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    ∀ j, fbIn .cfbDec 8 ciph m₀ D iv j = cbcPrev 8 m₀ D iv j
  | 0 => rfl
  | j + 1 => by simp only [fbIn, fbStep, cbcPrev, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]

theorem xor_comm (a b : List Byte) : Spec.Cbc.xor a b = Spec.Cbc.xor b a := by
  unfold Spec.Cbc.xor
  rw [List.zipWith_comm]
  congr 1; funext x y; exact BitVec.xor_comm _ _

theorem outB_cfb (k : Spec.TripleDes.Schedule) (m₀ : Mem) (D : Addr) (iv : List Byte) :
    outB true k m₀ D iv = fbOut .cfbDec 8 (Spec.TripleDes.cipher k) m₀ D iv := by
  funext j
  simp only [outB, inpB, othB, dir, blockCipher, ite_true, fbOut, input_eq]
  exact xor_comm _ _

theorem cfb_of_dinv {k : Spec.TripleDes.Schedule} {m₀ m : Mem} {D : Addr} {n : Nat} {iv : List Byte}
    (h : DInv 8 m₀ m D n n (fbOut .cfbDec 8 (Spec.TripleDes.cipher k) m₀ D iv)) :
    blocksOf 8 m D n = Spec.Cfb.decrypt (Spec.TripleDes.cipher k) iv (blocksOf 8 m₀ D n) := by
  rw [Proof.Modes.blocksOf_of_dinv (fun j => Proof.Modes.fbOut_length (blockCipher_length k .encrypt) m₀ D iv j) h]
  exact (Proof.Modes.cfbDec_of 8 _ m₀ D iv n).1

/-! ## The whole function -/

theorem decrypt_wp (v : EcbImpl) (cfb : Bool) {s₀ : State} (hp : (contract cfb).pre s₀) :
    WP isa (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))) s₀ fun s' =>
      gprPreserved s₀ s' ∧ (contract cfb).post s₀ s' := by
  have L := Lay.of_preC hp
  have hW := W_eq
  have hGe := G_eq
  unfold decrypt
  refine WP.seq (WP.mono (entry_wp cfb L rfl rfl rfl rfl rfl) fun s ⟨z, h0⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8)
    (s₀.gpr .rcx).toNat (s₀.gpr .rcx).toNat)
    (WP.ite (decide ((s₀.gpr .rcx).toNat = 0)) (by simp [X86_64.eval, z]) (fun h => ?_) (fun h => ?_))
    fun s₄ h₄ => ?_)
  · have e : (s₀.gpr .rcx).toNat = 0 := by simpa using h
    rw [e] at h0 ⊢
    exact WP.block_nil h0
  · exact loop_wp v cfb L h0 (by simp at h; omega)
  · -- The exit.
    obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := loads_ok (B := s₀.gpr .r8) core.slots savedReg 6 s₄ h₄.base
      (by decide) (by decide) (fun i hi => by
        rw [h₄.rd, h₄.wr]
        exact inRd (L.wB (by rw [core_slots]; omega)))
    refine WP.of_runBlock ⟨s₅, e₅, ⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
    · have hsaved : ∀ i < 6, s₅.gpr (savedReg i) = s₀.gpr (savedReg i) := fun i hi => by
        rw [v₅ i hi, ← h₄.saved i hi]; rfl
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsaved 0 (by decide)
      · exact hsaved 1 (by decide)
      · rw [o₅ _ (fun i hi => by revert i; decide), h₄.rsp]
      · exact hsaved 2 (by decide)
      · exact hsaved 3 (by decide)
      · exact hsaved 4 (by decide)
      · exact hsaved 5 (by decide)
    · rw [m₅]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.retB
      · exact L.retD
      · exact L.retP
      · exact Offset.base_disjoint_below _ (by decide)
    · rw [m₅]
      have hd := h₄.data
      cases cfb
      · rw [outB_cbc] at hd
        exact Proof.Modes.cbc_of_dinv (blockCipher_length _ .decrypt) (by simp [bytesAt]) hd
      · rw [outB_cfb] at hd
        exact cfb_of_dinv hd
    · rw [m₅]; exact h₄.iv

/-! ## Constant time -/

open VG VG.X86_64 VG.Impl.TripleDes.X86_64.Batch
open VG.Impl.Aes.X86_64 (sb)

/-- `RelCT.wpDep`, with what each run satisfies stated of its own. -/
theorem _root_.VG.RelCT.wpDep2 {P Q : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → State → Prop}
    (h : RelCT isa P c Q) (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (F₁ s₁) ∧ WP isa c s₂ (F₂ s₂)) :
    RelCT isa P c fun s₁' s₂' => Q s₁' s₂' ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F₁ σ₁ s₁' ∧ F₂ σ₂ s₂' := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩⟩ := hw _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht, hq, _, _, hp, g₁, g₂⟩

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- The registers the loop pins. -/
abbrev loopRegs : List Reg := [sb, .r12, .r13, .r14, .r15, .rsp]

theorem before_taint (cfb : Bool) :
    ∃ h, (taint.check (Taint.ofRegs loopRegs) (before cfb) h).isSome = true := by
  cases cfb
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem after_taint (cfb : Bool) :
    ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15, .rsp]) (after cfb) h).isSome = true := by
  cases cfb
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

section
variable {cfb : Bool} {s₀ s₀' : State} {K P D B : Addr} {n j : Nat}

/-- The registers the loop pins agree in two runs at the same block. -/
theorem Inv.agree (hsp : s₀.gpr .rsp = s₀'.gpr .rsp) {s₁ s₂ : State} (h₁ : Inv cfb s₀ K P D B n j s₁)
    (h₂ : Inv cfb s₀' K P D B n j s₂) : ∀ r ∈ loopRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.base, h₂.base]
  · rw [h₁.dataR, h₂.dataR]
  · rw [h₁.r13, h₂.r13]
  · rw [h₁.leftR, h₂.leftR]
  · rw [h₁.r15, h₂.r15]
  · rw [h₁.rsp, h₂.rsp, hsp]

end

theorem group_rel (v : EcbImpl) (cfb : Bool) {s₀ s₀' : State} {K P D B : Addr} {n : Nat}
    (L₁ : Lay s₀ K P D B n) (L₂ : Lay s₀' K P D B n) (hsp : s₀.gpr .rsp = s₀'.gpr .rsp) {j : Nat} (hj : j < n) :
    RelCT isa (fun s₁ s₂ => Inv cfb s₀ K P D B n j s₁ ∧ Inv cfb s₀' K P D B n j s₂)
      (group cfb (v.name (dir cfb)) (v.code (dir cfb))) fun s₁ s₂ =>
        (s₁.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧ Inv cfb s₀ K P D B n (j + min (n - j) G) s₁) ∧
        (s₂.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧ Inv cfb s₀' K P D B n (j + min (n - j) G) s₂) := by
  have hGe := G_eq
  have hc0 : 0 < min (n - j) G := by omega
  have hjc : j + min (n - j) G ≤ n := by omega
  have hcG : min (n - j) G ≤ G := Nat.min_le_right _ _
  have a := (rel_taintR loopRegs
    (P := fun s₁ s₂ => Inv cfb s₀ K P D B n j s₁ ∧ Inv cfb s₀' K P D B n j s₂) (fun s₁ s₂ h => Inv.agree hsp h.1 h.2) (before_taint cfb)).wpDep2
    (F₁ := Mid cfb s₀ K P D B n j (min (n - j) G)) (F₂ := Mid cfb s₀' K P D B n j (min (n - j) G))
    fun s₁ s₂ h => ⟨before_wp cfb L₁ h.1 hj, before_wp cfb L₂ h.2 hj⟩
  have b := (ecb_rel v (dir cfb) (P := fun a b => True ∧ ∃ σ₁ σ₂,
      (Inv cfb s₀ K P D B n j σ₁ ∧ Inv cfb s₀' K P D B n j σ₂) ∧
      Mid cfb s₀ K P D B n j (min (n - j) G) σ₁ a ∧ Mid cfb s₀' K P D B n j (min (n - j) G) σ₂ b)
    fun a b h => by
      obtain ⟨_, σ₁, σ₂, ⟨i₁, i₂⟩, m₁, m₂⟩ := h
      exact ⟨K, _, _, m₁.callPre L₁ i₁ hjc hc0, m₂.callPre L₂ i₂ hjc hc0,
        by rw [m₁.keep .rsp (by simp), m₂.keep .rsp (by simp), i₁.rsp, i₂.rsp, hsp]⟩).wpDep2
    (F₁ := fun a => EcbCallPost (dir cfb) a K (D + BitVec.ofNat 64 (8 * j)) (min (n - j) G))
    (F₂ := fun a => EcbCallPost (dir cfb) a K (D + BitVec.ofNat 64 (8 * j)) (min (n - j) G))
    fun a b h => by
      obtain ⟨_, σ₁, σ₂, ⟨i₁, i₂⟩, m₁, m₂⟩ := h
      exact ⟨ecb_call v _ (m₁.callPre L₁ i₁ hjc hc0), ecb_call v _ (m₂.callPre L₂ i₂ hjc hc0)⟩
  have c := (rel_taintR [.r12, .r13, .r14, .r15, .rsp] (P := fun a' b' => True ∧ ∃ a b, (True ∧ ∃ σ₁ σ₂,
      (Inv cfb s₀ K P D B n j σ₁ ∧ Inv cfb s₀' K P D B n j σ₂) ∧
      Mid cfb s₀ K P D B n j (min (n - j) G) σ₁ a ∧ Mid cfb s₀' K P D B n j (min (n - j) G) σ₂ b) ∧
      EcbCallPost (dir cfb) a K (D + BitVec.ofNat 64 (8 * j)) (min (n - j) G) a' ∧
      EcbCallPost (dir cfb) b K (D + BitVec.ofNat 64 (8 * j)) (min (n - j) G) b')
    (fun a' b' h r hr => by
      obtain ⟨_, a, b, ⟨_, σ₁, σ₂, ⟨i₁, i₂⟩, m₁, m₂⟩, p₁, p₂⟩ := h
      have hr' : r ∈ loopRegs := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
      rw [p₁.saved r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]),
        p₂.saved r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]),
        m₁.keep r hr, m₂.keep r hr]
      exact Inv.agree hsp i₁ i₂ r hr') (after_taint cfb)).wpDep2
    (F₁ := fun _ s' => s'.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧
      Inv cfb s₀ K P D B n (j + min (n - j) G) s')
    (F₂ := fun _ s' => s'.zf = some (decide (n - (j + min (n - j) G) = 0)) ∧
      Inv cfb s₀' K P D B n (j + min (n - j) G) s')
    fun a' b' h => by
      obtain ⟨_, a, b, ⟨_, σ₁, σ₂, ⟨i₁, i₂⟩, m₁, m₂⟩, p₁, p₂⟩ := h
      exact ⟨after_wp cfb L₁ i₁ hj (Called.of L₁ i₁ hjc hcG m₁ p₁),
        after_wp cfb L₂ i₂ hj (Called.of L₂ i₂ hjc hcG m₂ p₂)⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h).seq
    ((b.mono (fun _ _ h => h) fun _ _ h => h).seq
      (c.mono (fun _ _ h => h) fun _ _ h => by
        obtain ⟨_, _, _, _, h₁, h₂⟩ := h
        exact ⟨h₁, h₂⟩))

/-! ## The loop -/

/-- The loop's relation, with the number of blocks left. -/
def LRel (cfb : Bool) (s₀ s₀' : State) (K P D B : Addr) (n m : Nat) (s₁ s₂ : State) : Prop :=
  ∃ j, m = n - j ∧ j < n ∧ Inv cfb s₀ K P D B n j s₁ ∧ Inv cfb s₀' K P D B n j s₂

theorem loop_rel (v : EcbImpl) (cfb : Bool) {s₀ s₀' : State} {K P D B : Addr} {n : Nat}
    (L₁ : Lay s₀ K P D B n) (L₂ : Lay s₀' K P D B n) (hsp : s₀.gpr .rsp = s₀'.gpr .rsp) (m : Nat) :
    RelCT isa (LRel cfb s₀ s₀' K P D B n m) (.loop (group cfb (v.name (dir cfb)) (v.code (dir cfb))) .ne)
      fun s₁ s₂ => Inv cfb s₀ K P D B n n s₁ ∧ Inv cfb s₀' K P D B n n s₂ := by
  refine RelCT.loop (M := isa) (LRel cfb s₀ s₀' K P D B n) (fun m => ?_) m
  refine (RelCT.exists_ fun j => ?_).mono (fun s₁ s₂ (h : LRel cfb s₀ s₀' K P D B n m s₁ s₂) => h) fun _ _ h => h
  by_cases hm : m = n - j
  swap
  · exact RelCT.of_false fun _ _ h => hm h.1
  subst hm
  by_cases hj : j < n
  swap
  · exact RelCT.of_false fun _ _ h => hj h.2.1
  refine (group_rel v cfb L₁ L₂ hsp hj).mono (fun _ _ h => h.2.2) fun s₁ s₂ ⟨⟨z₁, i₁⟩, ⟨z₂, i₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some (!decide (n - (j + min (n - j) G) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (n - (j + min (n - j) G) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : j + min (n - j) G = n := by
      have : n - (j + min (n - j) G) = 0 := by simpa using hf
      omega
    rw [h0] at i₁ i₂
    exact ⟨i₁, i₂⟩
  · rw [e₁] at ht
    have hGe := G_eq
    have hc0 : 0 < min (n - j) G := by omega
    have h0 : n - (j + min (n - j) G) ≠ 0 := by simpa using ht
    exact ⟨n - (j + min (n - j) G), by omega, _, rfl, by omega, i₁, i₂⟩

/-! ## The whole function -/

theorem prologue_taint :
    ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) prologue h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [sb]) (.block core.restoreRegs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem whole_rel (v : EcbImpl) (cfb : Bool) {s₀ s₀' : State} (h₁ : (contract cfb).pre s₀)
    (h₂ : (contract cfb).pre s₀') (hq : (contract cfb).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have L₁ := Lay.of_preC h₁
  have L₂ : Lay s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat := by
    have := Lay.of_preC h₂; rwa [← q1, ← q2, ← q3, ← q4, ← q5] at this
  let n := (s₀.gpr .rcx).toNat
  have pro := (rel_taintR [.rdi, .rsi, .rdx, .rcx, .r8, .rsp] (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) prologue_taint).wp
    (F₁ := fun (s : State) => s.zf = some (decide (n = 0)) ∧ Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx)
      (s₀.gpr .r8) n 0 s)
    (F₂ := fun (s : State) => s.zf = some (decide (n = 0)) ∧ Inv cfb s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx)
      (s₀.gpr .r8) n 0 s)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨entry_wp cfb L₁ rfl rfl rfl rfl rfl, entry_wp cfb L₂ q1.symm q2.symm q3.symm q5.symm (by rw [← q4])⟩
  have mid : RelCT isa (fun a b => True ∧ (a.zf = some (decide (n = 0)) ∧
        Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n 0 a) ∧
      (b.zf = some (decide (n = 0)) ∧ Inv cfb s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n 0 b))
      (.ite .e (.block []) (.loop (group cfb (v.name (dir cfb)) (v.code (dir cfb))) .ne))
      (fun a b => Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n n a ∧
        Inv cfb s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n n b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · obtain ⟨_, ⟨z₁, _⟩, ⟨z₂, _⟩⟩ := h
      show a.zf = b.zf; rw [z₁, z₂]
    · refine (rel_taintR [] (fun _ _ _ r hr => by simp at hr) nil_taint).wp
        (F₁ := Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n n)
        (F₂ := Inv cfb s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n n) (fun a b h => ?_)
        |>.mono (fun _ _ h => h) fun _ _ h => h.2
      obtain ⟨⟨_, ⟨z₁, i₁⟩, ⟨_, i₂⟩⟩, hz⟩ := h
      have h0 : n = 0 := by
        change a.zf = _ at hz; rw [z₁] at hz; simpa using hz
      rw [show (0 : Nat) = n from h0.symm] at i₁ i₂
      exact ⟨WP.block_nil i₁, WP.block_nil i₂⟩
    · refine (loop_rel v cfb L₁ L₂ q6 (n - 0)).mono (fun a b h => ?_) fun _ _ h => h
      obtain ⟨⟨_, ⟨z₁, i₁⟩, ⟨_, i₂⟩⟩, hz⟩ := h
      change a.zf = _ at hz; rw [z₁] at hz
      have : n ≠ 0 := by simpa using hz
      exact ⟨0, rfl, by omega, i₁, i₂⟩
  have epi := rel_taintR [sb] (P := fun a b => Inv cfb s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx)
      (s₀.gpr .r8) n n a ∧ Inv cfb s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) n n b)
    (fun a b h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.base, h.2.base]) restore_taint
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem decrypt_ct (v : EcbImpl) (cfb : Bool) :
    ConstantTime isa (contract cfb).pre (contract cfb).pub (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel v cfb h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The contracts -/

theorem decrypt_noMxcsr (v : EcbImpl) (cfb : Bool) :
    (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := v.noMxcsr (dir cfb)
  cases cfb <;>
  · simp only [decrypt, group, Code.allInstrs, h, Bool.true_and]
    decide

theorem decrypt_correct (v : EcbImpl) (cfb : Bool) (s : State) (hs : (contract cfb).pre s) :
    ∃ t s', Exec isa (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))) s t s' ∧ abiPreserved s s' ∧
      (contract cfb).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := decrypt_wp v cfb hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_noMxcsr v cfb) he hg, hpost⟩

/-- `contract`, with the postcondition of the shared contracts. -/
def contractS (cfb : Bool) : Contract isa where
  pre := preC
  post s s' :=
    let k := Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)
    let iv := Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) 8
    let cs := Spec.TripleDes.cbcBlocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
    Spec.TripleDes.cbcBlocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        (if cfb then Spec.Cfb.decrypt (Spec.TripleDes.cipher k) iv cs
         else Spec.Cbc.decrypt (Spec.TripleDes.invCipher k) iv cs) ∧
      Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next iv cs
  pub := (contract cfb).pub

theorem post_S {cfb : Bool} {s s' : State} (h : (contract cfb).post s s') : (contractS cfb).post s s' := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h₁
  · rw [cbcBlocksAt_eq]; exact h₂

/-- A state satisfying the precondition (one block). -/
def batchSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * W⟩]

theorem cbc_implies : (contractS false).Implies (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi W 1048) := by
  sig_implies [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
    Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, contractS, contract, preC, X86_64.abi,
    X86_64.argRegs] [batchSat] using batchSat

theorem cfb_implies :
    (contractS true).Implies (Proof.TripleDes.fbScratchContract X86_64.abi W Proof.TripleDes.cfbDecPost 1048) := by
  sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
    Proof.TripleDes.cfbDecPost, contractS, contract, preC, X86_64.abi, X86_64.argRegs] [batchSat] using batchSat

/-- Verified against a contract the function's contract implies. -/
theorem verified_of {v : EcbImpl} {cfb : Bool} {k : Contract isa} (himp : (contractS cfb).Implies k) :
    Verified X86_64.target (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))) k :=
  ⟨fun s hs =>
    let ⟨t, s', he, ha, hp⟩ := decrypt_correct v cfb s (himp.pre s hs)
    ⟨t, s', he, ha, himp.post s s' hs (post_S hp)⟩,
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    decrypt_ct v cfb s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂,
  himp.sat⟩

theorem cbc_verified (v : EcbImpl) :
    Verified X86_64.target (decrypt false (v.name .decrypt) (v.code .decrypt))
      (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi W 1048) :=
  verified_of (v := v) cbc_implies

theorem cfb_verified (v : EcbImpl) :
    Verified X86_64.target (decrypt true (v.name .encrypt) (v.code .encrypt))
      (Proof.TripleDes.fbScratchContract X86_64.abi W Proof.TripleDes.cfbDecPost 1048) :=
  verified_of (v := v) cfb_implies

/-! ## In their frames -/

theorem decrypt_sp (v : EcbImpl) (cfb : Bool) :
    (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))).all (fun i => !isa.writesSp i) = true := by
  have h : (v.code (dir cfb)).allInstrs (fun i => !isa.writesSp i) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi
    simpa using v.spSafe (dir cfb) i hi
  refine Code.all_of_allInstrs ?_
  cases cfb <;>
  · simp only [decrypt, group, Code.allInstrs, h, Bool.true_and]
    decide

theorem decrypt_depth (v : EcbImpl) (cfb : Bool) :
    (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb))).x86_64Depth ≤ 1048 := by
  have h := v.depth (dir cfb)
  have e : ∀ c : Bool, prologue.x86_64Depth = 0 ∧ (before c).x86_64Depth = 0 ∧ (after c).x86_64Depth = 0 := by
    decide
  obtain ⟨e1, e2, e3⟩ := e cfb
  cases cfb <;>
  · simp only [decrypt, group, Code.x86_64Depth, Nat.max_le] at e1 e2 e3 ⊢
    omega

/-- CBC decryption with its working space on the stack. -/
theorem cbc_framed (v : EcbImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 W
        (decrypt false (v.name .decrypt) (v.code .decrypt)))
      (Spec.TripleDes.cbcDecryptChainedContract X86_64.abi 3176) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := W) (post := Proof.TripleDes.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 1048)
    (bytes := 2128) (cbc_verified v) (by decide) (by decide) (by decide) (decrypt_sp v false)
    (decrypt_depth v false) (by decide) (Proof.TripleDes.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 decryption with its working space on the stack. -/
theorem cfb_framed (v : EcbImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 W
        (decrypt true (v.name .encrypt) (v.code .encrypt)))
      (Spec.TripleDes.cfbDecryptContract X86_64.abi 3176) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := W) (post := Proof.TripleDes.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 1048)
    (bytes := 2128) (cfb_verified v) (by decide) (by decide) (by decide) (decrypt_sp v true)
    (decrypt_depth v true) (by decide) (Proof.TripleDes.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem framed_spSafe (v : EcbImpl) (cfb : Bool) :
    (Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 W (decrypt cfb (v.name (dir cfb)) (v.code (dir cfb)))).all
      (fun i => !isa.writesSp i) = true :=
  withStackScratch_spSafe (by decide) (by simp only [Code.all, decrypt_sp v cfb, wipe_spSafe, Bool.and_self])

theorem cbc_spSafe (v : EcbImpl) :
    (Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 W (decrypt false (v.name .decrypt) (v.code .decrypt))).all
      (fun i => !isa.writesSp i) = true := framed_spSafe v false

theorem cfb_spSafe (v : EcbImpl) :
    (Impl.StackScratch.X86_64.withStackScratchWiped 2128 .r8 W (decrypt true (v.name .encrypt) (v.code .encrypt))).all
      (fun i => !isa.writesSp i) = true := framed_spSafe v true

end VG.Proof.TripleDes.X86_64.Batch

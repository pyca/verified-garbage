module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.KeySearchSpec
public import VerifiedGarbage.Proof.RsaKeyGen.SearchFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The controller's public data, its frame and its loop states

`GenPublic` is everything two constant-time runs share: the arguments, the
primes' octets and the exponent. The controller keeps its working state in a
frame of 20 words at `sp - 160` (`GenPublic.F`); a loop state (`GenLive`) is
at an offset into the tape with the search's progress in the state and the
key's buffer.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

structure GenPublic where
  kp : Addr
  up : Addr
  rp : Addr
  B : Addr
  stp : Addr
  sp : Addr
  L : Nat
  randLen : Nat
  Z : Nat
  eB : List Byte

/-- The frame's base. -/
abbrev GenPublic.F (p : GenPublic) : Addr := p.sp - BitVec.ofNat 64 160

/-- The frame's region. -/
abbrev GenPublic.frame (p : GenPublic) : Region := ⟨p.F, 160⟩

/-- The frame's words while the search goes on (but the status, and the
region to zero). -/
def GenPublic.headers (p : GenPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(0, p.kp), (1, BitVec.ofNat 64 p.L), (2, p.up), (3, p.rp), (4, BitVec.ofNat 64 p.randLen), (5, p.B),
    (6, BitVec.ofNat 64 (p.Z / 8)), (7, p.stp), (8, BitVec.ofNat 64 used),
    (11, BitVec.ofNat 64 (limitOf p.L p.eB))]

theorem GenPublic.headers_bound (p : GenPublic) (used : Nat) : ∀ e ∈ p.headers used, e.1 < 20 := by
  simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

def genOfState (s : State) : GenPublic where
  kp := s.gpr .rdi
  up := s.gpr .rdx
  rp := s.gpr .rcx
  B := s.gpr .r9
  stp := stackArg s 1
  sp := s.gpr .rsp
  L := genLen s
  randLen := (s.gpr .r8).toNat
  Z := (stackArg s 0).toNat * 8
  eB := genE s

def GenInput (p : GenPublic) (s : State) : Prop := genPre s ∧ genOfState s = p

/-- The phase's word in the state. -/
def phaseWord : KeyPhase → Nat
  | .p => 0
  | .q _ => 1

/-- The key's buffer's slot `j` (`p_len` octets each). -/
abbrev GenPublic.slot (p : GenPublic) (j : Nat) : Addr := p.kp + BitVec.ofNat 64 (j * p.L)

/-- The state's words for the progress `st`, and the exponent. -/
structure StateOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  remaining : word m p.stp 0 = BitVec.ofNat 64 st.remaining
  len : word m p.stp 8 = BitVec.ofNat 64 p.L
  cap : word m p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L)
  phase : word m p.stp 32 = BitVec.ofNat 64 (phaseWord st.phase)
  left : word m p.stp 40 = BitVec.ofNat 64 st.left
  e : Spec.Rsa.bytesAt m (p.stp + 48) 8 = p.eB
  remaining_le : st.remaining ≤ limitOf p.L p.eB
  left_lt : st.left < 2 ^ 64

/-- The key's buffer for the progress `st`: zeros but `p`'s slot, which holds
`p` for `q`'s search. -/
structure KeyOk (p : GenPublic) (st : KeyProgress) (m : Mem) : Prop where
  low : Spec.Rsa.bytesAt m p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  high : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0
  other : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB

/-- A state of the controller in its frame: `used` octets consumed, the
progress `st` in the state. The entry state is functional-proof data only: its
callee-saved registers may hold secrets, and its tape and key buffer are
secret. -/
structure GenFrame (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop where
  input : GenInput p original
  used_le : used ≤ p.randLen
  rd : s.rd = original.rd
  wr : s.wr = p.frame :: original.wr
  rsp : s.gpr .rsp = p.F
  r12 : s.gpr .r12 = p.F
  saved : ∀ r ∈ calleeSaved, r ≠ .r12 → r ≠ .rsp → s.gpr r = original.gpr r
  savedR12 : word s.mem p.F 72 = original.gpr .r12
  random : Spec.Rsa.bytesAt s.mem p.rp p.randLen = genRand original
  headers : Slots s.mem p.F (p.headers used)
  state : StateOk p st s.mem

/-- A state of the loop: the frame's, and the key's buffer for the progress. -/
structure GenLive (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) (s : State) : Prop
    extends GenFrame p original used st s where
  key : KeyOk p st s.mem

/-- The key search from octet `used` of the tape, from the progress `st`. -/
abbrev tailOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : KeySearchResult :=
  keySearch p.L p.eB st ((genRand original).drop used)

/-- A loop state, whose key search from there finishes as `final`. -/
def GenIter (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (s : State) : Prop :=
  GenLive p original used st s ∧ ∃ tr, final = (tailOf p original used st).consume used tr

end VG.Proof.RsaKeyGen.X86_64.Generate

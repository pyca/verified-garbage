import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# What the modes need of a block cipher's ECB function, on ARMv7

A core (`Impl.Modes.Arm.Core`) is a cipher's ECB function, which the modes
call: `f(schedule = r0, data = r1, n = r2)`, replacing the `n` blocks of
`bs = 4 bw` bytes at `data` with their images under the cipher. `CoreSpec c`
is what the modes' proofs use of `c`, and nothing else: the modes are proven
once, for any core, and each cipher proves `CoreSpec` of its ECB function,
from that function's own (shared) contract.

* `contract`, `correct`, `ct`: the callee's contract, under which its code is
  correct and constant time (a `Verified` proof gives both), using at most
  `stack` bytes below the stack pointer (`depth`).
* `pre_of`: its precondition holds in a state where it may read only the
  `keyLen` bytes at `r0` (the schedule) and write only the blocks at `r1`
  (`EcbPre`), which, with the `stack` bytes below the stack pointer, are
  apart.
* `post_of`: its postcondition makes the blocks their images under
  `ciphAt m K`, the cipher whose schedule is at `K` in the memory `m` on
  entry; `ciphAt` depends only on the schedule's `keyLen` bytes
  (`ciphAt_congr`), and maps blocks to blocks (`cipher_len`).
* `pub_of`: its public data are its arguments and the stack pointer.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- What a call of an ECB function on `n` blocks of `bs` bytes needs, in the
state it is entered in, with only the schedule (`keyLen` bytes) readable
and only the blocks writable. -/
structure EcbPre (bs keyLen stack : Nat) (s : State) : Prop where
  stk : stack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), keyLen⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat * bs⟩]
  kd : Region.Disjoint ⟨State.addr (s.gpr .r0), keyLen⟩ ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat * bs⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩ ⟨State.addr (s.gpr .r0), keyLen⟩
  bd : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩
    ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat * bs⟩
  fK : (s.gpr .r0).toNat + keyLen ≤ 2 ^ 32
  fD : (s.gpr .r1).toNat + (s.gpr .r2).toNat * bs ≤ 2 ^ 32

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  keyLen : Nat
  stack : Nat
  ciphAt : Mem → Addr → Spec.Cbc.Cipher
  contract : Contract isa
  correct : ∀ s, contract.pre s → ∃ t s', Exec isa c.code s t s' ∧ abiPreserved s s' ∧ contract.post s s'
  ct : ConstantTime isa contract.pre contract.pub c.code
  depth : armStack c.code ≤ stack
  pre_of : ∀ s, EcbPre c.bs keyLen stack s → contract.pre s
  post_of : ∀ s s', EcbPre c.bs keyLen stack s → contract.post s s' →
    blocksOf c.bs s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      (blocksOf c.bs s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat).map (ciphAt s.mem (State.addr (s.gpr .r0)))
  pub_of : ∀ s₁ s₂, s₁.sp = s₂.sp → s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    s₁.gpr .r2 = s₂.gpr .r2 → contract.pub s₁ s₂
  ciphAt_congr : ∀ {m m' : Mem} {K : Addr}, (∀ i < keyLen, m (K + BitVec.ofNat 64 i) = m' (K + BitVec.ofNat 64 i)) →
    ciphAt m K = ciphAt m' K
  cipher_len : ∀ m K b, b.length = c.bs → (ciphAt m K b).length = c.bs
  bw_pos : 0 < c.bw
  bw_le : oOff + 2 * c.bs ≤ 4096
  bs_enc : encodable (BitVec.ofNat 32 c.bs) = true

/-! ## A call on one block -/

/-- What a call of the core on the block at `B` needs, from the caller's
state `s`: the schedule at `K`, `n = 1`, room for the callee's stack, and
the regions it is given readable, writable and apart. -/
structure CallPre (c : Core) (S : CoreSpec c) (s : State) (K B : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = B
  r2 : s.gpr .r2 = 1
  stk : S.stack ≤ s.sp.toNat
  fK : K.toNat + S.keyLen ≤ 2 ^ 32
  fB : B.toNat + c.bs ≤ 2 ^ 32
  kb : Region.Disjoint ⟨State.addr K, S.keyLen⟩ ⟨State.addr B, c.bs⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr K, S.keyLen⟩
  bb : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr B, c.bs⟩
  rK : Covers [⟨State.addr K, S.keyLen⟩] (s.rd ++ s.wr)
  wB : Covers [⟨State.addr B, c.bs⟩] s.wr

/-- What a call leaves: the permissions and stack pointer of `s`, its
callee-saved registers but `lr`, memory changed only in the block and the
stack below the stack pointer, and the block its image under the cipher. -/
structure CallPost (c : Core) (S : CoreSpec c) (s : State) (K B : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr B, c.bs⟩, ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩] s.mem s'.mem
  out : bytesAt s'.mem (State.addr B) c.bs = S.ciphAt s.mem (State.addr K) (bytesAt s.mem (State.addr B) c.bs)

theorem one_mul' (n : Nat) : (1 : BitVec 32).toNat * n = n := by simp

theorem blocksOf_one (L : Nat) (m : Mem) (p : Addr) : blocksOf L m p 1 = [bytesAt m p L] := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

/-- The callee's precondition, on the state it is entered in. -/
theorem CallPre.ecbPre {c : Core} {S : CoreSpec c} {s : State} {K B : BitVec 32} (h : CallPre c S s K B) :
    EcbPre c.bs S.keyLen S.stack
      (s.callEntry.withRegions [⟨State.addr K, S.keyLen⟩] [⟨State.addr B, c.bs⟩]) := by
  have g : ∀ r, r ≠ .r12 → r ≠ .lr → (s.callEntry.withRegions [⟨State.addr K, S.keyLen⟩]
      [⟨State.addr B, c.bs⟩]).gpr r = s.gpr r := fun r h1 h2 => by
    rw [State.withRegions_gpr, State.callEntry_gpr s (by simp [linkRegs, h1, h2])]
  refine ⟨by simpa using h.stk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [g .r0 (by decide) (by decide), g .r1 (by decide) (by decide), g .r2 (by decide) (by decide),
      h.r0, h.r1, h.r2, one_mul', State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp]
  · exact h.kb
  · exact h.bk
  · exact h.bb
  · exact h.fK
  · exact h.fB

theorem call_wp {c : Core} (S : CoreSpec c) {s : State} {K B : BitVec 32} (h : CallPre c S s K B) :
    WP isa (.call c.name c.code) s (CallPost c S s K B) := by
  refine WP.callF S.correct (S.pre_of _ h.ecbPre) (Covers.append_left h.rK (Covers.right h.wB))
    h.wB (Nat.le_trans S.depth h.stk) fun s' hrd hwr hsp hf hsv hpost => ⟨hrd, hwr, hsp, hsv, ?_, ?_⟩
  · refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩, by simp, ?_⟩
      have := belowA_sub (sp := s.sp) (b := S.stack) S.depth h.stk
      rwa [belowA, belowA, addr_sub' h.stk] at this
  · have e := S.post_of _ _ h.ecbPre hpost
    have g : ∀ (t : State) r, r ≠ .r12 → r ≠ .lr → (t.callEntry.withRegions [⟨State.addr K, S.keyLen⟩]
        [⟨State.addr B, c.bs⟩]).gpr r = t.gpr r := fun t r h1 h2 => by
      rw [State.withRegions_gpr, State.callEntry_gpr t (by simp [linkRegs, h1, h2])]
    simp only [g s .r0 (by decide) (by decide), g s .r1 (by decide) (by decide), g s .r2 (by decide) (by decide),
      h.r0, h.r1, h.r2, State.withRegions_mem, State.callEntry_mem, blocksOf_one, List.map_cons, List.map_nil,
      show (1 : BitVec 32).toNat = 1 from rfl] at e
    exact List.cons.inj e |>.1

end VG.Proof.Modes.Arm

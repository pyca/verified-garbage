import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Modes.Ctr
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# What the modes need of a block cipher's ECB function, on ARMv7

A core (`Impl.Modes.Arm.Core`) is a cipher's ECB function, which the modes
call: `f(schedule = r0, data = r1, n = r2)`, or `f(schedule = r0, rounds =
r1, data = r2, n = r3)` for a cipher with a number of rounds, replacing the
`n` blocks of `bs = 4 bw` bytes at `data` with their images under the
cipher. `CoreSpec c`
is what the modes' proofs use of `c`, and nothing else: the modes are proven
once, for any core, and each cipher proves `CoreSpec` of its ECB function,
from that function's own (shared) contract.

* `contract`, `correct`, `ct`: the callee's contract, under which its code is
  correct and constant time (a `Verified` proof gives both), using at most
  `stack` bytes below the stack pointer (`depth`).
* `pre_of`: its precondition holds in a state where it may read only the
  `keyLen` bytes at `r0` (the schedule) and write only the blocks (`EcbPre`),
  which, with the `stack` bytes below the stack pointer, are apart, and
  where the number of rounds, if any, satisfies `rok`.
* `post_of`: its postcondition makes the blocks their images under
  `ciphAt m K R`, the cipher whose schedule is at `K` in the memory `m` on
  entry, with `R` rounds (in `r1`; a core without rounds ignores `R`:
  `ciphAt_R`); `ciphAt` depends only on the schedule's `keyLen` bytes
  (`ciphAt_congr`), and maps blocks to blocks (`cipher_len`).
* `pub_of`: its public data are its arguments and the stack pointer.
-/

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Arm.FrameStack VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Modes (blocksOf)

/-- What a call of the ECB function of `c` on `n` blocks needs, in the
state it is entered in, with only the schedule (`keyLen` bytes) readable
and only the blocks writable, and the number of rounds, if any, satisfying
`rok`. -/
structure EcbPre (c : Core) (keyLen stack : Nat) (rok : BitVec 32 → Prop) (s : State) : Prop where
  stk : stack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), keyLen⟩]
  wr : s.wr = [⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩]
  kd : Region.Disjoint ⟨State.addr (s.gpr .r0), keyLen⟩ ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩ ⟨State.addr (s.gpr .r0), keyLen⟩
  bd : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 stack, stack⟩
    ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩
  fK : (s.gpr .r0).toNat + keyLen ≤ 2 ^ 32
  fD : (s.gpr c.dReg).toNat + (s.gpr c.nReg).toNat * c.bs ≤ 2 ^ 32
  rr : c.rounds = true → rok (s.gpr .r1)

/-- What the modes need of the core `c` (see above). -/
structure CoreSpec (c : Core) where
  keyLen : Nat
  stack : Nat
  rok : BitVec 32 → Prop := fun _ => True
  ciphAt : Mem → Addr → BitVec 32 → Spec.Cbc.Cipher
  contract : Contract isa
  correct : ∀ s, contract.pre s → ∃ t s', Exec isa c.code s t s' ∧ abiPreserved s s' ∧ contract.post s s'
  ct : ConstantTime isa contract.pre contract.pub c.code
  depth : armStack c.code ≤ stack
  pre_of : ∀ s, EcbPre c keyLen stack rok s → contract.pre s
  post_of : ∀ s s', EcbPre c keyLen stack rok s → contract.post s s' →
    blocksOf c.bs s'.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat =
      (blocksOf c.bs s.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat).map
        (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
  pub_of : ∀ s₁ s₂, s₁.sp = s₂.sp → s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    s₁.gpr .r2 = s₂.gpr .r2 → (c.rounds = true → s₁.gpr .r3 = s₂.gpr .r3) → contract.pub s₁ s₂
  ciphAt_congr : ∀ {m m' : Mem} {K : Addr} {R : BitVec 32},
    (∀ i < keyLen, m (K + BitVec.ofNat 64 i) = m' (K + BitVec.ofNat 64 i)) → ciphAt m K R = ciphAt m' K R
  ciphAt_R : c.rounds = false → ∀ m K R R', ciphAt m K R = ciphAt m K R'
  cipher_len : ∀ m K R b, b.length = c.bs → (ciphAt m K R b).length = c.bs
  bw_pos : 0 < c.bw
  bw_le : oOff + 2 * c.bs ≤ 4096
  bs_enc : encodable (BitVec.ofNat 32 c.bs) = true

/-! ## A call on one block -/

/-- What a call of the core on the block at `B` needs, from the caller's
state `s`: the schedule at `K`, the number of rounds `R` (if the core takes
one), `n = 1`, room for the callee's stack, and the regions it is given
readable, writable and apart. -/
structure CallPre (c : Core) (S : CoreSpec c) (s : State) (K R B : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : c.rounds = true → s.gpr .r1 = R
  rok : c.rounds = true → S.rok R
  rd : s.gpr c.dReg = B
  rn : s.gpr c.nReg = 1
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
structure CallPost (c : Core) (S : CoreSpec c) (s : State) (K R B : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr B, c.bs⟩, ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩] s.mem s'.mem
  out : bytesAt s'.mem (State.addr B) c.bs = S.ciphAt s.mem (State.addr K) R (bytesAt s.mem (State.addr B) c.bs)

theorem one_mul' (n : Nat) : (1 : BitVec 32).toNat * n = n := by simp

theorem blocksOf_one (L : Nat) (m : Mem) (p : Addr) : blocksOf L m p 1 = [bytesAt m p L] := by
  simp [blocksOf, VG.Proof.Modes.blocksOf]

theorem _root_.VG.Impl.Modes.Arm.Core.dReg_ne (c : Core) : c.dReg ≠ .r12 ∧ c.dReg ≠ .lr ∧ c.dReg ≠ .r0 := by
  unfold Core.dReg; split <;> decide

theorem _root_.VG.Impl.Modes.Arm.Core.nReg_ne (c : Core) : c.nReg ≠ .r12 ∧ c.nReg ≠ .lr ∧ c.nReg ≠ .r0 := by
  unfold Core.nReg; split <;> decide

/-- The registers but `r12` and `lr` on entry to a callee given the regions `rd` and `wr`. -/
theorem entry_gpr (t : State) (rd wr : List Region) {r : Reg} (h1 : r ≠ .r12) (h2 : r ≠ .lr) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr t (by simp [linkRegs, h1, h2])]

/-- The callee's precondition, on the state it is entered in. -/
theorem CallPre.ecbPre {c : Core} {S : CoreSpec c} {s : State} {K R B : BitVec 32} (h : CallPre c S s K R B) :
    EcbPre c S.keyLen S.stack S.rok
      (s.callEntry.withRegions [⟨State.addr K, S.keyLen⟩] [⟨State.addr B, c.bs⟩]) := by
  have hd := c.dReg_ne
  have hn := c.nReg_ne
  refine ⟨by simpa using h.stk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hr => ?_⟩ <;>
    try simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      entry_gpr _ _ _ hn.1 hn.2.1, h.r0, h.rd, h.rn, one_mul', State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp]
  · exact h.kb
  · exact h.bk
  · exact h.bb
  · exact h.fK
  · exact h.fB
  · rw [entry_gpr _ _ _ (by decide) (by decide), h.r1 hr]; exact h.rok hr

theorem call_wp {c : Core} (S : CoreSpec c) {s : State} {K R B : BitVec 32} (h : CallPre c S s K R B) :
    WP isa (.call c.name c.code) s (CallPost c S s K R B) := by
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
    have hd := c.dReg_ne
    have hn := c.nReg_ne
    simp only [entry_gpr _ _ _ (show Reg.r0 ≠ .r12 by decide) (by decide), entry_gpr _ _ _ hd.1 hd.2.1,
      entry_gpr _ _ _ hn.1 hn.2.1, entry_gpr _ _ _ (show Reg.r1 ≠ .r12 by decide) (by decide),
      h.r0, h.rd, h.rn, State.withRegions_mem, State.callEntry_mem, blocksOf_one, List.map_cons, List.map_nil,
      show (1 : BitVec 32).toNat = 1 from rfl] at e
    rw [(List.cons.inj e).1]
    cases hr : c.rounds
    · rw [S.ciphAt_R hr]
    · rw [h.r1 hr]

end VG.Proof.Modes.Arm

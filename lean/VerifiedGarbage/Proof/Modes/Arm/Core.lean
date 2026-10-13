module

public import VerifiedGarbage.Proof.Modes.Arm.Ops
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Modes.Arm.Push
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
* `pre_of`, `post_of` and `pub_of` are needed only of a core that takes no
  working space.

A core that takes a working space as a stack argument (`c.stackScratch ≠ 0`)
is called with it pushed (`Core.callStep`): `pre_ofS`, `post_ofS` and
`pub_ofS` are `pre_of`, `post_of` and `pub_of` for it, from the state it is
entered in with the working space writable and the stack argument readable
(`EcbPreS`), and `stack` covers the push too (`depthS`). A core without one
needs none of them (their defaults).
-/

@[expose] public section

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

/-- What a call of the ECB function of `c` (taking a working space of
`c.stackScratch` bytes as its stack argument) on `n` blocks needs, in the
state it is entered in: as `EcbPre`, with the working space writable, apart
from the other regions, and the stack argument readable; and the
`stack - 8` bytes below the stack pointer (`stack` with the push) apart. -/
structure EcbPreS (c : Core) (keyLen stack : Nat) (rok : BitVec 32 → Prop) (s : State) : Prop where
  stk : stack - 8 ≤ s.sp.toNat
  spF : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r0), keyLen⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩,
    ⟨State.addr (stackArg s 0), c.stackScratch⟩]
  kd : Region.Disjoint ⟨State.addr (s.gpr .r0), keyLen⟩ ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩
  ks : Region.Disjoint ⟨State.addr (s.gpr .r0), keyLen⟩ ⟨State.addr (stackArg s 0), c.stackScratch⟩
  ds : Region.Disjoint ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩
    ⟨State.addr (stackArg s 0), c.stackScratch⟩
  da : Region.Disjoint ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩ ⟨stackArgAddr s 0, 4⟩
  sa : Region.Disjoint ⟨State.addr (stackArg s 0), c.stackScratch⟩ ⟨stackArgAddr s 0, 4⟩
  bk : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 (stack - 8), stack - 8⟩ ⟨State.addr (s.gpr .r0), keyLen⟩
  bd : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 (stack - 8), stack - 8⟩
    ⟨State.addr (s.gpr c.dReg), (s.gpr c.nReg).toNat * c.bs⟩
  bs : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 (stack - 8), stack - 8⟩
    ⟨State.addr (stackArg s 0), c.stackScratch⟩
  ba : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 (stack - 8), stack - 8⟩ ⟨stackArgAddr s 0, 4⟩
  fK : (s.gpr .r0).toNat + keyLen ≤ 2 ^ 32
  fD : (s.gpr c.dReg).toNat + (s.gpr c.nReg).toNat * c.bs ≤ 2 ^ 32
  fS : (stackArg s 0).toNat + c.stackScratch ≤ 2 ^ 32
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
  pre_of : c.stackScratch = 0 → ∀ s, EcbPre c keyLen stack rok s → contract.pre s
  post_of : c.stackScratch = 0 → ∀ s s', EcbPre c keyLen stack rok s → contract.post s s' →
    blocksOf c.bs s'.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat =
      (blocksOf c.bs s.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat).map
        (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1))
  pub_of : c.stackScratch = 0 → ∀ s₁ s₂, s₁.sp = s₂.sp → s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    s₁.gpr .r2 = s₂.gpr .r2 → (c.rounds = true → s₁.gpr .r3 = s₂.gpr .r3) → contract.pub s₁ s₂
  ciphAt_congr : ∀ {m m' : Mem} {K : Addr} {R : BitVec 32},
    (∀ i < keyLen, m (K + BitVec.ofNat 64 i) = m' (K + BitVec.ofNat 64 i)) → ciphAt m K R = ciphAt m' K R
  ciphAt_R : c.rounds = false → ∀ m K R R', ciphAt m K R = ciphAt m K R'
  cipher_len : ∀ m K R b, b.length = c.bs → (ciphAt m K R b).length = c.bs
  bw_pos : 0 < c.bw
  bw_le : oOff + 2 * c.bs ≤ 4096
  bs_enc : encodable (BitVec.ofNat 32 c.bs) = true
  pre_ofS : c.stackScratch ≠ 0 → ∀ s, EcbPreS c keyLen stack rok s → contract.pre s := by
    intro h; exact absurd rfl h
  post_ofS : c.stackScratch ≠ 0 → ∀ s s', EcbPreS c keyLen stack rok s → contract.post s s' →
    blocksOf c.bs s'.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat =
      (blocksOf c.bs s.mem (State.addr (s.gpr c.dReg)) (s.gpr c.nReg).toNat).map
        (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1)) := by
    intro h; exact absurd rfl h
  pub_ofS : c.stackScratch ≠ 0 → ∀ s₁ s₂, s₁.sp = s₂.sp → s₁.gpr .r0 = s₂.gpr .r0 → s₁.gpr .r1 = s₂.gpr .r1 →
    s₁.gpr .r2 = s₂.gpr .r2 → (c.rounds = true → s₁.gpr .r3 = s₂.gpr .r3) → stackArg s₁ 0 = stackArg s₂ 0 →
    contract.pub s₁ s₂ := by
    intro h; exact absurd rfl h
  depthS : c.stackScratch ≠ 0 → armStack c.code + 8 ≤ stack := by intro h; exact absurd rfl h
  cs_enc : c.stackScratch ≠ 0 → encodable (BitVec.ofNat 32 c.csOff) = true := by intro h; exact absurd rfl h

/-! ## A call on one block -/

/-- What a call of the core on the block at `B` needs, from the caller's
state `s`: the schedule at `K`, the number of rounds `R` (if the core takes
one), `n = 1`, room for the callee's stack, and the regions it is given
readable, writable and apart. -/
structure CallPre (c : Core) (S : CoreSpec c) (s : State) (K R B C : BitVec 32) : Prop where
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
  r12 : c.stackScratch ≠ 0 → s.gpr .r12 = C
  fC : c.stackScratch ≠ 0 → C.toNat + c.stackScratch ≤ 2 ^ 32
  kc : Region.Disjoint ⟨State.addr K, S.keyLen⟩ ⟨State.addr C, c.stackScratch⟩
  bc : Region.Disjoint ⟨State.addr B, c.bs⟩ ⟨State.addr C, c.stackScratch⟩
  bC : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ ⟨State.addr C, c.stackScratch⟩
  wC : c.stackScratch ≠ 0 → Covers [⟨State.addr C, c.stackScratch⟩] s.wr

/-- What a call leaves: the permissions and stack pointer of `s`, its
callee-saved registers but `lr`, memory changed only in the block, the
callee's working space and the stack below the stack pointer, and the block
its image under the cipher. -/
structure CallPost (c : Core) (S : CoreSpec c) (s : State) (K R B C : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr B, c.bs⟩, ⟨State.addr C, c.stackScratch⟩,
    ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩] s.mem s'.mem
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
theorem CallPre.ecbPre {c : Core} {S : CoreSpec c} {s : State} {K R B C : BitVec 32} (h : CallPre c S s K R B C) :
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

/-- The call of a core without a working space. -/
theorem callPlain_wp {c : Core} (S : CoreSpec c) {s : State} {K R B C : BitVec 32} (h : CallPre c S s K R B C)
    (hs : c.stackScratch = 0) :
    WP isa (.call c.name c.code) s (CallPost c S s K R B C) := by
  refine WP.callF S.correct (S.pre_of hs _ h.ecbPre) (Covers.append_left h.rK (Covers.right h.wB))
    h.wB (Nat.le_trans S.depth h.stk) fun s' hrd hwr hsp hf hsv hpost => ⟨hrd, hwr, hsp, hsv, ?_, ?_⟩
  · refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩, by simp, ?_⟩
      have := belowA_sub (sp := s.sp) (b := S.stack) S.depth h.stk
      rwa [belowA, belowA, addr_sub' h.stk] at this
  · have e := S.post_of hs _ _ h.ecbPre hpost
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


section
variable {c : Core} {S : CoreSpec c} {s : State} {K R B C : BitVec 32}

/-- The stack holds the push. -/
theorem CallPre.sp8 (h : CallPre c S s K R B C) (hs : c.stackScratch ≠ 0) : 8 ≤ s.sp.toNat := by
  have := S.depthS hs; have := h.stk; omega

omit S in
/-- The callee's stack argument lies in the stack the core may use. -/
theorem argSub {st : Nat} (h : 8 ≤ st) :
    Region.Sub (Push.argR s) ⟨State.addr s.sp - BitVec.ofNat 64 st, st⟩ :=
  VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := st) h (by omega)

/-- The callee's own stack: the `stack - 8` bytes below the push. -/
theorem CallPre.calleeBelow (h : CallPre c S s K R B C) (hs : c.stackScratch ≠ 0) (rd wr : List Region) :
    (⟨State.addr (Push.view s rd wr).sp - BitVec.ofNat 64 (S.stack - 8), S.stack - 8⟩ : Region) =
      ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack - 8⟩ := by
  have := S.depthS hs
  rw [Push.view_addr (h.sp8 hs), show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub,
    ← BitVec.ofNat_add, show 8 + (S.stack - 8) = S.stack by omega]

omit S in
theorem calleeSub (st : Nat) :
    Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 st, st - 8⟩ ⟨State.addr s.sp - BitVec.ofNat 64 st, st⟩ :=
  Region.sub_prefix (by omega)

/-- The callee's precondition, on the state it is entered in, with its
working space pushed. -/
theorem CallPre.ecbPreS (h : CallPre c S s K R B C) (hs : c.stackScratch ≠ 0) :
    EcbPreS c S.keyLen S.stack S.rok
      (Push.view s [⟨State.addr K, S.keyLen⟩, Push.argR s] [⟨State.addr B, c.bs⟩, ⟨State.addr C, c.stackScratch⟩]) := by
  have h8 := h.sp8 hs
  have hst := h.stk
  have hd := c.dReg_ne
  have hn := c.nReg_ne
  have dS := S.depthS hs
  have aS := argSub (s := s) (st := S.stack) (by omega)
  have cS := calleeSub (s := s) S.stack
  have e0 : ∀ r : Reg, r ≠ .r12 → r ≠ .lr → ∀ rd wr, (Push.view s rd wr).gpr r = s.gpr r :=
    fun r a b rd wr => Push.view_gpr _ _ _ _ (by simp [linkRegs, a, b])
  have below_arg : Region.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack - 8⟩ (Push.argR s) := by
    show Region.Disjoint _ ⟨State.addr s.sp - 8, 4⟩
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, VG.Offset.sub_ofNat_eq (State.addr s.sp) (a := 8) (b := S.stack)
      (by omega)]
    exact VG.Offset.base_disjoint _ (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun hr => ?_⟩ <;>
    try simp only [e0 .r0 (by decide) (by decide), e0 _ hd.1 hd.2.1, e0 _ hn.1 hn.2.1, h.r0, h.rd, h.rn, one_mul',
      State.withRegions_rd, State.withRegions_wr, Push.arg0 h8, h.r12 hs, Push.sa0 h8, h.calleeBelow hs]
  · rw [Push.view_sp h8]; omega
  · rw [Push.view_sp h8]; have := s.sp.isLt; omega
  · exact h.kb
  · exact h.kc
  · exact h.bc
  · exact (h.bb.sub_left aS).symm
  · exact (h.bC.sub_left aS).symm
  · exact h.bk.sub_left cS
  · exact h.bb.sub_left cS
  · exact h.bC.sub_left cS
  · exact below_arg
  · exact h.fK
  · exact h.fB
  · exact h.fC hs
  · rw [e0 .r1 (by decide) (by decide), h.r1 hr]; exact h.rok hr

/-- The call of a core with a working space, pushed. -/
theorem callScr_wp (S : CoreSpec c) (h : CallPre c S s K R B C) (hs : c.stackScratch ≠ 0) :
    WP isa (.frame (.push [.r12, .lr]) (.call c.name c.code) (.pop .r12 8)) s (CallPost c S s K R B C) := by
  have h8 := h.sp8 hs
  have dS := S.depthS hs
  have hst := h.stk
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8) (by simp) ?_
  have hsp' : (pushed [.r12, .lr] s).sp = s.sp - BitVec.ofNat 32 8 := rfl
  have hspN : (pushed [.r12, .lr] s).sp.toNat = s.sp.toNat - 8 := by rw [hsp']; exact sub_toNat' h8
  refine WP.callF S.correct (rd := [⟨State.addr K, S.keyLen⟩, Push.argR s])
    (wr := [⟨State.addr B, c.bs⟩, ⟨State.addr C, c.stackScratch⟩]) (S.pre_ofS hs _ (h.ecbPreS hs))
    (Push.cov h8 h.rK (wr := [⟨State.addr B, c.bs⟩, ⟨State.addr C, c.stackScratch⟩])
      (show Covers ([⟨State.addr B, c.bs⟩] ++ [⟨State.addr C, c.stackScratch⟩]) s.wr from Covers.append_left h.wB (h.wC hs)))
    (Push.covW (show Covers ([⟨State.addr B, c.bs⟩] ++ [⟨State.addr C, c.stackScratch⟩]) s.wr from
      Covers.append_left h.wB (h.wC hs)))
    (by rw [hspN]; omega) fun s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost => ?_
  have fK : ∀ i < S.keyLen, (pushed [.r12, .lr] s).mem (State.addr K + BitVec.ofNat 64 i) =
      s.mem (State.addr K + BitVec.ofNat 64 i) := fun i hi =>
    (Push.fA h8).bytes (R := ⟨State.addr K, S.keyLen⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [belowA, addr_sub' h8]
      exact (h.bk.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega) (by omega))).symm)
      (by show S.keyLen ≤ 2 ^ 64; have := h.fK; omega) hi
  have fB : Spec.Aes.bytesAt (pushed [.r12, .lr] s).mem (State.addr B) c.bs = bytesAt s.mem (State.addr B) c.bs :=
    VG.Proof.Modes.bytesAt_frame (Push.fA h8) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [belowA, addr_sub' h8]
      exact (h.bb.sub_left (VG.Offset.sub_below (State.addr s.sp) (a := 8) (b := S.stack) (by omega) (by omega))).symm)
      (by have := h.fB; omega)
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, hsp']; exact BitVec.sub_add_cancel _ _
  · have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    have bel : Region.Sub (belowA s.sp S.stack) ⟨State.addr s.sp - BitVec.ofNat 64 S.stack, S.stack⟩ := by
      rw [belowA, addr_sub' hst]; exact fun _ h => h
    refine ((Push.fA h8).sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun x hx => bel x (belowA_sub (by omega) hst x hx)⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · refine ⟨_, by simp, fun x hx => bel x ?_⟩
        rw [hsp'] at hx
        exact belowA_inner (k := 8) (by omega) hst x hx
  · have e := S.post_ofS hs _ _ (h.ecbPreS hs) hpost
    have hd := c.dReg_ne
    have hn := c.nReg_ne
    have e0 : ∀ r : Reg, r ≠ .r12 → r ≠ .lr → ∀ rd wr, (Push.view s rd wr).gpr r = s.gpr r :=
      fun r a b rd wr => Push.view_gpr _ _ _ _ (by simp [linkRegs, a, b])
    simp only [e0 .r0 (by decide) (by decide), e0 _ hd.1 hd.2.1, e0 _ hn.1 hn.2.1, e0 .r1 (by decide) (by decide),
      h.r0, h.rd, h.rn, State.withRegions_mem, State.callEntry_mem, blocksOf_one, List.map_cons, List.map_nil,
      show (1 : BitVec 32).toNat = 1 from rfl, fB] at e
    rw [popped_mem, (List.cons.inj e).1, S.ciphAt_congr fK]
    cases hr : c.rounds
    · rw [S.ciphAt_R hr]
    · rw [h.r1 hr]

end

/-- The call of a core, with its working space pushed if it takes one. -/
theorem call_wp {c : Core} (S : CoreSpec c) {s : State} {K R B C : BitVec 32} (h : CallPre c S s K R B C) :
    WP isa c.callStep s (CallPost c S s K R B C) := by
  unfold Core.callStep
  split
  · exact callPlain_wp S h ‹_›
  · exact callScr_wp S h ‹_›

end VG.Proof.Modes.Arm

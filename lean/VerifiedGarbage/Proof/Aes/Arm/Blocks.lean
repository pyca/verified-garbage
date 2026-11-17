module

public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Aes.Arm.Ecb
public import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.Arm.Ecb
meta import VerifiedGarbage.Proof.Aes.Arm.Ctr32
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES on whole blocks on ARMv7: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation of
two blocks with `CryptOk`: the prologue saves the callee-saved registers
(as `vg_aes_ctr32`'s does, `Ctr32.lean`), stores `n` in its slot and
bitslices the round keys (`Keys.lean`); the groups (`Ecb.lean`) do the
rest; the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_encrypt_blocks(schedule = r0, rounds = r1,
data = r2, n = r3, scratch = [sp])` (and `vg_aes_decrypt_blocks`, with `f` the
inverse cipher): replaces each of the `n` blocks at `data` with `f rounds w`
of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and the argument on the stack (4
bytes at `sp`), and read and write `data` (`16 n` bytes) and `scratch` (2048
bytes, whose contents on exit are unspecified). These may not overlap each
other, and none may wrap around the end of the (32-bit) address space.
`rounds` is 10, 12 or 14. The pointers, `rounds` and `n` are public; the key
schedule and the data are secret. -/
def blocksArm (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 2048⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    data.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 2048 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      (Spec.Aes.statesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).map
        (f (s.gpr .r1).toNat
          (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open VG.Arm VG.Impl.Aes.Arm in
/-- The bitsliced round keys of the `R`-round schedule `w` in the scratch
buffer at `b`, the first at byte `lastKey - 32 R`, where the key loop leaves
them. -/
abbrev KeysIn (m : Mem) (b : BitVec 32) (R : Nat) (w : List Byte) : Prop :=
  Arm.KeysAt m (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_blocks_keys(schedule = r0, rounds = r1,
scratch = r2)`: bitslices the round keys of the schedule at `schedule` into
`scratch` (`KeysIn`).

The code may read `schedule` (240 bytes) and read and write `scratch` (2048
bytes), which may not overlap, and neither may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. The pointers and `rounds`
are public; the key schedule is secret. -/
def blocksKeysArm : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 2048⟩
    s.rd = [sched] ∧ s.wr = [scratch] ∧ sched.Disjoint scratch ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 2048 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    KeysIn s'.mem (s.gpr .r2) (s.gpr .r1).toNat
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_encrypt_blocks_keyed`: `blocksArm f`, from
the round keys of the schedule at `schedule` bitsliced into `scratch`
(`KeysIn`), which it leaves there. -/
def blocksKeyedArm (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract Arm.isa where
  pre s := (blocksArm f).pre s ∧
    KeysIn s.mem (stackArg s 0) (s.gpr .r1).toNat
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
  post s s' := (blocksArm f).post s s' ∧
    KeysIn s'.mem (stackArg s 0) (s.gpr .r1).toNat
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
  pub := (blocksArm f).pub

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str wp_ldrSp)

section
variable (s₀ : State)

abbrev scP : BitVec 32 := s₀.gpr .r0
abbrev dP : BitVec 32 := s₀.gpr .r2
abbrev nB : Nat := (s₀.gpr .r3).toNat
abbrev bP : BitVec 32 := stackArg s₀ 0
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (scP s₀), 240⟩, argR s₀]
  wr : s₀.wr = [⟨State.addr (dP s₀), 16 * nB s₀⟩, ⟨State.addr (bP s₀), 2048⟩]
  dSD : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (dP s₀), 16 * nB s₀⟩
  dSS : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (bP s₀), 2048⟩
  dDS : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ ⟨State.addr (bP s₀), 2048⟩
  dDA : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ (argR s₀)
  dSA : Region.Disjoint ⟨State.addr (bP s₀), 2048⟩ (argR s₀)
  fitS : (scP s₀).toNat + 240 ≤ 2 ^ 32
  fitD : (dP s₀).toNat + 16 * nB s₀ ≤ 2 ^ 32
  fitB : (bP s₀).toNat + 2048 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rounds : (s₀.gpr .r1).toNat = 10 ∨ (s₀.gpr .r1).toNat = 12 ∨ (s₀.gpr .r1).toNat = 14

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksArm f).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem arg_in {s : State} (hr : argR s ∈ s.rd) : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
  ⟨argR s, List.mem_append_left _ hr, by simp [Region.Contains]⟩

/-- The stack argument is as on entry. -/
theorem stackArg_frame {s s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsp : s'.sp = s.sp)
    (hd : ∀ r ∈ rs, Region.Disjoint (argR s) r) : stackArg s' 0 = stackArg s 0 := by
  simp only [stackArg, stackArgAddr, hsp]
  exact hf.readW (by simp [Region.Contains, stackArgAddr]) hd (by decide)

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n (4 * n) F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  obtain hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 4 * (4 * n) by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-! ## The key loop, counting in the low 4 bits of `lr` -/

theorem and15 {N j : Nat} (hj : j < 16) (hN : 16 * N + 16 ≤ 2 ^ 32) :
    BitVec.ofNat 32 (16 * N + j) &&& 15 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem shr4 {N : Nat} (hN : 16 * N + 16 ≤ 2 ^ 32) : BitVec.ofNat 32 (16 * N) >>> 4 = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
  omega_arith

theorem blocksKeyBody_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {j : Nat} {s : State}
    (hi : KInv s₀ b sc R w j s) (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + j + 1)) :
    WP isa (.block blocksKeyBody) s fun s' =>
      (j = 0 ∧ Arm.eval .ne s' = some false ∧ KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N)) ∨
      (0 < j ∧ Arm.eval .ne s' = some true ∧ KInv s₀ b sc R w (j - 1) s' ∧
        s'.gpr .lr = BitVec.ofNat 32 (16 * N + (j - 1) + 1)) := by
  have hR := hk.rounds
  have hjR := hi.hj
  simp only [blocksKeyBody]
  refine keyFront_ok hk hi fun s₃ hr12 hkp hlr₃ hkeep₃ hrd hwr hsp hfr hkeys => ?_
  simp only [blocksKeyStep]
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_imm (by decide)) fun s₅ u₅ =>
    wp_sub (op2_imm (by decide)) fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_and (op2_imm (by decide))
    fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  obtain hlr₈ : s₈.gpr .lr = BitVec.ofNat 32 (16 * N + j) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hlr₃,
      hlr]
    bv_omega
  obtain hev : Arm.eval .ne s₈ = some (!(BitVec.ofNat 32 j == 0)) := by
    obtain e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by grind
    simp only [Arm.eval, z₈, e0, u₇.gpr]
    rw [show s₆.gpr .lr = BitVec.ofNat 32 (16 * N + j) by
      rw [← hlr₈, f₈.gpr, u₇.other _ (by decide)], and15 (by omega_arith) hN]
  obtain hkeep : ∀ r, r ∉ keyWrites → s₈.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    obtain h5 : r ≠ t0 := fun h => h1 (h ▸ by decide)
    rw [f₈.gpr, u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.other _ h2, hkeep₃ r hr]
  obtain m₈ : s₈.mem = s₃.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, hrd]
  obtain wr₈ : s₈.wr = s₀.wr := by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, hwr]
  obtain sp₈ : s₈.sp = s₀.sp := by rw [f₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, hsp]
  obtain kp₈ : s₈.gpr kp = keyAddr b R j - 32 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), hkp]
  obtain r12₈ : s₈.gpr .r12 = sc + BitVec.ofNat 32 (16 * j) - 16 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hr12]
  rw [← m₈] at hfr hkeys
  by_cases h0 : j = 0
  · subst h0
    exact .inl ⟨rfl, hev.trans (by decide), ⟨kp₈, rd₈, wr₈, sp₈, hkeep, hfr,
      fun i hiR => hkeys i (by omega_arith) hiR⟩, by rw [hlr₈]; rfl⟩
  · have hne : BitVec.ofNat 32 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      simp at this; omega_arith
    refine .inr ⟨by omega_arith, hev.trans (by simpa using hne),
      ⟨by omega_arith, ?_, ?_, rd₈, wr₈, sp₈, hkeep, hfr, fun i hi' hiR => hkeys i (by omega_arith) hiR⟩,
      by rw [hlr₈, show 16 * N + (j - 1) + 1 = 16 * N + j by omega_arith]⟩
    · rw [r12₈]; bv_omega
    · rw [kp₈]; exact keyAddr_pred b hk.rounds (by omega_arith) hi.hj

theorem blocksKeyLoop_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {s : State} (hi : KInv s₀ b sc R w R s)
    (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + R + 1)) :
    WP isa (.loop (.block blocksKeyBody) .ne) s fun s' =>
      KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N) := by
  refine WP.loop (M := isa)
    (fun n s => KInv s₀ b sc R w n s ∧ s.gpr .lr = BitVec.ofNat 32 (16 * N + n + 1))
    (fun n s hs => ?_) R s ⟨hi, hlr⟩
  refine WP.mono (blocksKeyBody_ok hk hN hs.1 hs.2) fun s' h => ?_
  rcases h with ⟨_, hev, hd, hl⟩ | ⟨hn, hev, hi', hlr'⟩
  · exact .inl ⟨hev, hd, hl⟩
  · exact .inr ⟨hev, n - 1, by omega_arith, hi', hlr'⟩

/-! ## The groups and the epilogue -/

/-- The groups and the epilogue, from the state the setup of the round keys
leaves: the registers saved in their slots, the round keys in the scratch
buffer, of which only the first `scratchUsed` bytes have changed, the first
round key's address in `r12`, the data in `r10` and the blocks in `r11`. The
round keys stay as they are. -/
theorem tail_ok {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : Pre s₀) {w : List Byte} {s : State}
    (hkeys : Proof.Aes.KeysIn s.mem (bP s₀) (s₀.gpr .r1).toNat w)
    (h10 : s.gpr .r10 = dP s₀) (h11 : s.gpr .r11 = s₀.gpr .r3)
    (h12 : s.gpr .r12 = bP s₀ + BitVec.ofNat 32 (lastKey - 32 * (s₀.gpr .r1).toNat))
    (hsb : s.gpr sb = bP s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (hev : Arm.eval .eq s = some (s₀.gpr .r3 == 0))
    (hsv : Saved s₀ (State.addr (bP s₀)) s.mem)
    (hfr : Frame [⟨State.addr (bP s₀), scratchUsed⟩] s₀.mem s.mem) :
    WP isa (.seq (.ite .eq (.block []) (.loop (blockGroup crypt2) .ne))
        (.block (.ldrSp .r12 0 :: restoreRegs .r12))) s fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Aes.statesAt s'.mem (State.addr (dP s₀)) (nB s₀) =
        (Spec.Aes.statesAt s₀.mem (State.addr (dP s₀)) (nB s₀)).map (f (s₀.gpr .r1).toNat w) ∧
      Frame [⟨State.addr (bP s₀), scratchUsed⟩, ⟨State.addr (dP s₀), 16 * nB s₀⟩] s₀.mem s'.mem ∧
      Proof.Aes.KeysIn s'.mem (bP s₀) (s₀.gpr .r1).toNat w := by
  obtain hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hfit := hp.fitB
  obtain hwS : (⟨State.addr (bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hwD : (⟨State.addr (dP s₀), 16 * nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := bP s₀
  let B := State.addr b
  let n := nB s₀
  let D := State.addr (dP s₀)
  let R := (s₀.gpr .r1).toNat
  obtain n16 : 16 * n < 2 ^ 64 := by have := hp.fitD; omega_arith
  obtain argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨B, lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  obtain hs : ESetup s b (dP s₀) n R w :=
    { scr := by rw [hwr]; exact hwS
      fit := hfit
      dat := by rw [hwr]; exact hwD
      fitD := hp.fitD
      sep := hp.dDS
      rounds := hp.rounds
      keys := hkeys }
  -- The data is as on entry.
  obtain data : EcbInv s₀.mem s.mem D n (8 * 0) (ecbOut f s₀.mem D R w) := by
    intro i hi
    rw [ite_eq_right (by omega_arith)]
    refine hfr.bytes (R := ⟨D, 16 * n⟩) (fun r hr => ?_) (by simp only; omega_arith) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dDS.sub_right (Region.sub_prefix (by decide))
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s b (dP s₀) n R w) ?_ fun s₁₄ gd => ?_)
  · refine WP.ite (s₀.gpr .r3 == 0) hev (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by
        simp only [beq_iff_eq] at h0; show (s₀.gpr .r3).toNat = 0; rw [h0]; rfl
      exact WP.block_nil ⟨hsb, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega_arith⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      exact groups_ok hcr hs ⟨by omega_arith, by rw [h10]; simp,
        by rw [h11]; simp only [n, nB, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        h12, hsb, rfl, rfl, rfl, Frame.refl _ _, data⟩
  -- The epilogue.
  obtain sv : Saved s₀ B s₁₄.mem := by
    intro i hi
    rw [gd.frame.readW (r := ⟨slotA B (32 + i), 32 / 8⟩) (Region.contains_self _ _)
      (slot_disj_regions hp.dDS (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact hsv i hi
  obtain f₀₁₄ : Frame [⟨B, scratchUsed⟩, ⟨D, 16 * n⟩] s₀.mem s₁₄.mem := by
    refine (hfr.sub fun r hr => ?_).trans (gd.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., VG.Offset.sub_base B (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  refine wp_ldrSp (by omega_arith) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, gd.sp, hsp])
    (by rw [gd.rd, gd.wr, hrd, hwr]; exact arg_in hrA) fun s₁₅ u₁₅ => ?_
  obtain b₁₅ : s₁₅.gpr .r12 = b := by
    rw [u₁₅.gpr]
    have := stackArg_frame f₀₁₄ (by rw [gd.sp, hsp]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact argB (by decide)
      · exact hp.dDA.symm)
    simp only [stackArg, stackArgAddr, gd.sp, hsp] at this
    exact this
  obtain ⟨s₁₆, h₁₆, rg₁₆, fR⟩ := restore_ok (s₀ := s₀) (by decide)
    (by rw [u₁₅.wr, gd.wr, hwr]; exact hwS) hfit b₁₅ (by rw [u₁₅.mem]; exact sv)
  rw [u₁₅.mem] at fR
  -- What is written: the slots and the round keys, and the data.
  obtain fW : Frame [⟨B, scratchUsed⟩, ⟨D, 16 * n⟩] s₀.mem s₁₆.mem :=
    f₀₁₄.trans (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩)
  refine WP.of_runBlock ⟨s₁₆, h₁₆, rg₁₆, ?_, fW, ?_⟩
  · show Spec.Aes.statesAt s₁₆.mem D n = _
    rw [statesAt_of_ecbInv (ecbInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.dDS.sub_right (Region.sub_prefix (by omega_arith))) n16 gd.data)]
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl
  · exact keysAt_frame hfit hR14 fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (scr_disj B (lx := 4 * 41) (y := 224) (ly := 480) (by decide) (by decide)).symm)
      (keysAt_frame hfit hR14 gd.frame (keys_disj_regions hp.dDS) hkeys)

theorem correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : Pre s₀) :
    WP isa (blocks crypt2) s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksArm f).post s₀ s' ∧
        Frame [⟨State.addr (bP s₀), scratchUsed⟩, ⟨State.addr (dP s₀), 16 * nB s₀⟩] s₀.mem s'.mem := by
  obtain hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hfit := hp.fitB
  obtain hwS : (⟨State.addr (bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hwD : (⟨State.addr (dP s₀), 16 * nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hrS : (⟨State.addr (scP s₀), 240⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  obtain hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := bP s₀
  let B := State.addr b
  let n := nB s₀
  let D := State.addr (dP s₀)
  obtain n16 : 16 * n < 2 ^ 64 := by have := hp.fitD; omega_arith
  obtain argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨B, lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  obtain argD : ∀ {x lx : Nat}, x + lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨B + BitVec.ofNat 64 x, lx⟩ :=
    fun h => (hp.dSA.sub_left (sub_scr _ h)).symm
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  simp only [blocksPrologue, blocksKeySetup, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega_arith) (a := stackArgAddr s₀ 0) rfl (arg_in hrA) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain sv₂' : Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  obtain f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  obtain sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  obtain hb₂ : s₂.gpr .r12 = b := by rw [g₂, hb₁]
  obtain hscr₂ : (⟨B, 2048⟩ : Region) ∈ s₂.wr := by rw [wr₂, u₁.wr]; exact hwS
  -- The key loop's setup.
  obtain r0₂ : s₂.gpr .r0 = scP s₀ := by rw [g₂, u₁.other _ (by decide)]
  obtain r1₂ : s₂.gpr .r1 = s₀.gpr .r1 := by rw [g₂, u₁.other _ (by decide)]
  obtain r2₂ : s₂.gpr .r2 = dP s₀ := by rw [g₂, u₁.other _ (by decide)]
  obtain r3₂ : s₂.gpr .r3 = s₀.gpr .r3 := by rw [g₂, u₁.other _ (by decide)]
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide))
    fun s₄ u₄ => wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ =>
    wp_add (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₆' u₆' =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  obtain m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆'.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆'.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆'.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆'.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂']
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (scP s₀)) (16 * (R + 1))
  obtain f₀₇ : Frame [⟨B, 2048⟩] s₀.mem s₇.mem := by
    rw [m₇]
    exact f₀₂.sub fun r hr => ⟨⟨B, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
  obtain hk : KSetup s₇ b (scP s₀) R w :=
    { scr := by rw [wr₇]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₇]; exact hrS)
      fitS := hp.fitS
      sep := hp.dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₇.bytes (R := ⟨State.addr (scP s₀), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dSS }
  obtain hi₇ : KInv s₇ b (scP s₀) R w R s₇ :=
    { hj := Nat.le_refl _
      r12 := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), r0₂, u₃.other _ (by decide), r1₂, shl4]
      kp := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hb₂]
        simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  obtain hN : 16 * n + 16 ≤ 2 ^ 32 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have hD := hp.fitD
    simp only [n, nB] at hc hD
    obtain hz : State.addr (dP s₀) = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [VG.Proof.MdStream.Arm.addr_toNat]; show _ = 0; omega_arith
    refine hp.dDS (State.addr (bP s₀)) ?_ (by
      show (State.addr (bP s₀) - State.addr (bP s₀)).toNat + 1 ≤ 2048; simp)
    show (State.addr (bP s₀) - State.addr (dP s₀)).toNat + 1 ≤ 16 * nB s₀
    obtain e : State.addr (bP s₀) - 0 = State.addr (bP s₀) := by grind
    rw [hz, e, VG.Proof.MdStream.Arm.addr_toNat]
    have := (bP s₀).isLt
    simp only [nB]
    omega_arith
  obtain lr₇ : s₇.gpr .lr = BitVec.ofNat 32 (16 * n + R + 1) := by
    rw [u₇.other _ (by decide), u₆'.gpr, u₆.gpr, u₅.gpr, u₅.other .r1 (by decide),
      u₄.other .r3 (by decide), u₄.other .r1 (by decide), u₃.other .r3 (by decide),
      u₃.other .r1 (by decide), r3₂, r1₂, shl4]
    simp only [n, nB, R]
    bv_omega
  obtain r8₇ : s₇.gpr .r8 = dP s₀ := by
    rw [u₇.gpr, u₆'.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), r2₂]
  -- The key loop.
  refine WP.seq (WP.mono (blocksKeyLoop_ok hk hN hi₇ lr₇) fun s₈ ⟨d₈, lr₈⟩ => ?_)
  obtain f₀₈ : Frame [⟨B, 2048⟩] s₀.mem s₈.mem :=
    f₀₇.trans (d₈.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨B, 2048⟩, by simp, keyArea_sub _⟩)
  obtain sp₈ : s₈.sp = s₀.sp := by rw [d₈.sp, sp₇]
  obtain arg₈ : stackArg s₈ 0 = b := stackArg_frame f₀₈ sp₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact argB (by omega_arith)
  -- After the key loop.
  refine WP.seq ?_
  simp only [blocksKeyDone, List.cons_append, List.nil_append]
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  obtain sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, sp₈]
  obtain rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, d₈.rd, rd₇]
  obtain wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, d₈.wr, wr₇]
  obtain m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
  refine wp_ldrSp (by omega_arith) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, sp₁₀])
    (by rw [rd₁₀, wr₁₀]; exact arg_in hrA) fun s₁₁ u₁₁ => ?_
  obtain b₁₁ : s₁₁.gpr sb = b := by
    rw [u₁₁.gpr, m₁₀]
    have := arg₈
    simp only [stackArg, stackArgAddr, sp₈] at this
    exact this
  refine wp_mov (op2_lsr (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  obtain n₁₂ : s₁₂.gpr .r11 = s₀.gpr .r3 := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), lr₈,
      shr4 hN]
    simp [n]
  obtain b₁₃ : s₁₃.gpr sb = b := by rw [f₁₃.gpr, u₁₂.other _ (by decide), b₁₁]
  obtain d₁₃ : s₁₃.gpr .r10 = dP s₀ := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      d₈.keep _ (by decide), r8₇]
  obtain k₁₃ : s₁₃.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      d₈.kp]
    simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  obtain m₁₃ : s₁₃.mem = s₈.mem := by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  obtain rd₁₃ : s₁₃.rd = s₀.rd := by rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  obtain wr₁₃ : s₁₃.wr = s₀.wr := by rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  obtain sp₁₃ : s₁₃.sp = s₀.sp := by rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀]
  -- The registers are in their slots, and only the slots and the round keys have changed.
  obtain sv₁₃ : Saved s₀ B s₁₃.mem := by
    intro i hi
    rw [m₁₃, d₈.frame.readW (r := ⟨slotA B (32 + i), 32 / 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m₇, sv₂' i hi]
  obtain f₀₁₃ : Frame [⟨B, scratchUsed⟩] s₀.mem s₁₃.mem := by
    rw [m₁₃]
    refine (f₀₂.sub fun r hr => ?_).trans (?_ : Frame _ s₂.mem s₈.mem)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · rw [← m₇]
      exact d₈.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base B (by decide)⟩
  have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by grind
  refine WP.mono (tail_ok hcr hp (w := w) (fun j hj => keyRel_congr (d₈.keys j hj) fun k hk => by
        rw [m₁₃, keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
          simp only [lastKey]; omega_arith])
      d₁₃ (by rw [f₁₃.gpr, n₁₂]) k₁₃ b₁₃ rd₁₃ wr₁₃ sp₁₃ (by simp only [Arm.eval, z₁₃, n₁₂, e0]) sv₁₃ f₀₁₃)
    fun s' ⟨h₁, h₂, h₃, _⟩ => ⟨h₁, h₂, h₃⟩

/-- The callee-saved registers are those the code saves. -/
theorem preserved_of_sreg {s s' : State} (h : ∀ i < 9, s'.gpr (sreg i) = s.gpr (sreg i)) :
    ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by omega_arith)
  · exact h 1 (by omega_arith)
  · exact h 2 (by omega_arith)
  · exact h 3 (by omega_arith)
  · exact h 4 (by omega_arith)
  · exact h 5 (by omega_arith)
  · exact h 6 (by omega_arith)
  · exact h 7 (by omega_arith)
  · exact h 8 (by omega_arith)

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksArm f).pre s) :
    ∃ t s', Exec isa (blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksArm f).post s s' := by
  obtain ⟨t, s', he, h₁, h₂, -⟩ := correct hcr (pre_of hs)
  exact ⟨t, s', he, ⟨preserved_of_sreg h₁, Exec.sp he⟩, h₂⟩

/-- A run changes no byte of `scratch` from offset `scratchUsed` on: it writes
only the slots and the round keys there. -/
theorem blocks_scratch {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s : State} (hs : (Proof.Aes.blocksArm f).pre s) {t : List Leak} {s' : State}
    (he : Exec isa (blocks crypt2) s t s') {i : Nat} (h1 : scratchUsed ≤ i) (h2 : i < 2048) :
    s'.mem (State.addr (stackArg s 0) + BitVec.ofNat 64 i) =
      s.mem (State.addr (stackArg s 0) + BitVec.ofNat 64 i) := by
  obtain hp := pre_of hs
  obtain ⟨t', s'', he', -, -, hf⟩ := correct hcr hp
  obtain ⟨-, rfl⟩ := Exec.det he he'
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [Region.Contains, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
    omega_using [hc, h1, h2]
  · exact hp.dDS _ hc (VG.Offset.contains_base _ (by omega_using [h2]) (by omega_using [h2]))

/-! ## Constant time -/

/-- The initial taint: the pointers, `rounds`, `n` and the stack argument are
public; `r2` points at the data, and the stack argument at the scratch
buffer. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 2048],
    bases := [(.r2, 0)], argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksArm f).pre s) : VG.Arm.Taint.Wf τ₀ s := by
  obtain hp := pre_of h
  obtain e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨hp.dDS, fun _ h => h.elim, trivial⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitD; have := hp.fitB
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega_arith
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.dDA.symm
    · exact hp.dSA.symm
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksArm f).pre s₁) (h₂ : (Proof.Aes.blocksArm f).pre s₂)
    (hpub : (Proof.Aes.blocksArm f).pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [dP, nB, bP, p2, p3, a0]
  · simp only [τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    rw [show k / 4 = 0 by omega_arith]
    exact congrArg _ a0

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.cipher).pre
    (Proof.Aes.blocksArm Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.invCipher).pre
    (Proof.Aes.blocksArm Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 0⟩, ⟨0, 2048⟩]

theorem encryptBlocks_implies :
    (Proof.Aes.blocksArm Spec.Aes.cipher).Implies (Proof.Aes.encryptBlocksRoundsContract Arm.abi) := by
  sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.Aes.Arm.Ecb.sat

theorem decryptBlocks_implies :
    (Proof.Aes.blocksArm Spec.Aes.invCipher).Implies (Proof.Aes.decryptBlocksRoundsContract Arm.abi) := by
  sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.Aes.Arm.Ecb.sat

theorem encryptBlocks_verified :
    Verified Arm.target encryptBlocks (Proof.Aes.encryptBlocksRoundsContract Arm.abi) :=
  Verified.of_correct (blocks_correct encrypt2_cryptOk) encryptBlocks_ct encryptBlocks_implies

theorem decryptBlocks_verified :
    Verified Arm.target decryptBlocks (Proof.Aes.decryptBlocksRoundsContract Arm.abi) :=
  Verified.of_correct (blocks_correct decrypt2_cryptOk) decryptBlocks_ct decryptBlocks_implies

/-! ## The round keys bitsliced once

`vg_aes_blocks_keys` is `blocks`' prologue and key loop, and leaves the
bitsliced round keys in the scratch buffer (`blocksKeysArm`, `KeysIn`);
`vg_aes_encrypt_blocks_keyed` is `blocks` from them, without its key loop,
and leaves them as they are (`blocksKeyedArm`). Their proofs are `blocks`',
split where the key loop ends (`tail_ok`); their contracts are only their
callers': they are internal functions. -/

/-- The round keys stay where the memory changes only apart from the scratch
buffer. -/
theorem keysIn_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R : Nat}
    {w : List Byte} {rs : List Region} (hR : R ≤ 14) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b, 2048⟩ r) (h : Proof.Aes.KeysIn m b R w) :
    Proof.Aes.KeysIn m' b R w :=
  keysAt_frame hfit hR hf (fun r hr => (hd r hr).sub_left (scr_sub _ (x := 224) (lx := 480) (by decide))) h

theorem shl5 (x : BitVec 32) : x <<< 5 = BitVec.ofNat 32 (32 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem keys_wp {s₀ : State} (hp : Proof.Aes.blocksKeysArm.pre s₀) :
    WP isa blocksKeys s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.blocksKeysArm.post s₀ s' := by
  obtain ⟨hrd, hwr, dSS, fitS, hfit, hR⟩ := hp
  obtain hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_arith
  let b := s₀.gpr .r2
  let B := State.addr b
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (16 * (R + 1))
  obtain hwS : (⟨B, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [B, b]
  obtain hrS : (⟨State.addr (s₀.gpr .r0), 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The registers saved.
  unfold blocksKeys
  refine WP.seq ?_
  simp only [keysSetup, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain sv₂' : Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  obtain f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  -- The key loop's setup.
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ =>
    wp_add (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain r0₂ : s₂.gpr .r0 = s₀.gpr .r0 := by rw [g₂, u₁.other _ (by decide)]
  obtain r1₂ : s₂.gpr .r1 = s₀.gpr .r1 := by rw [g₂, u₁.other _ (by decide)]
  obtain hb₂ : s₂.gpr .r12 = b := by rw [g₂, hb₁]
  obtain hk : KSetup s₆ b (s₀.gpr .r0) R w :=
    { scr := by rw [wr₆]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₆]; exact hrS)
      fitS := fitS
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [m₆]
        refine (f₀₂.bytes (R := ⟨State.addr (s₀.gpr .r0), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega_arith)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact dSS.sub_right (Region.sub_prefix (by decide)) }
  obtain hi₆ : KInv s₆ b (s₀.gpr .r0) R w R s₆ :=
    { hj := Nat.le_refl _
      r12 := by
        rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), r0₂,
          u₄.other _ (by decide), u₃.other _ (by decide), r1₂, shl4]
      kp := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hb₂]
        simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega_arith) }
  obtain lr₆ : s₆.gpr .lr = BitVec.ofNat 32 (R + 1) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r1₂]
    simp only [R]
    bv_omega
  obtain r8₆ : s₆.gpr .r8 = b := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hb₂]
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₆ lr₆) fun s₇ d₇ => ?_)
  -- The registers restored.
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => ?_
  obtain b₈ : s₈.gpr .r12 = b := by rw [u₈.gpr, d₇.keep _ (by decide), r8₆]
  obtain sv₈ : Saved s₀ B s₈.mem := by
    intro i hi
    rw [u₈.mem, d₇.frame.readW (r := ⟨slotA B (32 + i), 32 / 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m₆, sv₂' i hi]
  obtain ⟨s₉, h₉, rg₉, fR⟩ := restore_ok (s₀ := s₀) (by decide)
    (by rw [u₈.wr, d₇.wr, wr₆]; exact hwS) hfit b₈ sv₈
  refine WP.of_runBlock ⟨s₉, h₉, rg₉, ?_⟩
  rw [u₈.mem] at fR
  refine keysAt_frame hfit hR14 fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (scr_disj B (lx := 4 * 41) (y := 224) (ly := 480) (by decide) (by decide)).symm) ?_
  exact fun j hj => keyRel_congr (d₇.keys j hj) fun k hk => by
    rw [keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
      simp only [lastKey]; omega_arith]

theorem keys_correct (s : State) (hs : Proof.Aes.blocksKeysArm.pre s) :
    ∃ t s', Exec isa blocksKeys s t s' ∧ abiPreserved s s' ∧ Proof.Aes.blocksKeysArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := keys_wp hs
  exact ⟨t, s', he, ⟨preserved_of_sreg h₁, Exec.sp he⟩, h₂⟩

/-- `blocksKeyed crypt2`, from the round keys of `w` in the scratch buffer:
`f rounds w` of each block, and the round keys as they were. -/
theorem keyed_wp {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : Pre s₀) {w : List Byte}
    (hkeys : Proof.Aes.KeysIn s₀.mem (bP s₀) (s₀.gpr .r1).toNat w) :
    WP isa (blocksKeyed crypt2) s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Spec.Aes.statesAt s'.mem (State.addr (dP s₀)) (nB s₀) =
        (Spec.Aes.statesAt s₀.mem (State.addr (dP s₀)) (nB s₀)).map (f (s₀.gpr .r1).toNat w) ∧
      Proof.Aes.KeysIn s'.mem (bP s₀) (s₀.gpr .r1).toNat w := by
  obtain hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega_arith
  have hfit := hp.fitB
  obtain hwS : (⟨State.addr (bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := bP s₀
  let B := State.addr b
  let R := (s₀.gpr .r1).toNat
  -- The prologue.
  unfold blocksKeyed
  refine WP.seq ?_
  simp only [blocksPrologue, keyedSetup, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega_arith) (a := stackArgAddr s₀ 0) rfl (arg_in hrA) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain sv₂' : Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  obtain f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  obtain hb₂ : s₂.gpr .r12 = b := by rw [g₂, hb₁]
  -- The first round key's address, the data and the blocks.
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_sub (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  obtain m₈ : s₈.mem = s₂.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain g₂' : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other _ hr]
  obtain r11₇ : s₇.gpr .r11 = s₀.gpr .r3 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂' _ (by decide)]
  have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by grind
  refine WP.mono (tail_ok hcr hp (w := w) ?_ ?_ (by rw [f₈.gpr, r11₇]) ?_ ?_
      (by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd])
      (by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr])
      (by rw [f₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp])
      (by simp only [Arm.eval, z₈, r11₇, e0]) (by rw [m₈]; exact sv₂') ?_)
    fun s' ⟨h₁, h₂, _, h₄⟩ => ⟨h₁, h₂, h₄⟩
  · rw [m₈]
    exact keysAt_frame hfit hR14 f₀₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (scr_disj B (lx := 4 * 41) (y := 224) (ly := 480) (by decide) (by decide)).symm) hkeys
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂' _ (by decide)]
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      hb₂, u₄.other _ (by decide), u₃.other _ (by decide), g₂' _ (by decide), shl5]
    simp only [lastKey, b]
    bv_omega
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, hb₂]
  · rw [m₈]
    exact f₀₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem keyed_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksKeyedArm f).pre s) :
    ∃ t s', Exec isa (blocksKeyed crypt2) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksKeyedArm f).post s s' := by
  obtain ⟨t, s', he, h₁, h₂, h₃⟩ := keyed_wp hcr (pre_of hs.1) hs.2
  exact ⟨t, s', he, ⟨preserved_of_sreg h₁, Exec.sp he⟩, h₂, h₃⟩

theorem encryptBlocksKeyed_correct (s : State) (hs : (Proof.Aes.blocksKeyedArm Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocksKeyed s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksKeyedArm Spec.Aes.cipher).post s s' :=
  keyed_correct encrypt2_cryptOk s hs

theorem encryptBlocksKeyed_ct : ConstantTime isa (Proof.Aes.blocksKeyedArm Spec.Aes.cipher).pre
    (Proof.Aes.blocksKeyedArm Spec.Aes.cipher).pub encryptBlocksKeyed :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

/-- The initial taint of `vg_aes_blocks_keys`: the pointers and `rounds` are
public; `r2` points at the scratch buffer. -/
def keysτ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [2048], bases := [(.r2, 0)] }

theorem keys_wf₀ {s : State} (h : Proof.Aes.blocksKeysArm.pre s) : VG.Arm.Taint.Wf keysτ₀ s := by
  obtain ⟨_, hwr, _, _, fB, _⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, keysτ₀], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => by simp [keysτ₀] at h⟩
  · simp only [hwr, List.pairwise_cons, List.not_mem_nil, List.Pairwise.nil, false_implies,
      implies_true, and_true]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [VG.Proof.MdStream.Arm.addr_toNat]; omega_arith
  · intro p hp'
    simp only [keysτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'; simp [VG.Arm.Taint.region, hwr]

theorem keys_ct : ConstantTime isa Proof.Aes.blocksKeysArm.pre Proof.Aes.blocksKeysArm.pub blocksKeys := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) keysτ₀ (fun s₁ s₂ h₁ h₂ hp => ?_) (by taint_decide)
  obtain ⟨p0, p1, p2⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, keys_wf₀ h₁, keys_wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [keysτ₀])⟩
  · simp only [keysτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p2]

end VG.Proof.Aes.Arm.Ecb

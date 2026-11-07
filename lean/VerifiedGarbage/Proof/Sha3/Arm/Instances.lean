module

public import VerifiedGarbage.Proof.Sha3.Arm.Permute
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.Arm.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arm.Shared
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

meta import VerifiedGarbage.Proof.Sha3.Arm.Permute
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.Arm.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arm.Shared
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# SHA-3 and SHAKE on ARMv7: the functions of each instance

Each allocates a frame (`WP.alloc`), stores the callee's stack arguments
and `lr` at its base and sets its register arguments (a block run
instruction by instruction), and calls the sponge function
(`FrameStack.WP.callF`), whose precondition holds of the arguments stored,
and which leaves the frame as it was; then restores `lr`.

The blocks' addresses are `sp` and `r12`, which holds `sp`, and offsets
(`spCheck`), so two runs with the same `sp` leak the same trace
(`spCheck_trace`); the calls are constant time by their callees' proofs
(`RelCT.call`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Instances

open VG VG.Arm VG.Impl.Sha3.Arm.Instances
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad)

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 256 := by simp [rates] at hr; omega

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Blocks whose addresses are `sp` and `r12` -/

/-- Whether every address the block accesses is `sp` and an offset, or
`r12` and an offset once `r12` is known to hold the same value in both
runs (`k`), which only `addSp r12` makes it. -/
def spCheck : Bool → List Instr → Bool
  | _, [] => true
  | k, .addSp d _ :: is => spCheck (k || d == .r12) is
  | k, .str _ n _ :: is => n == .r12 && k && spCheck k is
  | k, .ldrSp t _ :: is => spCheck (k && t != .r12) is
  | k, .mov d _ :: is => spCheck (k && d != .r12) is
  | _, _ :: _ => false

theorem spCheck_trace : ∀ (is : List Instr) (k : Bool), spCheck k is = true →
    ∀ a b a' b' ta tb, a.sp = b.sp → (k = true → a.gpr .r12 = b.gpr .r12) →
      execBlock isa is a = some (a', ta) → execBlock isa is b = some (b', tb) → ta = tb
  | [], _, _, a, b, a', b', ta, tb, _, _, ha, hb => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at ha hb
    rw [← ha.2, ← hb.2]
  | i :: is, k, hc, a, b, a', b', ta, tb, hsp, hk, ha, hb => by
    simp only [execBlock] at ha hb
    split at ha <;> [cases ha; rename_i a₁ e₁]
    split at hb <;> [cases hb; rename_i b₁ e₁']
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at ha hb
    obtain ⟨⟨a'', ta'⟩, ha₁, -, rfl⟩ := ha
    obtain ⟨⟨b'', tb'⟩, hb₁, -, rfl⟩ := hb
    have s₁ := exec_sp e₁
    have s₂ := exec_sp e₁'
    cases i with
    | addSp d imm =>
      simp only [spCheck] at hc
      have h₁ : a₁.gpr .r12 = b₁.gpr .r12 ∨ (k || d == .r12) = false := by
        simp only [isa, exec] at e₁ e₁'
        split at e₁ <;> [rename_i hi; cases e₁]
        simp only [Option.some.injEq] at e₁ e₁'
        simp only [hi, ↓reduceIte, Option.some.injEq] at e₁'
        subst e₁ e₁'
        by_cases hd : d = .r12
        · subst hd; left; simp [State.setReg, hsp]
        · cases k
          · right; simp [hd]
          · left; simp [State.setReg, Ne.symm hd, hk rfl]
      have := spCheck_trace is _ hc a₁ b₁ a'' b'' ta' tb' (by rw [s₁, s₂, hsp])
        (fun h => h₁.resolve_right (by rw [h]; decide)) ha₁ hb₁
      simp only [addrs, List.map_nil, List.nil_append, this]
    | str t n off =>
      simp only [spCheck, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := hc
      have g₁ := exec_gpr (r := .r12) (by rfl) e₁
      have g₂ := exec_gpr (r := .r12) (by rfl) e₁'
      have := spCheck_trace is true hc a₁ b₁ a'' b'' ta' tb' (by rw [s₁, s₂, hsp])
        (fun _ => by rw [g₁, g₂, hk rfl]) ha₁ hb₁
      simp only [addrs, this, hk rfl]
    | ldrSp t off =>
      simp only [spCheck] at hc
      have := spCheck_trace is _ hc a₁ b₁ a'' b'' ta' tb' (by rw [s₁, s₂, hsp]) (fun h => by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        rw [exec_gpr (r := .r12) (by simp [clobbers, dstOf, h.2]) e₁,
          exec_gpr (r := .r12) (by simp [clobbers, dstOf, h.2]) e₁', hk h.1]) ha₁ hb₁
      simp only [addrs, this, hsp]
    | mov d op =>
      simp only [spCheck] at hc
      have := spCheck_trace is _ hc a₁ b₁ a'' b'' ta' tb' (by rw [s₁, s₂, hsp]) (fun h => by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        rw [exec_gpr (r := .r12) (by simp [clobbers, dstOf, h.2]) e₁,
          exec_gpr (r := .r12) (by simp [clobbers, dstOf, h.2]) e₁', hk h.1]) ha₁ hb₁
      simp only [addrs, List.map_nil, List.nil_append, this]
    | _ => simp [spCheck] at hc

/-- Two runs of such a block from states with the same `sp` leak the same trace. -/
theorem RelCT.spBlock {is : List Instr} (hc : spCheck false is = true) {P : State → State → Prop}
    (hP : ∀ a b, P a b → a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro a b ta tb a' b' hp ea eb
  cases ea with
  | block ha =>
    cases eb with
    | block hb => exact ⟨spCheck_trace is false hc a b a' b' ta tb (hP a b hp) (by simp) ha hb, trivial⟩

/-- An allocated frame leaks only what its body does. -/
theorem RelCT.alloc {bytes : Nat} {body : Prog isa} {P : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocated bytes s₁ ∧ b = allocated bytes s₂)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea : ∀ {s a : State}, isa.push (.alloc bytes) s = some a → a = allocated bytes s := by
        intro s a h
        simp only [isa, push] at h
        split at h <;> [cases h; cases h]
        rfl
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, ea p₁, ea p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp only [addrs]

/-! ## Single instructions -/

theorem wcons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 256) :
    exec (.addSp d imm) s = some (s.setReg d (s.sp + BitVec.ofNat 32 imm)) := by
  simp only [exec, h, ite_true]

theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    exec (.ldrSp t off) s = some (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ite_true, State.load32, h, Option.map_some]

theorem exec_movr {s : State} {d m : Reg} : exec (.mov d (.reg m)) s = some (s.setReg d (s.gpr m)) := rfl

theorem exec_li {s : State} {d : Reg} {n : Nat} (h : encodable (BitVec.ofNat 32 n) = true) :
    exec (li d n) s = some (s.setReg d (BitVec.ofNat 32 n)) := by
  simp [li, exec, Op2.eval, h]

theorem sa_eq {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    State.addr (x + BitVec.ofNat 32 d) = State.addr x + BitVec.ofNat 64 d := addr_add h

theorem sa0 (x : BitVec 32) (d : Nat) :
    x + BitVec.ofNat 32 0 + BitVec.ofNat 32 d = x + BitVec.ofNat 32 d := by
  rw [BitVec.add_zero]

/-- Two words of the frame, apart. -/
theorem sa_sep {x : BitVec 32} {a b : Nat} (hab : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : x.toNat + a + 4 ≤ 2 ^ 32)
    (hb : x.toNat + b + 4 ≤ 2 ^ 32) :
    Mem.Sep (State.addr (x + BitVec.ofNat 32 a)) (32 / 8) (State.addr (x + BitVec.ofNat 32 b)) (32 / 8) := by
  rw [sa_eq (by omega), sa_eq (by omega)]
  exact Offset.sep _ hab (by omega) (by omega)

/-- A word of the frame of `B` bytes at `x`. -/
theorem sa_con {x : BitVec 32} {B d : Nat} (hd : d + 4 ≤ B) (hfit : x.toNat + B ≤ 2 ^ 32) :
    (⟨State.addr x, B⟩ : Region).Contains (State.addr (x + BitVec.ofNat 32 d)) (32 / 8) := by
  rw [sa_eq (by omega)]; exact Offset.contains_base _ hd (by omega)

theorem sa_in {x : BitVec 32} {B d : Nat} {rs : List Region} (hfr : ⟨State.addr x, B⟩ ∈ rs)
    (hd : d + 4 ≤ B) (hfit : x.toNat + B ≤ 2 ^ 32) : InRegions rs (State.addr (x + BitVec.ofNat 32 d)) 4 :=
  ⟨_, hfr, sa_con hd hfit⟩

/-! ## `update` -/

/-- `update rate`'s contract on ARMv7: that of `absorb` (`Proof.Sha3.absorbArm`)
with the rate `rate`, and the 16 bytes of stack its frame uses. -/
def updateArm (rate : Nat) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem (State.addr (s.gpr .r0)) rate msg → (s.gpr .r1).toNat = msg.length % rate →
      Repr s'.mem (State.addr (s.gpr .r0)) rate
        (msg ++ bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)) ∧
    (s'.gpr .r0).toNat = ((s.gpr .r1).toNat + (s.gpr .r3).toNat) % rate
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem preserved_lo : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide

/-- After `updateArgs rate`. -/
theorem upd_block {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true) {u : State}
    (hfr : ⟨State.addr u.sp, 16⟩ ∈ u.wr) (hfit : u.sp.toNat + 20 ≤ 2 ^ 32)
    (hin : InRegions (u.rd ++ u.wr) (State.addr (u.sp + BitVec.ofNat 32 16)) 4) :
    WP isa (.block (updateArgs rate)) u fun t =>
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧ Frame [⟨State.addr u.sp, 16⟩] u.mem t.mem ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 0)) 32 = u.gpr .r3 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 4)) 32 =
        u.mem.readW (State.addr (u.sp + BitVec.ofNat 32 16)) 32 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 8)) 32 = u.gpr .lr ∧
      t.gpr .r0 = u.gpr .r0 ∧ t.gpr .r1 = BitVec.ofNat 32 rate ∧ t.gpr .r2 = u.gpr .r1 ∧
      t.gpr .r3 = u.gpr .r2 ∧ ∀ r ∈ preserved, r ≠ .lr → t.gpr r = u.gpr r := by
  have w8 := sa_in (d := 8) hfr (by decide) (by omega)
  have w0 := sa_in (d := 0) hfr (by decide) (by omega)
  have w4 := sa_in (d := 4) hfr (by decide) (by omega)
  have e16 : ((u.mem.writeW (State.addr (u.sp + BitVec.ofNat 32 8)) (u.gpr .lr)).writeW
      (State.addr (u.sp + BitVec.ofNat 32 0)) (u.gpr .r3)).readW
      (State.addr (u.sp + BitVec.ofNat 32 16)) 32 = u.mem.readW (State.addr (u.sp + BitVec.ofNat 32 16)) 32 := by
    rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide)]
  unfold updateArgs
  refine wcons (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w8)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w0)) (wcons (exec_ldrSp (by decide) (by
    simpa only [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.sp_setReg] using hin)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg] using w4))
    (wcons exec_movr (wcons exec_movr (wcons (exec_li hre) (WP.block_nil ?_))))))))
  simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, reduceCtorEq, ite_true, ite_false, sa0, e16]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, fun r hr hl => ?_⟩
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sa_con (by decide) (by omega))).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) (by omega))).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) (by omega))
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · obtain ⟨-, h1, h2, h3, h12⟩ := preserved_lo r hr
    simp only [h1, h2, h3, h12, hl, ite_false]

theorem stateAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 200⟩ r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => hf.bytes (R := ⟨p, 200⟩) hd (by show 200 ≤ 2 ^ 64; decide) hi

theorem bytesAt_frame {rs : List Region} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Sha3.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem disjoint_empty (r : Region) (p : Addr) : r.Disjoint ⟨p, 0⟩ := fun _ _ h => by
  simp only [Region.Contains] at h; omega

theorem covers_of {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := Covers.of_sub h

theorem mem_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by simp⟩

/-- The frame of `B` bytes below `x`, at `sp = x - B`. -/
theorem frame_eq {x : BitVec 32} {B : Nat} (h : B ≤ x.toNat) :
    State.addr (x - BitVec.ofNat 32 B) = State.addr x - BitVec.ofNat 64 B := FrameStack.addr_sub' h

/-- `absorb`'s regions at the call. -/
def updRd (s : State) : List Region :=
  [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, ⟨State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 0), 8⟩]
def updWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr (stackArg s 0), 640⟩]

/-- What holds after `update`'s block, from `s`. -/
structure UpdAt (rate : Nat) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩ :: s.wr
  sp : t.sp = s.sp - BitVec.ofNat 32 16
  frame : Frame [⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩] s.mem t.mem
  w0 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 0)) 32 = s.gpr .r3
  w4 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 4)) 32 = stackArg s 0
  w8 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 8)) 32 = s.gpr .lr
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = BitVec.ofNat 32 rate
  r2 : t.gpr .r2 = s.gpr .r1
  r3 : t.gpr .r3 = s.gpr .r2
  pr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r

theorem upd_args {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true) {s : State}
    (hs : (updateArm rate).pre s) :
    WP isa (.block (updateArgs rate)) (allocated 16 s) (UpdAt rate s) := by
  obtain ⟨p1, -, -, -, -, -, -, -, -, -, -, -, -, e16, efit, -⟩ := hs
  have hE : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := FrameStack.sub_toNat' (by omega)
  have h16 : s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 16 = s.sp + BitVec.ofNat 32 (4 * 0) := by
    rw [BitVec.sub_add_cancel]; simp
  refine WP.mono (upd_block hre (u := allocated 16 s) List.mem_cons_self (by
      show (s.sp - BitVec.ofNat 32 16).toNat + 20 ≤ 2 ^ 32; omega) (by
      show InRegions (s.rd ++ _) (State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 16)) 4
      rw [h16, p1]
      exact ⟨_, by simp [stackArgAddr], Region.contains_self _ _⟩))
    fun t ⟨trd, twr, tsp, tf, t0, t4, t8, tr0, tr1, tr2, tr3, tpr⟩ => ?_
  simp only [allocated] at t4
  exact ⟨trd, twr, tsp, tf, t0, by rw [t4, h16]; rfl, t8, tr0, tr1, tr2, tr3, tpr⟩

theorem upd_pre {rate : Nat} (hr : rate ∈ rates) {s t : State} (hs : (updateArm rate).pre s)
    (hI : UpdAt rate s t) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (updRd s) (updWr s)) ∧
      Covers (updRd s ++ updWr s) (t.rd ++ t.wr) ∧ Covers (updWr s) t.wr := by
  obtain ⟨p1, p2, d1, d2, d3, -, -, d6, -, d8, f1, f2, f3, e16, efit, hpos⟩ := hs
  have hrt := rate_lt hr
  have hE : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := FrameStack.sub_toNat' (by omega)
  have a0 : stackArg t.callEntry 0 = s.gpr .r3 := by
    simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
    exact hI.w0
  have a1 : stackArg t.callEntry 1 = stackArg s 0 := by
    simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_one]
    exact hI.w4
  have eA : stackArgAddr t.callEntry 0 = State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 0) := by
    simp only [stackArgAddr, State.callEntry_sp, hI.sp, Nat.mul_zero]
  have g0 : t.callEntry.gpr .r0 = s.gpr .r0 := by rw [State.callEntry_gpr _ (by decide), hI.r0]
  have g1 : t.callEntry.gpr .r1 = BitVec.ofNat 32 rate := by rw [State.callEntry_gpr _ (by decide), hI.r1]
  have g2 : t.callEntry.gpr .r2 = s.gpr .r1 := by rw [State.callEntry_gpr _ (by decide), hI.r2]
  have g3 : t.callEntry.gpr .r3 = s.gpr .r2 := by rw [State.callEntry_gpr _ (by decide), hI.r3]
  have hrate : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 (by omega)
  have hb : State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 0) =
      State.addr s.sp - BitVec.ofNat 64 16 := by rw [BitVec.add_zero, frame_eq (by omega)]
  have sub : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 16, 8⟩ ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ :=
    Region.sub_prefix (by decide)
  refine ⟨?_, covers_of fun r hr => ?_, covers_of fun r hr => ?_⟩
  · simp only [Proof.Sha3.absorbArm, updRd, updWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions,
      a0, a1, eA, g0, g1, g2, g3, hrate, State.callEntry_sp, hI.sp, hb]
    refine ⟨trivial, trivial, d1, d2, d3, d6.sub_left sub, d8.sub_left sub, f1, f2, f3,
      by rw [hE]; omega, hr, hpos⟩
  · rw [hI.rd, hI.wr, p1, p2]
    simp only [updRd, updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact mem_self (by simp)
    · refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 16), 16⟩, by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero]; simp
    · exact mem_self (by simp)
    · exact mem_self (by simp)
  · rw [hI.wr, p2]
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact mem_self (by simp)
    · exact mem_self (by simp)

theorem absorb_stack : FrameStack.armStack Impl.Sha3.Arm.Stream.absorb = 0 := rfl
theorem pad_stack : FrameStack.armStack Impl.Sha3.Arm.Stream.pad = 0 := rfl
theorem squeeze_stack : FrameStack.armStack Impl.Sha3.Arm.Stream.squeeze = 0 := rfl

theorem update_correct {rate : Nat} (hr : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    {s : State} (hs : (updateArm rate).pre s) :
    WP isa (update rate) s fun s' => abiPreserved s s' ∧ (updateArm rate).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, d6, d7, d8, -, -, -, e16, efit, -⟩ := hs'
  have hE : (s.sp - BitVec.ofNat 32 16).toNat = s.sp.toNat - 16 := FrameStack.sub_toNat' (by omega)
  have hfb := frame_eq (x := s.sp) (B := 16) (by omega)
  unfold update
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega) ?_
  refine WP.seq (WP.mono (upd_args hre hs) fun t hI => ?_)
  obtain ⟨hpre, hc, hw⟩ := upd_pre hr hs hI
  refine WP.seq (FrameStack.WP.callF (k := Proof.Sha3.absorbArm) Stream.Absorb.absorb_verified.1 hpre hc hw
    (by rw [absorb_stack]; omega) fun v vrd vwr vsp vf vpr hpost => ?_)
  have hsub : ∀ r ∈ updWr s ++ [FrameStack.belowA t.sp (FrameStack.armStack Impl.Sha3.Arm.Stream.absorb)],
      Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 8), 4⟩ r := by
    intro r hr
    rw [absorb_stack] at hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    have hs8 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 8), 4⟩
        ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ := by
      rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by decide)
    rcases hr with rfl | rfl | rfl
    · exact d6.sub_left hs8
    · exact d8.sub_left hs8
    · exact disjoint_empty _ _
  have v8 : v.mem.readW (State.addr (s.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 8)) 32 = s.gpr .lr := by
    rw [vf.readW (Region.contains_self _ _) hsub (by decide), hI.w8]
  refine wcons (exec_ldrSp (by decide) (by
    rw [vsp, vrd, vwr, hI.sp, hI.wr]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, sa_con (by decide) (by omega)⟩))
    (WP.block_nil ?_)
  simp only [vsp, hI.sp, v8]
  simp only [Proof.Sha3.absorbArm, State.withRegions_gpr, State.withRegions_mem, stackArg_withRegions] at hpost
  have g0 : t.callEntry.gpr .r0 = s.gpr .r0 := by rw [State.callEntry_gpr _ (by decide), hI.r0]
  have g1 : t.callEntry.gpr .r1 = BitVec.ofNat 32 rate := by rw [State.callEntry_gpr _ (by decide), hI.r1]
  have g2 : t.callEntry.gpr .r2 = s.gpr .r1 := by rw [State.callEntry_gpr _ (by decide), hI.r2]
  have g3 : t.callEntry.gpr .r3 = s.gpr .r2 := by rw [State.callEntry_gpr _ (by decide), hI.r3]
  have a0 : stackArg t.callEntry 0 = s.gpr .r3 := by
    simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
    exact hI.w0
  have hrate : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 (by have := rate_lt hr; omega)
  rw [g0, g1, g2, g3, a0, hrate, State.callEntry_mem] at hpost
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_, ?_⟩
  · simp only [freed, RegUpd.gpr_setReg]
    by_cases hl : r = .lr
    · subst hl; simp
    · simp only [hl, ite_false]
      rw [vpr r hr hl, hI.pr r hr hl]
  · simp only [freed, RegUpd.sp_setReg]; rw [vsp, hI.sp]; exact BitVec.sub_add_cancel _ _
  · have hst : stateAt t.mem (State.addr (s.gpr .r0)) = stateAt s.mem (State.addr (s.gpr .r0)) :=
      stateAt_frame hI.frame fun r hr => by
        rw [List.mem_singleton.mp hr, hfb]; exact d6.symm
    have hd : bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat :=
      bytesAt_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr, hfb]; exact d7.symm)
        (by have := (s.gpr .r3).isLt; omega)
    have := hpost.1 msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp
    rw [hd] at this
    simpa only [freed, RegUpd.mem_setReg] using this
  · simp only [freed, RegUpd.gpr_setReg, reduceCtorEq, ite_false]
    exact hpost.2

theorem upd_entry {rate : Nat} {s t : State} (hI : UpdAt rate s t) :
    t.callEntry.gpr .r0 = s.gpr .r0 ∧ t.callEntry.gpr .r1 = BitVec.ofNat 32 rate ∧
      t.callEntry.gpr .r2 = s.gpr .r1 ∧ t.callEntry.gpr .r3 = s.gpr .r2 ∧
      stackArg t.callEntry 0 = s.gpr .r3 ∧ stackArg t.callEntry 1 = stackArg s 0 := by
  refine ⟨by rw [State.callEntry_gpr _ (by decide), hI.r0], by rw [State.callEntry_gpr _ (by decide), hI.r1],
    by rw [State.callEntry_gpr _ (by decide), hI.r2], by rw [State.callEntry_gpr _ (by decide), hI.r3], ?_, ?_⟩
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
    exact hI.w0
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_one]
    exact hI.w4

theorem upd_call {rate : Nat} (hr : rate ∈ rates) {s t : State} (hs : (updateArm rate).pre s)
    (hI : UpdAt rate s t) :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.Arm.Stream.absorb) t
      fun v => v.sp = s.sp - BitVec.ofNat 32 16 := by
  obtain ⟨hpre, hc, hw⟩ := upd_pre hr hs hI
  exact FrameStack.WP.callF (k := Proof.Sha3.absorbArm) Stream.Absorb.absorb_verified.1 hpre hc hw
    (by rw [absorb_stack]; omega) fun v _ _ vsp _ _ _ => by rw [vsp, hI.sp]

theorem update_ct {rate : Nat} (hr : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hc : spCheck false (updateArgs rate) = true) :
    ConstantTime isa (updateArm rate).pre (updateArm rate).pub (update rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, q0, q1, q2, q3, q4⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (update rate) fun _ _ => True := by
    unfold update
    refine RelCT.alloc (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := UpdAt rate σ₁) (F₂ := UpdAt rate σ₂)
      (RelCT.spBlock hc fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; simp only [allocated, hsp])
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨upd_args hre p₁, upd_args hre p₂⟩) ?_)
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp
      (F₁ := fun v : State => v.sp = σ₁.sp - BitVec.ofNat 32 16)
      (F₂ := fun v : State => v.sp = σ₂.sp - BitVec.ofNat 32 16)
      (RelCT.call Stream.Absorb.absorb_verified.1 Stream.Absorb.absorb_verified.2.1
        (updRd σ₁) (updWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_))
      fun a b ⟨_, ha', hb'⟩ => ⟨upd_call hr p₁ ha', upd_call hr p₂ hb'⟩) ?_
    · obtain ⟨x1, x2, x3⟩ := upd_pre hr p₁ ha'
      obtain ⟨y1, y2, y3⟩ := upd_pre hr p₂ hb'
      have er : updRd σ₂ = updRd σ₁ := by simp only [updRd, q2, q3, hsp]
      have ew : updWr σ₂ = updWr σ₁ := by simp only [updWr, q0, q4]
      rw [er, ew] at y1 y2
      rw [ew] at y3
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := upd_entry ha'
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := upd_entry hb'
      refine ⟨x1, y1, ?_, x2, x3, y2, y3⟩
      simp only [Proof.Sha3.absorbArm, State.withRegions_gpr, State.withRegions_sp,
        stackArg_withRegions, State.callEntry_sp]
      exact ⟨by rw [ha'.sp, hb'.sp, hsp], by rw [a0, b0, q0], by rw [a1, b1], by rw [a2, b2, q1],
        by rw [a3, b3, q2], by rw [a4, b4, q3], by rw [a5, b5, q4]⟩
    exact RelCT.spBlock rfl fun a b ⟨_, ha, hb⟩ => by rw [ha, hb, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying `updateArm`'s precondition (with no data, and the working space at 0). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x1000, 200⟩, ⟨0, 640⟩]

theorem update_verified {rate : Nat} (hr : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hct : ConstantTime isa (updateArm rate).pre (updateArm rate).pub (update rate))
    (hsat : ∃ s, (updateArm rate).pre s)
    (himp : (updateArm rate).Implies (Spec.Sha3.updateContract Arm.abi rate 16)) :
    Verified Arm.target (update rate) (Spec.Sha3.updateContract Arm.abi rate 16) :=
  (show Verified Arm.target (update rate) (updateArm rate) from
    ⟨fun _ hs => (update_correct hr hre hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      hsat⟩).of_implies himp

/-- `update` for the rate of `I`, from the checks the kernel evaluates on its instance. -/
macro "upd_arm" I:ident : term => `(update_verified (by decide) (by decide)
  (update_ct (by decide) (by decide) rfl)
  ⟨updSat, by
    have e : stackArg updSat 0 = 0 := by simp [stackArg, updSat, Mem.readW, Mem.read]
    simp only [updateArm, e, updSat]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      by decide, by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)⟩
  (by contract_implies [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
      Spec.Sha3.updatePost, updateArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Shared.setWidth_append32, $I:ident]
      [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using updSat))

theorem update_sha3_224 :
    Verified Arm.target (update Spec.Sha3.hashSha3_224.rate)
      (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_224.rate 16) :=
  upd_arm Spec.Sha3.hashSha3_224

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on ARMv7 for `X`: `pad`'s, with SHAKE's
suffix, its working space in a frame of 648 bytes. -/
def xofFinArm (X : Xof) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 648, 648⟩
    s.rd = [] ∧ s.wr = [state] ∧ stack.Disjoint state ∧ (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧
    648 ≤ s.sp.toNat ∧ (s.gpr .r1).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) X.rate msg →
    (s.gpr .r1).toNat = msg.length % X.rate →
    XofRepr s'.mem (State.addr (s.gpr .r0)) X.rate 0 X.xof msg 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

/-- What holds after SHAKE's `finalize`'s block, from `s`. -/
structure XpAt (rate : Nat) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 648), 648⟩ :: s.wr
  sp : t.sp = s.sp - BitVec.ofNat 32 648
  frame : Frame [⟨State.addr (s.sp - BitVec.ofNat 32 648), 648⟩] s.mem t.mem
  w0 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 0)) 32 =
    s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 8
  w4 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 4)) 32 = s.gpr .lr
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = BitVec.ofNat 32 rate
  r2 : t.gpr .r2 = s.gpr .r1
  r3 : t.gpr .r3 = BitVec.ofNat 32 0x1f
  pr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r

/-- After `xofPadArgs rate`. -/
theorem xp_block {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true) {u : State}
    (hfr : ⟨State.addr u.sp, 648⟩ ∈ u.wr) (hfit : u.sp.toNat + 648 ≤ 2 ^ 32) :
    WP isa (.block (xofPadArgs rate)) u fun t =>
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧ Frame [⟨State.addr u.sp, 648⟩] u.mem t.mem ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 0)) 32 = u.sp + BitVec.ofNat 32 8 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 4)) 32 = u.gpr .lr ∧
      t.gpr .r0 = u.gpr .r0 ∧ t.gpr .r1 = BitVec.ofNat 32 rate ∧ t.gpr .r2 = u.gpr .r1 ∧
      t.gpr .r3 = BitVec.ofNat 32 0x1f ∧ ∀ r ∈ preserved, r ≠ .lr → t.gpr r = u.gpr r := by
  have w4 := sa_in (d := 4) hfr (by decide) hfit
  have w0 := sa_in (d := 0) hfr (by decide) hfit
  unfold xofPadArgs
  refine wcons (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w4)) (wcons
    (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg,
      RegUpd.sp_setReg] using w0))
    (wcons exec_movr (wcons (exec_li hre) (wcons (exec_li (by decide)) (WP.block_nil ?_)))))))
  simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, reduceCtorEq, ite_true, ite_false, sa0]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, trivial, trivial, trivial, trivial, fun r hr hl => ?_⟩
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)
  · rw [Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · obtain ⟨-, h1, h2, h3, h12⟩ := preserved_lo r hr
    simp only [h1, h2, h3, h12, hl, ite_false]

theorem xp_args {X : Xof} (hre : encodable (BitVec.ofNat 32 X.rate) = true) {s : State}
    (hs : (xofFinArm X).pre s) :
    WP isa (.block (xofPadArgs X.rate)) (allocated 648 s) (XpAt X.rate s) := by
  obtain ⟨-, -, -, -, e648, -⟩ := hs
  have hE : (s.sp - BitVec.ofNat 32 648).toNat = s.sp.toNat - 648 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  exact WP.mono (xp_block hre (u := allocated 648 s) List.mem_cons_self (by
      show (s.sp - BitVec.ofNat 32 648).toNat + 648 ≤ 2 ^ 32; omega))
    fun t ⟨trd, twr, tsp, tf, t0, t4, tr0, tr1, tr2, tr3, tpr⟩ =>
      ⟨trd, twr, tsp, tf, t0, t4, tr0, tr1, tr2, tr3, tpr⟩

def xpRd (s : State) : List Region := [⟨State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 0), 4⟩]
def xpWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 8), 640⟩]

theorem xp_entry {rate : Nat} {s t : State} (hI : XpAt rate s t) :
    t.callEntry.gpr .r0 = s.gpr .r0 ∧ t.callEntry.gpr .r1 = BitVec.ofNat 32 rate ∧
      t.callEntry.gpr .r2 = s.gpr .r1 ∧ t.callEntry.gpr .r3 = BitVec.ofNat 32 0x1f ∧
      stackArg t.callEntry 0 = s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 8 := by
  refine ⟨by rw [State.callEntry_gpr _ (by decide), hI.r0], by rw [State.callEntry_gpr _ (by decide), hI.r1],
    by rw [State.callEntry_gpr _ (by decide), hI.r2], by rw [State.callEntry_gpr _ (by decide), hI.r3], ?_⟩
  simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
  exact hI.w0

theorem xp_pre {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofFinArm X).pre s)
    (hI : XpAt X.rate s t) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions (xpRd s) (xpWr s)) ∧
      Covers (xpRd s ++ xpWr s) (t.rd ++ t.wr) ∧ Covers (xpWr s) t.wr := by
  obtain ⟨p1, p2, d1, f1, e648, hpos⟩ := hs
  obtain ⟨g0, g1, g2, -, a0⟩ := xp_entry hI
  have hrt := rate_lt hr
  have hsp := s.sp.isLt
  have hE : (s.sp - BitVec.ofNat 32 648).toNat = s.sp.toNat - 648 := FrameStack.sub_toNat' (by omega)
  have eA : stackArgAddr t.callEntry 0 = State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 0) := by
    simp only [stackArgAddr, State.callEntry_sp, hI.sp, Nat.mul_zero]
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  have hfb := frame_eq (x := s.sp) (B := 648) (by omega)
  have hA : State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 0) =
      State.addr s.sp - BitVec.ofNat 64 648 := by rw [BitVec.add_zero, hfb]
  have hC : State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 8) =
      State.addr s.sp - BitVec.ofNat 64 648 + BitVec.ofNat 64 8 := by rw [sa_eq (by omega), hfb]
  have sA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 648, 4⟩ ⟨State.addr s.sp - BitVec.ofNat 64 648, 648⟩ :=
    Region.sub_prefix (by decide)
  have sC : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 648 + BitVec.ofNat 64 8, 640⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 648, 648⟩ := Offset.sub_base _ (by decide)
  refine ⟨?_, covers_of fun r hr => ?_, covers_of fun r hr => ?_⟩
  · simp only [Proof.Sha3.padArm, xpRd, xpWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions,
      a0, eA, g0, g1, g2, hrate, State.callEntry_sp, hI.sp, hA, hC]
    refine ⟨trivial, trivial, (d1.sub_left sC).symm, d1.sub_left sA,
      Offset.base_disjoint _ (by decide) (by omega), f1, ?_, by rw [hE]; omega, hr, hpos⟩
    rw [BitVec.toNat_add, hE, BitVec.toNat_ofNat]; omega
  · rw [hI.rd, hI.wr, p1, p2]
    simp only [xpRd, xpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 648), 648⟩, by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero]; simp
    · exact mem_self (by simp)
    · refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 648), 648⟩, by simp, 8, sa_eq (by omega), by simp⟩
  · rw [hI.wr, p2]
    simp only [xpWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact mem_self (by simp)
    · exact ⟨⟨State.addr (s.sp - BitVec.ofNat 32 648), 648⟩, by simp, 8, sa_eq (by omega), by simp⟩

theorem xof_correct {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 X.rate) = true) {s : State} (hs : (xofFinArm X).pre s) :
    WP isa (xofFinalize X.rate) s fun s' => abiPreserved s s' ∧ (xofFinArm X).post s s' := by
  have hs' := hs
  obtain ⟨-, -, d1, -, e648, -⟩ := hs'
  have hE : (s.sp - BitVec.ofNat 32 648).toNat = s.sp.toNat - 648 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  have hfb := frame_eq (x := s.sp) (B := 648) (by omega)
  unfold xofFinalize
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega) ?_
  refine WP.seq (WP.mono (xp_args hre hs) fun t hI => ?_)
  obtain ⟨hpre, hc, hw⟩ := xp_pre hr hs hI
  refine WP.seq (FrameStack.WP.callF (k := Proof.Sha3.padArm) Stream.Pad.pad_verified.1 hpre hc hw
    (by rw [pad_stack]; omega) fun v vrd vwr vsp vf vpr hpost => ?_)
  have hs4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 4), 4⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 648, 648⟩ := by
    rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by decide)
  have hsub : ∀ r ∈ xpWr s ++ [FrameStack.belowA t.sp (FrameStack.armStack Impl.Sha3.Arm.Stream.pad)],
      Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 4), 4⟩ r := by
    intro r hr
    rw [pad_stack] at hr
    simp only [xpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d1.sub_left hs4
    · rw [sa_eq (by omega), sa_eq (by omega), hfb]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact disjoint_empty _ _
  have v4 : v.mem.readW (State.addr (s.sp - BitVec.ofNat 32 648 + BitVec.ofNat 32 4)) 32 = s.gpr .lr := by
    rw [vf.readW (Region.contains_self _ _) hsub (by decide), hI.w4]
  refine wcons (exec_ldrSp (by decide) (by
    rw [vsp, vrd, vwr, hI.sp, hI.wr]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, sa_con (by decide) (by omega)⟩))
    (WP.block_nil ?_)
  simp only [vsp, hI.sp, v4]
  obtain ⟨g0, g1, g2, g3, -⟩ := xp_entry hI
  simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem] at hpost
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by have := rate_lt hr; omega)
  have hsuf : (BitVec.ofNat 32 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  rw [g0, g1, g2, g3, hrate, hsuf, State.callEntry_mem] at hpost
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_⟩
  · simp only [freed, RegUpd.gpr_setReg]
    by_cases hl : r = .lr
    · subst hl; simp
    · simp only [hl, ite_false]
      rw [vpr r hr hl, hI.pr r hr hl]
  · simp only [freed, RegUpd.sp_setReg]; rw [vsp, hI.sp]; exact BitVec.sub_add_cancel _ _
  · have hst : stateAt t.mem (State.addr (s.gpr .r0)) = stateAt s.mem (State.addr (s.gpr .r0)) :=
      stateAt_frame hI.frame fun r hr => by
        rw [List.mem_singleton.mp hr, hfb]; exact d1.symm
    have := hpost msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp
    simpa only [freed, RegUpd.mem_setReg] using xofRepr_pad hX this

theorem xp_call {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofFinArm X).pre s)
    (hI : XpAt X.rate s t) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.Arm.Stream.pad) t
      fun v => v.sp = s.sp - BitVec.ofNat 32 648 := by
  obtain ⟨hpre, hc, hw⟩ := xp_pre hr hs hI
  exact FrameStack.WP.callF (k := Proof.Sha3.padArm) Stream.Pad.pad_verified.1 hpre hc hw
    (by rw [pad_stack]; omega) fun v _ _ vsp _ _ _ => by rw [vsp, hI.sp]

theorem xof_ct {X : Xof} (hr : X.rate ∈ rates) (hre : encodable (BitVec.ofNat 32 X.rate) = true)
    (hc : spCheck false (xofPadArgs X.rate) = true) :
    ConstantTime isa (xofFinArm X).pre (xofFinArm X).pub (xofFinalize X.rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, q0, q1⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (xofFinalize X.rate) fun _ _ => True := by
    unfold xofFinalize
    refine RelCT.alloc (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := XpAt X.rate σ₁) (F₂ := XpAt X.rate σ₂)
      (RelCT.spBlock hc fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; simp only [allocated, hsp])
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨xp_args hre p₁, xp_args hre p₂⟩) ?_)
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp
      (F₁ := fun v : State => v.sp = σ₁.sp - BitVec.ofNat 32 648)
      (F₂ := fun v : State => v.sp = σ₂.sp - BitVec.ofNat 32 648)
      (RelCT.call Stream.Pad.pad_verified.1 Stream.Pad.pad_verified.2.1
        (xpRd σ₁) (xpWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_))
      fun a b ⟨_, ha', hb'⟩ => ⟨xp_call hr p₁ ha', xp_call hr p₂ hb'⟩) ?_
    · obtain ⟨x1, x2, x3⟩ := xp_pre hr p₁ ha'
      obtain ⟨y1, y2, y3⟩ := xp_pre hr p₂ hb'
      have er : xpRd σ₂ = xpRd σ₁ := by simp only [xpRd, hsp]
      have ew : xpWr σ₂ = xpWr σ₁ := by simp only [xpWr, q0, hsp]
      rw [er, ew] at y1 y2
      rw [ew] at y3
      obtain ⟨a0, a1, a2, a3, a4⟩ := xp_entry ha'
      obtain ⟨b0, b1, b2, b3, b4⟩ := xp_entry hb'
      refine ⟨x1, y1, ?_, x2, x3, y2, y3⟩
      simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_sp,
        stackArg_withRegions, State.callEntry_sp]
      exact ⟨by rw [ha'.sp, hb'.sp, hsp], by rw [a0, b0, q0], by rw [a1, b1], by rw [a2, b2, q1],
        by rw [a3, b3], by rw [a4, b4, hsp]⟩
    exact RelCT.spBlock rfl fun a b ⟨_, ha, hb⟩ => by rw [ha, hb, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying `xofFinArm`'s precondition. -/
def xpSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩]

theorem xofFinalize_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 X.rate) = true)
    (hct : ConstantTime isa (xofFinArm X).pre (xofFinArm X).pub (xofFinalize X.rate))
    (hsat : ∃ s, (xofFinArm X).pre s)
    (himp : (xofFinArm X).Implies (Spec.Sha3.xofFinalizeContract Arm.abi X 648)) :
    Verified Arm.target (xofFinalize X.rate) (Spec.Sha3.xofFinalizeContract Arm.abi X 648) :=
  (show Verified Arm.target (xofFinalize X.rate) (xofFinArm X) from
    ⟨fun _ hs => (xof_correct hX hr hre hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      hsat⟩).of_implies himp

macro "xof_arm" hX:term:max I:ident : term => `(xofFinalize_verified $hX (by decide) (by decide)
  (xof_ct (by decide) (by decide) rfl)
  ⟨xpSat, by
    simp only [xofFinArm, xpSat]
    exact ⟨trivial, rfl, Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩⟩
  (by contract_implies [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
      Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofFinArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, $I:ident]
      [xpSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using xpSat))

theorem finalize_shake128 :
    Verified Arm.target (xofFinalize Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofFinalizeContract Arm.abi Spec.Sha3.xofShake128 648) :=
  xof_arm VG.Proof.Sha3.Instances.shake128_sponge Spec.Sha3.xofShake128

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on ARMv7 for `X`: `squeeze`'s, its working
space in a frame of 656 bytes. -/
def xofSqzArm (X : Xof) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let out : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 656, 656⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧ stack.Disjoint state ∧
    stack.Disjoint out ∧ (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ 656 ≤ s.sp.toNat ∧ (s.gpr .r1).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem (State.addr (s.gpr .r0)) X.rate (s.gpr .r1).toNat X.xof msg n →
      bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        (X.xof msg (n + (s.gpr .r3).toNat)).drop n ∧
      XofRepr s'.mem (State.addr (s.gpr .r0)) X.rate (s'.gpr .r0).toNat X.xof msg
        (n + (s.gpr .r3).toNat)) ∧
    (s'.gpr .r0).toNat ≤ X.rate
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- What holds after SHAKE's `squeeze`'s block, from `s`. -/
structure XsAt (rate : Nat) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (s.sp - BitVec.ofNat 32 656), 656⟩ :: s.wr
  sp : t.sp = s.sp - BitVec.ofNat 32 656
  frame : Frame [⟨State.addr (s.sp - BitVec.ofNat 32 656), 656⟩] s.mem t.mem
  w0 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 0)) 32 = s.gpr .r3
  w4 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 4)) 32 =
    s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 16
  w8 : t.mem.readW (State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 8)) 32 = s.gpr .lr
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = BitVec.ofNat 32 rate
  r2 : t.gpr .r2 = s.gpr .r1
  r3 : t.gpr .r3 = s.gpr .r2
  pr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r

theorem xs_block {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true) {u : State}
    (hfr : ⟨State.addr u.sp, 656⟩ ∈ u.wr) (hfit : u.sp.toNat + 656 ≤ 2 ^ 32) :
    WP isa (.block (xofSqueezeArgs rate)) u fun t =>
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧ Frame [⟨State.addr u.sp, 656⟩] u.mem t.mem ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 0)) 32 = u.gpr .r3 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 4)) 32 = u.sp + BitVec.ofNat 32 16 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 8)) 32 = u.gpr .lr ∧
      t.gpr .r0 = u.gpr .r0 ∧ t.gpr .r1 = BitVec.ofNat 32 rate ∧ t.gpr .r2 = u.gpr .r1 ∧
      t.gpr .r3 = u.gpr .r2 ∧ ∀ r ∈ preserved, r ≠ .lr → t.gpr r = u.gpr r := by
  have w8 := sa_in (d := 8) hfr (by decide) hfit
  have w0 := sa_in (d := 0) hfr (by decide) hfit
  have w4 := sa_in (d := 4) hfr (by decide) hfit
  unfold xofSqueezeArgs
  refine wcons (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w8)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w0)) (wcons
    (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg,
      RegUpd.sp_setReg] using w4))
    (wcons exec_movr (wcons exec_movr (wcons (exec_li hre) (WP.block_nil ?_))))))))
  simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, reduceCtorEq, ite_true, ite_false, sa0]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, fun r hr hl => ?_⟩
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · obtain ⟨-, h1, h2, h3, h12⟩ := preserved_lo r hr
    simp only [h1, h2, h3, h12, hl, ite_false]

theorem xs_args {X : Xof} (hre : encodable (BitVec.ofNat 32 X.rate) = true) {s : State}
    (hs : (xofSqzArm X).pre s) :
    WP isa (.block (xofSqueezeArgs X.rate)) (allocated 656 s) (XsAt X.rate s) := by
  obtain ⟨-, -, -, -, -, -, -, e656, -⟩ := hs
  have hE : (s.sp - BitVec.ofNat 32 656).toNat = s.sp.toNat - 656 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  exact WP.mono (xs_block hre (u := allocated 656 s) List.mem_cons_self (by
      show (s.sp - BitVec.ofNat 32 656).toNat + 656 ≤ 2 ^ 32; omega))
    fun t ⟨trd, twr, tsp, tf, t0, t4, t8, tr0, tr1, tr2, tr3, tpr⟩ =>
      ⟨trd, twr, tsp, tf, t0, t4, t8, tr0, tr1, tr2, tr3, tpr⟩

def xsRd (s : State) : List Region := [⟨State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 0), 8⟩]
def xsWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
    ⟨State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 16), 640⟩]

theorem xs_entry {rate : Nat} {s t : State} (hI : XsAt rate s t) :
    t.callEntry.gpr .r0 = s.gpr .r0 ∧ t.callEntry.gpr .r1 = BitVec.ofNat 32 rate ∧
      t.callEntry.gpr .r2 = s.gpr .r1 ∧ t.callEntry.gpr .r3 = s.gpr .r2 ∧
      stackArg t.callEntry 0 = s.gpr .r3 ∧
      stackArg t.callEntry 1 = s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 16 := by
  refine ⟨by rw [State.callEntry_gpr _ (by decide), hI.r0], by rw [State.callEntry_gpr _ (by decide), hI.r1],
    by rw [State.callEntry_gpr _ (by decide), hI.r2], by rw [State.callEntry_gpr _ (by decide), hI.r3], ?_, ?_⟩
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
    exact hI.w0
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_one]
    exact hI.w4

theorem xs_pre {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofSqzArm X).pre s)
    (hI : XsAt X.rate s t) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions (xsRd s) (xsWr s)) ∧
      Covers (xsRd s ++ xsWr s) (t.rd ++ t.wr) ∧ Covers (xsWr s) t.wr := by
  obtain ⟨p1, p2, d1, d2, d3, f1, f2, e656, hpos⟩ := hs
  obtain ⟨g0, g1, g2, g3, a0, a1⟩ := xs_entry hI
  have hrt := rate_lt hr
  have hsp := s.sp.isLt
  have hE : (s.sp - BitVec.ofNat 32 656).toNat = s.sp.toNat - 656 := FrameStack.sub_toNat' (by omega)
  have eA : stackArgAddr t.callEntry 0 = State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 0) := by
    simp only [stackArgAddr, State.callEntry_sp, hI.sp, Nat.mul_zero]
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  have hfb := frame_eq (x := s.sp) (B := 656) (by omega)
  have hA : State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 0) =
      State.addr s.sp - BitVec.ofNat 64 656 := by rw [BitVec.add_zero, hfb]
  have hC : State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 16) =
      State.addr s.sp - BitVec.ofNat 64 656 + BitVec.ofNat 64 16 := by rw [sa_eq (by omega), hfb]
  have sA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 656, 8⟩ ⟨State.addr s.sp - BitVec.ofNat 64 656, 656⟩ :=
    Region.sub_prefix (by decide)
  have sC : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 656 + BitVec.ofNat 64 16, 640⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 656, 656⟩ := Offset.sub_base _ (by decide)
  refine ⟨?_, covers_of fun r hr => ?_, covers_of fun r hr => ?_⟩
  · simp only [Proof.Sha3.squeezeArm, xsRd, xsWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions,
      a0, a1, eA, g0, g1, g2, g3, hrate, State.callEntry_sp, hI.sp, hA, hC]
    refine ⟨trivial, trivial, d1, (d2.sub_left sC).symm, (d3.sub_left sC).symm, d2.sub_left sA,
      d3.sub_left sA, Offset.base_disjoint _ (by decide) (by omega), f1, f2, ?_, by rw [hE]; omega,
      hr, hpos⟩
    rw [BitVec.toNat_add, hE, BitVec.toNat_ofNat]; omega
  · rw [hI.rd, hI.wr, p1, p2]
    simp only [xsRd, xsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 656), 656⟩, by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero]; simp
    · exact mem_self (by simp)
    · exact mem_self (by simp)
    · refine ⟨⟨State.addr (s.sp - BitVec.ofNat 32 656), 656⟩, by simp, 16, sa_eq (by omega), by simp⟩
  · rw [hI.wr, p2]
    simp only [xsWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact mem_self (by simp)
    · exact mem_self (by simp)
    · exact ⟨⟨State.addr (s.sp - BitVec.ofNat 32 656), 656⟩, by simp, 16, sa_eq (by omega), by simp⟩

theorem xs_correct {X : Xof} (hr : X.rate ∈ rates) (hre : encodable (BitVec.ofNat 32 X.rate) = true)
    {s : State} (hs : (xofSqzArm X).pre s) :
    WP isa (xofSqueeze X.rate) s fun s' => abiPreserved s s' ∧ (xofSqzArm X).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, d2, d3, -, -, e656, -⟩ := hs'
  have hE : (s.sp - BitVec.ofNat 32 656).toNat = s.sp.toNat - 656 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  have hfb := frame_eq (x := s.sp) (B := 656) (by omega)
  unfold xofSqueeze
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega) ?_
  refine WP.seq (WP.mono (xs_args hre hs) fun t hI => ?_)
  obtain ⟨hpre, hc, hw⟩ := xs_pre hr hs hI
  refine WP.seq (FrameStack.WP.callF (k := Proof.Sha3.squeezeArm) Stream.Squeeze.squeeze_verified.1 hpre
    hc hw (by rw [squeeze_stack]; omega) fun v vrd vwr vsp vf vpr hpost => ?_)
  have hs8 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 8), 4⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 656, 656⟩ := by
    rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by decide)
  have hsub : ∀ r ∈ xsWr s ++ [FrameStack.belowA t.sp (FrameStack.armStack Impl.Sha3.Arm.Stream.squeeze)],
      Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 8), 4⟩ r := by
    intro r hr
    rw [squeeze_stack] at hr
    simp only [xsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact d2.sub_left hs8
    · exact d3.sub_left hs8
    · rw [sa_eq (by omega), sa_eq (by omega), hfb]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact disjoint_empty _ _
  have v8 : v.mem.readW (State.addr (s.sp - BitVec.ofNat 32 656 + BitVec.ofNat 32 8)) 32 = s.gpr .lr := by
    rw [vf.readW (Region.contains_self _ _) hsub (by decide), hI.w8]
  refine wcons (exec_ldrSp (by decide) (by
    rw [vsp, vrd, vwr, hI.sp, hI.wr]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, sa_con (by decide) (by omega)⟩))
    (WP.block_nil ?_)
  simp only [vsp, hI.sp, v8]
  obtain ⟨g0, g1, g2, g3, a0, -⟩ := xs_entry hI
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by have := rate_lt hr; omega)
  have hst : stateAt t.mem (State.addr (s.gpr .r0)) = stateAt s.mem (State.addr (s.gpr .r0)) :=
    stateAt_frame hI.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]; exact d2.symm
  simp only [Proof.Sha3.squeezeArm, State.withRegions_gpr, State.withRegions_mem,
    stackArg_withRegions] at hpost
  rw [g0, g1, g2, g3, a0, hrate, State.callEntry_mem, hst] at hpost
  obtain ⟨h1, h2, h3⟩ := hpost
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg n hR => ?_, ?_⟩
  · simp only [freed, RegUpd.gpr_setReg]
    by_cases hl : r = .lr
    · subst hl; simp
    · simp only [hl, ite_false]
      rw [vpr r hr hl, hI.pr r hr hl]
  · simp only [freed, RegUpd.sp_setReg]; rw [vsp, hI.sp]; exact BitVec.sub_add_cancel _ _
  · simpa only [freed, RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false] using
      xofRepr_squeeze hR h1 h3
  · simpa only [freed, RegUpd.gpr_setReg, reduceCtorEq, ite_false] using h2

theorem xs_call {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofSqzArm X).pre s)
    (hI : XsAt X.rate s t) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.Arm.Stream.squeeze) t
      fun v => v.sp = s.sp - BitVec.ofNat 32 656 := by
  obtain ⟨hpre, hc, hw⟩ := xs_pre hr hs hI
  exact FrameStack.WP.callF (k := Proof.Sha3.squeezeArm) Stream.Squeeze.squeeze_verified.1 hpre hc hw
    (by rw [squeeze_stack]; omega) fun v _ _ vsp _ _ _ => by rw [vsp, hI.sp]

theorem xs_ct {X : Xof} (hr : X.rate ∈ rates) (hre : encodable (BitVec.ofNat 32 X.rate) = true)
    (hc : spCheck false (xofSqueezeArgs X.rate) = true) :
    ConstantTime isa (xofSqzArm X).pre (xofSqzArm X).pub (xofSqueeze X.rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, q0, q1, q2, q3⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (xofSqueeze X.rate) fun _ _ => True := by
    unfold xofSqueeze
    refine RelCT.alloc (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := XsAt X.rate σ₁) (F₂ := XsAt X.rate σ₂)
      (RelCT.spBlock hc fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; simp only [allocated, hsp])
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨xs_args hre p₁, xs_args hre p₂⟩) ?_)
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp
      (F₁ := fun v : State => v.sp = σ₁.sp - BitVec.ofNat 32 656)
      (F₂ := fun v : State => v.sp = σ₂.sp - BitVec.ofNat 32 656)
      (RelCT.call Stream.Squeeze.squeeze_verified.1 Stream.Squeeze.squeeze_verified.2.1
        (xsRd σ₁) (xsWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_))
      fun a b ⟨_, ha', hb'⟩ => ⟨xs_call hr p₁ ha', xs_call hr p₂ hb'⟩) ?_
    · obtain ⟨x1, x2, x3⟩ := xs_pre hr p₁ ha'
      obtain ⟨y1, y2, y3⟩ := xs_pre hr p₂ hb'
      have er : xsRd σ₂ = xsRd σ₁ := by simp only [xsRd, hsp]
      have ew : xsWr σ₂ = xsWr σ₁ := by simp only [xsWr, q0, q2, q3, hsp]
      rw [er, ew] at y1 y2
      rw [ew] at y3
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := xs_entry ha'
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := xs_entry hb'
      refine ⟨x1, y1, ?_, x2, x3, y2, y3⟩
      simp only [Proof.Sha3.squeezeArm, State.withRegions_gpr, State.withRegions_sp,
        stackArg_withRegions, State.callEntry_sp]
      exact ⟨by rw [ha'.sp, hb'.sp, hsp], by rw [a0, b0, q0], by rw [a1, b1], by rw [a2, b2, q1],
        by rw [a3, b3, q2], by rw [a4, b4, q3], by rw [a5, b5, hsp]⟩
    exact RelCT.spBlock rfl fun a b ⟨_, ha, hb⟩ => by rw [ha, hb, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying `xofSqzArm`'s precondition (with no output). -/
def xsSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩]

theorem xofSqueeze_verified {X : Xof} (hr : X.rate ∈ rates)
    (hre : encodable (BitVec.ofNat 32 X.rate) = true)
    (hct : ConstantTime isa (xofSqzArm X).pre (xofSqzArm X).pub (xofSqueeze X.rate))
    (hsat : ∃ s, (xofSqzArm X).pre s)
    (himp : (xofSqzArm X).Implies (Spec.Sha3.xofSqueezeContract Arm.abi X 656)) :
    Verified Arm.target (xofSqueeze X.rate) (Spec.Sha3.xofSqueezeContract Arm.abi X 656) :=
  (show Verified Arm.target (xofSqueeze X.rate) (xofSqzArm X) from
    ⟨fun _ hs => (xs_correct hr hre hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      hsat⟩).of_implies himp

macro "xs_arm" I:ident : term => `(xofSqueeze_verified (by decide) (by decide)
  (xs_ct (by decide) (by decide) rfl)
  ⟨xsSat, by
    simp only [xofSqzArm, xsSat]
    exact ⟨trivial, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩⟩
  (by contract_implies [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
      Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqzArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Shared.setWidth_append32, $I:ident]
      [xsSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using xsSat))

theorem squeeze_shake128 :
    Verified Arm.target (xofSqueeze Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofSqueezeContract Arm.abi Spec.Sha3.xofShake128 656) :=
  xs_arm Spec.Sha3.xofShake128

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on ARMv7 for `H`: `pad` with SHA-3's
suffix and then `squeeze` of the digest, their working space in a frame of
664 bytes. -/
def finArm (H : Spec.Sha3.HashFn) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let out : Region := ⟨State.addr (s.gpr .r2), H.len⟩
    let stack : Region := ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧ stack.Disjoint state ∧
    stack.Disjoint out ∧ (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + H.len ≤ 2 ^ 32 ∧
    664 ≤ s.sp.toNat ∧ (s.gpr .r1).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) H.rate msg →
    (s.gpr .r1).toNat = msg.length % H.rate → bytesAt s'.mem (State.addr (s.gpr .r2)) H.len = H.digest msg
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2

/-- The frame's base, `sp - 664`. -/
abbrev fE (s : State) : BitVec 32 := s.sp - BitVec.ofNat 32 664

theorem fp_block {rate : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true) {u : State}
    (hfr : ⟨State.addr u.sp, 664⟩ ∈ u.wr) (hfit : u.sp.toNat + 664 ≤ 2 ^ 32) :
    WP isa (.block (finPadArgs rate)) u fun t =>
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧ Frame [⟨State.addr u.sp, 664⟩] u.mem t.mem ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 0)) 32 = u.sp + BitVec.ofNat 32 24 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 8)) 32 = u.gpr .lr ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 12)) 32 = u.gpr .r0 ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 16)) 32 = u.gpr .r2 ∧
      t.gpr .r0 = u.gpr .r0 ∧ t.gpr .r1 = BitVec.ofNat 32 rate ∧ t.gpr .r2 = u.gpr .r1 ∧
      t.gpr .r3 = BitVec.ofNat 32 0x06 ∧ ∀ r ∈ preserved, r ≠ .lr → t.gpr r = u.gpr r := by
  have w8 := sa_in (d := 8) hfr (by decide) hfit
  have w12 := sa_in (d := 12) hfr (by decide) hfit
  have w16 := sa_in (d := 16) hfr (by decide) hfit
  have w0 := sa_in (d := 0) hfr (by decide) hfit
  unfold finPadArgs
  refine wcons (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w8)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w12)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, ite_true, sa0, RegUpd.wr_setReg] using w16)) (wcons
    (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg,
      RegUpd.sp_setReg] using w0))
    (wcons exec_movr (wcons (exec_li hre) (wcons (exec_li (by decide)) (WP.block_nil ?_)))))))))
  simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, reduceCtorEq, ite_true, ite_false, sa0]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial,
    fun r hr hl => ?_⟩
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) hfit)
  · rw [Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · obtain ⟨-, h1, h2, h3, h12⟩ := preserved_lo r hr
    simp only [h1, h2, h3, h12, hl, ite_false]

/-- What holds after SHA-3's `finalize`'s first block, from `s`. -/
structure FpAt (rate : Nat) (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (fE s), 664⟩ :: s.wr
  sp : t.sp = fE s
  frame : Frame [⟨State.addr (fE s), 664⟩] s.mem t.mem
  w0 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 0)) 32 = fE s + BitVec.ofNat 32 24
  w8 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 8)) 32 = s.gpr .lr
  w12 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 12)) 32 = s.gpr .r0
  w16 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 16)) 32 = s.gpr .r2
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = BitVec.ofNat 32 rate
  r2 : t.gpr .r2 = s.gpr .r1
  r3 : t.gpr .r3 = BitVec.ofNat 32 0x06
  pr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r

theorem fp_args {H : Spec.Sha3.HashFn} (hre : encodable (BitVec.ofNat 32 H.rate) = true) {s : State}
    (hs : (finArm H).pre s) :
    WP isa (.block (finPadArgs H.rate)) (allocated 664 s) (FpAt H.rate s) := by
  obtain ⟨-, -, -, -, -, -, -, e664, -⟩ := hs
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  exact WP.mono (fp_block hre (u := allocated 664 s) List.mem_cons_self (by
      show (fE s).toNat + 664 ≤ 2 ^ 32; omega))
    fun t ⟨trd, twr, tsp, tf, t0, t8, t12, t16, tr0, tr1, tr2, tr3, tpr⟩ =>
      ⟨trd, twr, tsp, tf, t0, t8, t12, t16, tr0, tr1, tr2, tr3, tpr⟩

def fpRd (s : State) : List Region := [⟨State.addr (fE s + BitVec.ofNat 32 0), 4⟩]
def fpWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr (fE s + BitVec.ofNat 32 24), 640⟩]

theorem fp_entry {rate : Nat} {s t : State} (hI : FpAt rate s t) :
    t.callEntry.gpr .r0 = s.gpr .r0 ∧ t.callEntry.gpr .r1 = BitVec.ofNat 32 rate ∧
      t.callEntry.gpr .r2 = s.gpr .r1 ∧ t.callEntry.gpr .r3 = BitVec.ofNat 32 0x06 ∧
      stackArg t.callEntry 0 = fE s + BitVec.ofNat 32 24 := by
  refine ⟨by rw [State.callEntry_gpr _ (by decide), hI.r0], by rw [State.callEntry_gpr _ (by decide), hI.r1],
    by rw [State.callEntry_gpr _ (by decide), hI.r2], by rw [State.callEntry_gpr _ (by decide), hI.r3], ?_⟩
  simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hI.sp, Nat.mul_zero]
  exact hI.w0

theorem fp_pre {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {s t : State} (hs : (finArm H).pre s)
    (hI : FpAt H.rate s t) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions (fpRd s) (fpWr s)) ∧
      Covers (fpRd s ++ fpWr s) (t.rd ++ t.wr) ∧ Covers (fpWr s) t.wr := by
  obtain ⟨p1, p2, -, d2, -, f1, -, e664, hpos⟩ := hs
  obtain ⟨g0, g1, g2, -, a0⟩ := fp_entry hI
  have hrt := rate_lt hr
  have hsp := s.sp.isLt
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have eA : stackArgAddr t.callEntry 0 = State.addr (fE s + BitVec.ofNat 32 0) := by
    simp only [stackArgAddr, State.callEntry_sp, hI.sp, Nat.mul_zero]
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  have hfb := frame_eq (x := s.sp) (B := 664) (by omega)
  have hA : State.addr (fE s + BitVec.ofNat 32 0) = State.addr s.sp - BitVec.ofNat 64 664 := by
    rw [BitVec.add_zero, hfb]
  have hC : State.addr (fE s + BitVec.ofNat 32 24) =
      State.addr s.sp - BitVec.ofNat 64 664 + BitVec.ofNat 64 24 := by rw [sa_eq (by omega), hfb]
  have sA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 664, 4⟩ ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ :=
    Region.sub_prefix (by decide)
  have sC : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 664 + BitVec.ofNat 64 24, 640⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ := Offset.sub_base _ (by decide)
  refine ⟨?_, covers_of fun r hr => ?_, covers_of fun r hr => ?_⟩
  · simp only [Proof.Sha3.padArm, fpRd, fpWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions,
      a0, eA, g0, g1, g2, hrate, State.callEntry_sp, hI.sp, hA, hC]
    refine ⟨trivial, trivial, (d2.sub_left sC).symm, d2.sub_left sA,
      Offset.base_disjoint _ (by decide) (by omega), f1, ?_, by rw [hE]; omega, hr, hpos⟩
    rw [BitVec.toNat_add, hE, BitVec.toNat_ofNat]; omega
  · rw [hI.rd, hI.wr, p1, p2]
    simp only [fpRd, fpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨⟨State.addr (fE s), 664⟩, by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero]; simp
    · exact mem_self (by simp)
    · refine ⟨⟨State.addr (fE s), 664⟩, by simp, 24, sa_eq (by omega), by simp⟩
  · rw [hI.wr, p2]
    simp only [fpWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact mem_self (by simp)
    · exact ⟨⟨State.addr (fE s), 664⟩, by simp, 24, sa_eq (by omega), by simp⟩

theorem sub_empty (p : Addr) (R : Region) : Region.Sub ⟨p, 0⟩ R := fun _ h => by
  simp only [Region.Contains] at h; omega

/-- After the call of `pad`, from `s`. -/
structure AfterPad (H : Spec.Sha3.HashFn) (s v : State) : Prop where
  rd : v.rd = s.rd
  wr : v.wr = ⟨State.addr (fE s), 664⟩ :: s.wr
  sp : v.sp = fE s
  frame : Frame [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩] s.mem v.mem
  w8 : v.mem.readW (State.addr (fE s + BitVec.ofNat 32 8)) 32 = s.gpr .lr
  w12 : v.mem.readW (State.addr (fE s + BitVec.ofNat 32 12)) 32 = s.gpr .r0
  w16 : v.mem.readW (State.addr (fE s + BitVec.ofNat 32 16)) 32 = s.gpr .r2
  pr : ∀ r ∈ preserved, r ≠ .lr → v.gpr r = s.gpr r
  pad : ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) H.rate msg → (s.gpr .r1).toNat = msg.length % H.rate →
    stateAt v.mem (State.addr (s.gpr .r0)) =
      Spec.Sha3.absorb H.rate (Spec.Sha3.pad H.rate Spec.Sha3.sha3Suffix msg)

theorem fp_call {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {s t : State} (hs : (finArm H).pre s)
    (hI : FpAt H.rate s t) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.Arm.Stream.pad) t (AfterPad H s) := by
  have hs' := hs
  obtain ⟨-, -, -, d2, -, -, -, e664, -⟩ := hs'
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  have hfb := frame_eq (x := s.sp) (B := 664) (by omega)
  obtain ⟨hpre, hc, hw⟩ := fp_pre hr hs hI
  refine FrameStack.WP.callF (k := Proof.Sha3.padArm) Stream.Pad.pad_verified.1 hpre hc hw
    (by rw [pad_stack]; omega) fun v vrd vwr vsp vf vpr hpost => ?_
  rw [pad_stack] at vf
  have word : ∀ d, 8 ≤ d → d + 4 ≤ 24 → ∀ r ∈ fpWr s ++ [FrameStack.belowA t.sp 0],
      Region.Disjoint ⟨State.addr (fE s + BitVec.ofNat 32 d), 4⟩ r := by
    intro d h1 h2 r hr
    have hsd : Region.Sub ⟨State.addr (fE s + BitVec.ofNat 32 d), 4⟩
        ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ := by
      rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by omega)
    simp only [fpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d2.sub_left hsd
    · rw [sa_eq (by omega), sa_eq (by omega), hfb]
      exact Offset.disjoint _ (by omega) (by omega) (by decide)
    · exact disjoint_empty _ _
  obtain ⟨g0, g1, g2, g3, -⟩ := fp_entry hI
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by have := rate_lt hr; omega)
  have hsuf : (BitVec.ofNat 32 0x06).setWidth 8 = Spec.Sha3.sha3Suffix := by decide
  simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem] at hpost
  rw [g0, g1, g2, g3, hrate, hsuf, State.callEntry_mem] at hpost
  refine ⟨by rw [vrd, hI.rd], by rw [vwr, hI.wr], by rw [vsp, hI.sp], ?_,
    by rw [vf.readW (Region.contains_self _ _) (word 8 (by decide) (by decide)) (by decide), hI.w8],
    by rw [vf.readW (Region.contains_self _ _) (word 12 (by decide) (by decide)) (by decide), hI.w12],
    by rw [vf.readW (Region.contains_self _ _) (word 16 (by decide) (by decide)) (by decide), hI.w16],
    fun r hr hl => by rw [vpr r hr hl, hI.pr r hr hl], fun msg hm hp => ?_⟩
  · refine (hI.frame.sub fun r hr => ?_).trans (vf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩, by simp, fun _ h => h⟩
    · simp only [fpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · refine ⟨⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩, by simp, ?_⟩
        rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by decide)
      · exact ⟨_, List.mem_cons_self, sub_empty _ _⟩
  · have hst : stateAt t.mem (State.addr (s.gpr .r0)) = stateAt s.mem (State.addr (s.gpr .r0)) :=
      stateAt_frame hI.frame fun r hr => by
        rw [List.mem_singleton.mp hr, hfb]; exact d2.symm
    exact hpost msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp

theorem fs_block {rate len : Nat} (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hle : encodable (BitVec.ofNat 32 len) = true) {u : State}
    (hfr : ⟨State.addr u.sp, 664⟩ ∈ u.wr) (hfit : u.sp.toNat + 664 ≤ 2 ^ 32) :
    WP isa (.block (finSqzArgs rate len)) u fun t =>
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp ∧ Frame [⟨State.addr u.sp, 8⟩] u.mem t.mem ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 len ∧
      t.mem.readW (State.addr (u.sp + BitVec.ofNat 32 4)) 32 = u.sp + BitVec.ofNat 32 24 ∧
      t.gpr .r0 = u.mem.readW (State.addr (u.sp + BitVec.ofNat 32 12)) 32 ∧
      t.gpr .r1 = BitVec.ofNat 32 rate ∧ t.gpr .r2 = BitVec.ofNat 32 0 ∧
      t.gpr .r3 = u.mem.readW (State.addr (u.sp + BitVec.ofNat 32 16)) 32 ∧
      ∀ r ∈ preserved, r ≠ .lr → t.gpr r = u.gpr r := by
  have hfr8 : InRegions (u.rd ++ u.wr) (State.addr (u.sp + BitVec.ofNat 32 12)) 4 :=
    let ⟨r, hr, hc⟩ := sa_in (d := 12) hfr (by decide) hfit; ⟨r, List.mem_append_right _ hr, hc⟩
  have hfr16 : InRegions (u.rd ++ u.wr) (State.addr (u.sp + BitVec.ofNat 32 16)) 4 :=
    let ⟨r, hr, hc⟩ := sa_in (d := 16) hfr (by decide) hfit; ⟨r, List.mem_append_right _ hr, hc⟩
  have w0 := sa_in (d := 0) hfr (by decide) hfit
  have w4 := sa_in (d := 4) hfr (by decide) hfit
  unfold finSqzArgs
  refine wcons (exec_addSp (by decide)) (wcons (exec_ldrSp (by decide) (by
    simpa only [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.sp_setReg] using hfr8)) (wcons
    (exec_ldrSp (by decide) (by
    simpa only [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.sp_setReg] using hfr16)) (wcons
    (exec_li hre) (wcons (exec_li (by decide)) (wcons (exec_li hle) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg] using w0))
    (wcons (exec_addSp (by decide)) (wcons (exec_str (by decide) (by
    simpa only [RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, sa0, RegUpd.wr_setReg,
      RegUpd.sp_setReg] using w4)) (WP.block_nil ?_)))))))))
  simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, reduceCtorEq, ite_true, ite_false, sa0]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, trivial, trivial, trivial, trivial, fun r hr hl => ?_⟩
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sa_con (by decide) (by omega))).writeW
      (List.mem_singleton_self _) _ (sa_con (by decide) (by omega))
  · rw [Mem.readW_writeW_sep (sa_sep (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]
  · obtain ⟨-, h1, h2, h3, h12⟩ := preserved_lo r hr
    have h0 : r ≠ .r0 := (preserved_lo r hr).1
    simp only [h0, h1, h2, h3, h12, hl, ite_false]

/-- What holds after SHA-3's `finalize`'s second block, from `v` after the
call of `pad` from `s`. -/
structure FsAt (H : Spec.Sha3.HashFn) (s v t : State) : Prop where
  rd : t.rd = v.rd
  wr : t.wr = v.wr
  sp : t.sp = fE s
  frame : Frame [⟨State.addr (fE s), 8⟩] v.mem t.mem
  w0 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 H.len
  w4 : t.mem.readW (State.addr (fE s + BitVec.ofNat 32 4)) 32 = fE s + BitVec.ofNat 32 24
  r0 : t.gpr .r0 = s.gpr .r0
  r1 : t.gpr .r1 = BitVec.ofNat 32 H.rate
  r2 : t.gpr .r2 = BitVec.ofNat 32 0
  r3 : t.gpr .r3 = s.gpr .r2
  pr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = v.gpr r

theorem fs_args {H : Spec.Sha3.HashFn} (hre : encodable (BitVec.ofNat 32 H.rate) = true)
    (hle : encodable (BitVec.ofNat 32 H.len) = true) {s v : State} (hs : (finArm H).pre s)
    (hA : AfterPad H s v) :
    WP isa (.block (finSqzArgs H.rate H.len)) v (FsAt H s v) := by
  obtain ⟨-, -, -, -, -, -, -, e664, -⟩ := hs
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  refine WP.mono (fs_block hre hle (u := v) (by rw [hA.wr, hA.sp]; exact List.mem_cons_self)
    (by rw [hA.sp]; omega)) fun t ⟨trd, twr, tsp, tf, t0, t4, tr0, tr1, tr2, tr3, tpr⟩ => ?_
  rw [hA.sp] at tsp tf t0 t4 tr0 tr3
  exact ⟨trd, twr, tsp, tf, t0, t4, by rw [tr0, hA.w12], tr1, tr2, by rw [tr3, hA.w16], tpr⟩

def fsRd (s : State) : List Region := [⟨State.addr (fE s + BitVec.ofNat 32 0), 8⟩]
def fsWr (H : Spec.Sha3.HashFn) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 200⟩, ⟨State.addr (s.gpr .r2), H.len⟩,
    ⟨State.addr (fE s + BitVec.ofNat 32 24), 640⟩]

theorem fs_entry {H : Spec.Sha3.HashFn} {s v t : State} (hF : FsAt H s v t) :
    t.callEntry.gpr .r0 = s.gpr .r0 ∧ t.callEntry.gpr .r1 = BitVec.ofNat 32 H.rate ∧
      t.callEntry.gpr .r2 = BitVec.ofNat 32 0 ∧ t.callEntry.gpr .r3 = s.gpr .r2 ∧
      stackArg t.callEntry 0 = BitVec.ofNat 32 H.len ∧
      stackArg t.callEntry 1 = fE s + BitVec.ofNat 32 24 := by
  refine ⟨by rw [State.callEntry_gpr _ (by decide), hF.r0], by rw [State.callEntry_gpr _ (by decide), hF.r1],
    by rw [State.callEntry_gpr _ (by decide), hF.r2], by rw [State.callEntry_gpr _ (by decide), hF.r3], ?_, ?_⟩
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hF.sp, Nat.mul_zero]
    exact hF.w0
  · simp only [stackArg, stackArgAddr, State.callEntry_mem, State.callEntry_sp, hF.sp, Nat.mul_one]
    exact hF.w4

theorem fs_pre {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15) {s v t : State}
    (hs : (finArm H).pre s) (hA : AfterPad H s v) (hF : FsAt H s v t) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions (fsRd s) (fsWr H s)) ∧
      Covers (fsRd s ++ fsWr H s) (t.rd ++ t.wr) ∧ Covers (fsWr H s) t.wr := by
  obtain ⟨p1, p2, d1, d2, d3, f1, f2, e664, -⟩ := hs
  obtain ⟨g0, g1, g2, g3, a0, a1⟩ := fs_entry hF
  have hrt := rate_lt hr
  have hsp := s.sp.isLt
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have eA : stackArgAddr t.callEntry 0 = State.addr (fE s + BitVec.ofNat 32 0) := by
    simp only [stackArgAddr, State.callEntry_sp, hF.sp, Nat.mul_zero]
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  have hlen : (BitVec.ofNat 32 H.len).toNat = H.len := toNat_ofNat32 (by omega)
  have hfb := frame_eq (x := s.sp) (B := 664) (by omega)
  have hA0 : State.addr (fE s + BitVec.ofNat 32 0) = State.addr s.sp - BitVec.ofNat 64 664 := by
    rw [BitVec.add_zero, hfb]
  have hC : State.addr (fE s + BitVec.ofNat 32 24) =
      State.addr s.sp - BitVec.ofNat 64 664 + BitVec.ofNat 64 24 := by rw [sa_eq (by omega), hfb]
  have sA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 664, 8⟩ ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ :=
    Region.sub_prefix (by decide)
  have sC : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 664 + BitVec.ofNat 64 24, 640⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ := Offset.sub_base _ (by decide)
  refine ⟨?_, covers_of fun r hr => ?_, covers_of fun r hr => ?_⟩
  · simp only [Proof.Sha3.squeezeArm, fsRd, fsWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions,
      a0, a1, eA, g0, g1, g2, g3, hrate, hlen, State.callEntry_sp, hF.sp, hA0, hC]
    refine ⟨trivial, trivial, d1, (d2.sub_left sC).symm, (d3.sub_left sC).symm, d2.sub_left sA,
      d3.sub_left sA, Offset.base_disjoint _ (by decide) (by omega), f1, f2, ?_, by rw [hE]; omega,
      hr, by simp⟩
    rw [BitVec.toNat_add, hE, BitVec.toNat_ofNat]; omega
  · rw [hF.rd, hF.wr, hA.rd, hA.wr, p1, p2]
    simp only [fsRd, fsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨⟨State.addr (fE s), 664⟩, by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero]; simp
    · exact mem_self (by simp)
    · exact mem_self (by simp)
    · refine ⟨⟨State.addr (fE s), 664⟩, by simp, 24, sa_eq (by omega), by simp⟩
  · rw [hF.wr, hA.wr, p2]
    simp only [fsWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact mem_self (by simp)
    · exact mem_self (by simp)
    · exact ⟨⟨State.addr (fE s), 664⟩, by simp, 24, sa_eq (by omega), by simp⟩

theorem fin_correct {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15) (hre : encodable (BitVec.ofNat 32 H.rate) = true)
    (hle : encodable (BitVec.ofNat 32 H.len) = true) {s : State} (hs : (finArm H).pre s) :
    WP isa (finalize H.rate H.len) s fun s' => abiPreserved s s' ∧ (finArm H).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, d2, d3, -, -, e664, -⟩ := hs'
  have hE : (fE s).toNat = s.sp.toNat - 664 := FrameStack.sub_toNat' (by omega)
  have hsp := s.sp.isLt
  have hfb := frame_eq (x := s.sp) (B := 664) (by omega)
  unfold finalize
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega) ?_
  refine WP.seq (WP.mono (fp_args hre hs) fun t hI => ?_)
  refine WP.seq (WP.mono (fp_call hr hs hI) fun v hA => ?_)
  refine WP.seq (WP.mono (fs_args hre hle hs hA) fun t₂ hF => ?_)
  obtain ⟨hpre, hc, hw⟩ := fs_pre hr hl hs hA hF
  refine WP.seq (FrameStack.WP.callF (k := Proof.Sha3.squeezeArm) Stream.Squeeze.squeeze_verified.1 hpre
    hc hw (by rw [squeeze_stack]; omega) fun w wrd wwr wsp wf wpr hpost => ?_)
  rw [squeeze_stack] at wf
  have hs8 : Region.Sub ⟨State.addr (fE s + BitVec.ofNat 32 8), 4⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩ := by
    rw [sa_eq (by omega), hfb]; exact Offset.sub_base _ (by decide)
  have hsub : ∀ r ∈ fsWr H s ++ [FrameStack.belowA t₂.sp 0],
      Region.Disjoint ⟨State.addr (fE s + BitVec.ofNat 32 8), 4⟩ r := by
    intro r hr
    simp only [fsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact d2.sub_left hs8
    · exact d3.sub_left hs8
    · rw [sa_eq (by omega), sa_eq (by omega), hfb]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact disjoint_empty _ _
  have t8 : t₂.mem.readW (State.addr (fE s + BitVec.ofNat 32 8)) 32 = s.gpr .lr := by
    rw [hF.frame.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, sa_eq (by omega)]
      exact Offset.disjoint_base _ (by decide) (by omega)) (by decide), hA.w8]
  have w8 : w.mem.readW (State.addr (fE s + BitVec.ofNat 32 8)) 32 = s.gpr .lr := by
    rw [wf.readW (Region.contains_self _ _) hsub (by decide), t8]
  refine wcons (exec_ldrSp (by decide) (by
    rw [wsp, wrd, wwr, hF.sp, hF.wr, hA.wr]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, sa_con (by decide) (by omega)⟩))
    (WP.block_nil ?_)
  simp only [wsp, hF.sp, w8]
  obtain ⟨g0, g1, g2, g3, a0, -⟩ := fs_entry hF
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by have := rate_lt hr; omega)
  have hlen : (BitVec.ofNat 32 H.len).toNat = H.len := toNat_ofNat32 (by omega)
  have hst : stateAt t₂.mem (State.addr (s.gpr .r0)) = stateAt v.mem (State.addr (s.gpr .r0)) :=
    stateAt_frame hF.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (d2.sub_left (by rw [hfb]; exact Region.sub_prefix (by decide))).symm
  simp only [Proof.Sha3.squeezeArm, State.withRegions_gpr, State.withRegions_mem,
    stackArg_withRegions] at hpost
  rw [g0, g1, g2, g3, a0, hrate, hlen, State.callEntry_mem, hst] at hpost
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_⟩
  · simp only [freed, RegUpd.gpr_setReg]
    by_cases hl : r = .lr
    · subst hl; simp
    · simp only [hl, ite_false]
      rw [wpr r hr hl, hF.pr r hr hl, hA.pr r hr hl]
  · simp only [freed, RegUpd.sp_setReg]; rw [wsp, hF.sp]; exact BitVec.sub_add_cancel _ _
  · simp only [freed, RegUpd.mem_setReg]
    rw [hpost.1, hA.pad msg hm hp]
    exact digest_of_pad hH rfl

theorem fs_call {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15) {s v t : State}
    (hs : (finArm H).pre s) (hA : AfterPad H s v) (hF : FsAt H s v t) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.Arm.Stream.squeeze) t
      fun w => w.sp = fE s := by
  obtain ⟨hpre, hc, hw⟩ := fs_pre hr hl hs hA hF
  exact FrameStack.WP.callF (k := Proof.Sha3.squeezeArm) Stream.Squeeze.squeeze_verified.1 hpre hc hw
    (by rw [squeeze_stack]; omega) fun w _ _ wsp _ _ _ => by rw [wsp, hF.sp]

theorem fin_ct {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15)
    (hre : encodable (BitVec.ofNat 32 H.rate) = true) (hle : encodable (BitVec.ofNat 32 H.len) = true)
    (hc₁ : spCheck false (finPadArgs H.rate) = true) (hc₂ : spCheck false (finSqzArgs H.rate H.len) = true) :
    ConstantTime isa (finArm H).pre (finArm H).pub (finalize H.rate H.len) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, q0, q1, q2⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finalize H.rate H.len) fun _ _ => True := by
    unfold finalize
    refine RelCT.alloc (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := FpAt H.rate σ₁) (F₂ := FpAt H.rate σ₂)
      (RelCT.spBlock hc₁ fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; simp only [allocated, hsp])
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨fp_args hre p₁, fp_args hre p₂⟩) ?_)
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp (F₁ := AfterPad H σ₁) (F₂ := AfterPad H σ₂)
      (RelCT.call Stream.Pad.pad_verified.1 Stream.Pad.pad_verified.2.1
        (fpRd σ₁) (fpWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_))
      fun a b ⟨_, ha', hb'⟩ => ⟨fp_call hr p₁ ha', fp_call hr p₂ hb'⟩) ?_
    · obtain ⟨x1, x2, x3⟩ := fp_pre hr p₁ ha'
      obtain ⟨y1, y2, y3⟩ := fp_pre hr p₂ hb'
      have er : fpRd σ₂ = fpRd σ₁ := by simp only [fpRd, fE, hsp]
      have ew : fpWr σ₂ = fpWr σ₁ := by simp only [fpWr, fE, q0, hsp]
      rw [er, ew] at y1 y2
      rw [ew] at y3
      obtain ⟨a0, a1, a2, a3, a4⟩ := fp_entry ha'
      obtain ⟨b0, b1, b2, b3, b4⟩ := fp_entry hb'
      refine ⟨x1, y1, ?_, x2, x3, y2, y3⟩
      simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_sp,
        stackArg_withRegions, State.callEntry_sp]
      exact ⟨by rw [ha'.sp, hb'.sp, fE, fE, hsp], by rw [a0, b0, q0], by rw [a1, b1],
        by rw [a2, b2, q1], by rw [a3, b3], by rw [a4, b4, fE, fE, hsp]⟩
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp
      (F₁ := fun t => ∃ v, AfterPad H σ₁ v ∧ FsAt H σ₁ v t)
      (F₂ := fun t => ∃ v, AfterPad H σ₂ v ∧ FsAt H σ₂ v t)
      (RelCT.spBlock hc₂ fun a b ⟨_, ha', hb'⟩ => by rw [ha'.sp, hb'.sp, fE, fE, hsp])
      fun a b ⟨_, ha', hb'⟩ => ⟨WP.mono (fs_args hre hle p₁ ha') fun t h => ⟨a, ha', h⟩,
        WP.mono (fs_args hre hle p₂ hb') fun t h => ⟨b, hb', h⟩⟩) ?_
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp
      (F₁ := fun w : State => w.sp = fE σ₁) (F₂ := fun w : State => w.sp = fE σ₂)
      (RelCT.call Stream.Squeeze.squeeze_verified.1 Stream.Squeeze.squeeze_verified.2.1
        (fsRd σ₁) (fsWr H σ₁) (fun a b ⟨_, ⟨u₁, hA₁, ha'⟩, ⟨u₂, hA₂, hb'⟩⟩ => ?_))
      fun a b ⟨_, ⟨u₁, hA₁, ha'⟩, ⟨u₂, hA₂, hb'⟩⟩ =>
        ⟨fs_call hr hl p₁ hA₁ ha', fs_call hr hl p₂ hA₂ hb'⟩) ?_
    · obtain ⟨x1, x2, x3⟩ := fs_pre hr hl p₁ hA₁ ha'
      obtain ⟨y1, y2, y3⟩ := fs_pre hr hl p₂ hA₂ hb'
      have er : fsRd σ₂ = fsRd σ₁ := by simp only [fsRd, fE, hsp]
      have ew : fsWr H σ₂ = fsWr H σ₁ := by simp only [fsWr, fE, q0, q2, hsp]
      rw [er, ew] at y1 y2
      rw [ew] at y3
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := fs_entry ha'
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := fs_entry hb'
      refine ⟨x1, y1, ?_, x2, x3, y2, y3⟩
      simp only [Proof.Sha3.squeezeArm, State.withRegions_gpr, State.withRegions_sp,
        stackArg_withRegions, State.callEntry_sp]
      exact ⟨by rw [ha'.sp, hb'.sp, fE, fE, hsp], by rw [a0, b0, q0], by rw [a1, b1], by rw [a2, b2],
        by rw [a3, b3, q2], by rw [a4, b4], by rw [a5, b5, fE, fE, hsp]⟩
    exact RelCT.spBlock rfl fun a b ⟨_, ha, hb⟩ => by rw [ha, hb, fE, fE, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying `finArm`'s precondition. -/
def finSat (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩]

theorem fin_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15) (hre : encodable (BitVec.ofNat 32 H.rate) = true)
    (hle : encodable (BitVec.ofNat 32 H.len) = true)
    (hct : ConstantTime isa (finArm H).pre (finArm H).pub (finalize H.rate H.len))
    (hsat : ∃ s, (finArm H).pre s)
    (himp : (finArm H).Implies (Spec.Sha3.finalizeContract Arm.abi H 664)) :
    Verified Arm.target (finalize H.rate H.len) (Spec.Sha3.finalizeContract Arm.abi H 664) :=
  (show Verified Arm.target (finalize H.rate H.len) (finArm H) from
    ⟨fun _ hs => (fin_correct hH hr hl hre hle hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩,
      hct, hsat⟩).of_implies himp

macro "fin_arm" hH:term:max I:ident len:term:max : term => `(fin_verified $hH (by decide) (by decide)
  (by decide) (by decide)
  (fin_ct (by decide) (by decide) (by decide) (by decide) rfl rfl)
  ⟨finSat $len, by
    simp only [finArm, finSat]
    exact ⟨trivial, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩⟩
  (by contract_implies [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, finArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, $I:ident]
      [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finSat $len))

theorem finalize_sha3_224 :
    Verified Arm.target (finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract Arm.abi Spec.Sha3.hashSha3_224 664) :=
  fin_arm VG.Proof.Sha3.Instances.sha3_224_sponge Spec.Sha3.hashSha3_224 28

theorem update_sha3_256 :
    Verified Arm.target (update Spec.Sha3.hashSha3_256.rate)
      (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_256.rate 16) :=
  upd_arm Spec.Sha3.hashSha3_256

theorem update_sha3_384 :
    Verified Arm.target (update Spec.Sha3.hashSha3_384.rate)
      (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_384.rate 16) :=
  upd_arm Spec.Sha3.hashSha3_384

theorem update_sha3_512 :
    Verified Arm.target (update Spec.Sha3.hashSha3_512.rate)
      (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_512.rate 16) :=
  upd_arm Spec.Sha3.hashSha3_512

theorem update_shake128 :
    Verified Arm.target (update Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.updateContract Arm.abi Spec.Sha3.xofShake128.rate 16) :=
  upd_arm Spec.Sha3.xofShake128

theorem finalize_sha3_256 :
    Verified Arm.target (finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract Arm.abi Spec.Sha3.hashSha3_256 664) :=
  fin_arm VG.Proof.Sha3.Instances.sha3_256_sponge Spec.Sha3.hashSha3_256 32

theorem finalize_sha3_384 :
    Verified Arm.target (finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract Arm.abi Spec.Sha3.hashSha3_384 664) :=
  fin_arm VG.Proof.Sha3.Instances.sha3_384_sponge Spec.Sha3.hashSha3_384 48

theorem finalize_sha3_512 :
    Verified Arm.target (finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract Arm.abi Spec.Sha3.hashSha3_512 664) :=
  fin_arm VG.Proof.Sha3.Instances.sha3_512_sponge Spec.Sha3.hashSha3_512 64

theorem finalize_shake256 :
    Verified Arm.target (xofFinalize Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofFinalizeContract Arm.abi Spec.Sha3.xofShake256 648) :=
  xof_arm VG.Proof.Sha3.Instances.shake256_sponge Spec.Sha3.xofShake256

theorem squeeze_shake256 :
    Verified Arm.target (xofSqueeze Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofSqueezeContract Arm.abi Spec.Sha3.xofShake256 656) :=
  xs_arm Spec.Sha3.xofShake256

end VG.Proof.Sha3.Arm.Instances

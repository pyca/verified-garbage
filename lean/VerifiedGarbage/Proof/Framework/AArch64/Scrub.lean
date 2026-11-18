module

public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# The run of the stack's clearing (AArch64)

`tail_run`: `scrubTail W` (`Impl/Residue/AArch64/Scrub.lean`) runs from any
state whose stack pointer has `W` bytes below it, with a trace of the stack
pointer alone. It writes `x9` (the frame's base) and `v31` (zero), and leaves
the `W` bytes below the stack pointer zeroed and then released (`lose`), the
rest of memory, the regions, the stack pointer and the flags as they were.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.AArch64 VG.Impl.Residue.AArch64

/-- `m`, with the `n` bytes from `b` zero. -/
def zeroTo (b : Addr) (n : Nat) (m : Mem) : Mem := fun x => if (x - b).toNat < n then 0 else m x

/-- The trace of `scrubStores k` from `x9 = b`. -/
def storesTrace (b : Addr) (k : Nat) : List Leak :=
  (List.range k).map fun j => .addr (b + BitVec.ofNat 64 (16 * j))

theorem zeroTo_succ {b : Addr} {k W : Nat} (hk : 16 * k + 16 ≤ W) (hW : W < 4096) (m : Mem) :
    (zeroTo b (16 * k) m).write (b + BitVec.ofNat 64 (16 * k)) 16 (0 : BitVec 128) =
      zeroTo b (16 * (k + 1)) m := by
  funext x
  have hx : (x - (b + BitVec.ofNat 64 (16 * k))).toNat =
      ((x - b).toNat + (2 ^ 64 - 16 * k)) % 2 ^ 64 := by
    have hlt : 16 * k < 2 ^ 64 := by omega
    rw [show x - (b + BitVec.ofNat 64 (16 * k)) = (x - b) - BitVec.ofNat 64 (16 * k) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  have ht := (x - b).isLt
  simp only [Mem.write, zeroTo, hx]
  by_cases h₁ : ((x - b).toNat + (2 ^ 64 - 16 * k)) % 2 ^ 64 < 16
  · have : (x - b).toNat < 16 * (k + 1) := by omega
    simp only [h₁, this, ↓reduceIte]
    simp
  · simp only [h₁, ↓reduceIte]
    by_cases h₂ : (x - b).toNat < 16 * k
    · simp only [h₂, ↓reduceIte, show (x - b).toNat < 16 * (k + 1) by omega]
    · simp only [h₂, ↓reduceIte, show ¬ (x - b).toNat < 16 * (k + 1) by omega]

theorem stores_run {W : Nat} (hW : W < 4096) (u : State) (b : Addr) (hb : u.gpr .x9 = b)
    (hv : u.v .v31 = 0) (hR : (⟨b, W⟩ : Region) ∈ u.wr) :
    ∀ k, 16 * k ≤ W →
      execBlock isa (scrubStores k) u = some ({ u with mem := zeroTo b (16 * k) u.mem }, storesTrace b k)
  | 0, _ => by
    simp only [scrubStores, List.range_zero, List.map_nil, execBlock, storesTrace]
    congr 2
  | k + 1, hk => by
    rw [show scrubStores (k + 1) = scrubStores k ++ [.strq .v31 .x9 (16 * k)] by
      simp [scrubStores, List.range_succ]]
    rw [execBlock_append, stores_run hW u b hb hv hR k (by omega), Option.bind_some]
    have hoff : 16 * k % 16 = 0 ∧ 16 * k < 4096 * 16 := ⟨by omega, by omega⟩
    have hin : InRegions u.wr (b + BitVec.ofNat 64 (16 * k)) 16 := by
      refine ⟨_, hR, ?_⟩
      unfold Region.Contains
      simp only [BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hex : exec (.strq .v31 .x9 (16 * k)) { u with mem := zeroTo b (16 * k) u.mem } =
        some { u with mem := zeroTo b (16 * (k + 1)) u.mem } := by
      simp only [exec, addr, hoff, and_self, ↓reduceIte, Option.bind_some, State.store, hb, hin, hv,
        Option.some.injEq]
      rw [zeroTo_succ (by omega : 16 * k + 16 ≤ W) hW]
    simp only [execBlock, isa]
    rw [hex]
    simp [addrs, storesTrace, List.range_succ, hb]

/-- The trace of `scrubTail W` from the stack pointer `sp`. -/
def tailTrace (sp : Addr) (W : Nat) : List Leak := storesTrace (sp - BitVec.ofNat 64 W) (W / 16)

/-- What `scrubTail W` leaves (see `tail_run`). -/
structure TailRun (W : Nat) (u u' : State) : Prop where
  gpr : u'.gpr = fun q => if q = .x9 then u.sp - BitVec.ofNat 64 W else u.gpr q
  v : u'.v = fun w => if w = .v31 then 0 else u.v w
  sp : u'.sp = u.sp
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  c : u'.c = u.c
  nf : u'.nf = u.nf
  zf : u'.zf = u.zf
  vf : u'.vf = u.vf
  dit : u'.dit = u.dit
  unknowns : u'.unknowns = fun n => u.unknowns (n + W / 4)
  mem : u'.mem = lose (zeroTo (u.sp - BitVec.ofNat 64 W) W u.mem) (u.sp - BitVec.ofNat 64 W) W u.unknowns

theorem tail_run {W : Nat} (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (u : State) (hsp : W ≤ u.sp.toNat) :
    ∃ u', Exec isa (scrubTail W) u (tailTrace u.sp W) u' ∧ TailRun W u u' := by
  let b := u.sp - BitVec.ofNat 64 W
  let u₁ : State := { u with sp := b, wr := ⟨b, W⟩ :: u.wr }
  have hpush : isa.push (.alloc W) u = some u₁ := by
    simp only [isa, push, hW.1, hW.2.1, hW.2.2, hsp, and_self, ↓reduceIte]; rfl
  let u₂ : State := (u₁.setV .v31 0).write .x .x9 u₁.sp
  have h₂ : execBlock isa [.vop (.movi0 .v31), .addSp .x9 0] u₁ = some (u₂, []) := by
    simp [execBlock, isa, exec, VOp.eval, addrs, u₂, State.setV]
  have hb₂ : u₂.gpr .x9 = b := by simp [u₂, u₁, b, State.write]
  have hv₂ : u₂.v .v31 = 0 := by simp [u₂, State.write, State.setV]
  have hR : (⟨b, W⟩ : Region) ∈ u₂.wr := by simp [u₂, u₁, State.write, State.setV]
  have hs := stores_run hW.2.1 u₂ b hb₂ hv₂ hR (W / 16) (by omega)
  have hblk : execBlock isa (scrubBlock W) u₁ =
      some ({ u₂ with mem := zeroTo b (16 * (W / 16)) u₂.mem }, storesTrace b (W / 16)) := by
    rw [show scrubBlock W = [.vop (.movi0 .v31), .addSp .x9 0] ++ scrubStores (W / 16) from rfl,
      execBlock_append, h₂, Option.bind_some, hs]
    rfl
  let u₃ : State := { u₂ with mem := zeroTo b (16 * (W / 16)) u₂.mem }
  have hpop : isa.pop (.free W) u₁ u₃ = some { u₃ with
      sp := u₃.sp + BitVec.ofNat 64 W, wr := u₃.wr.tail,
      mem := lose u₃.mem u₃.sp W u₃.unknowns, unknowns := fun n => u₃.unknowns (n + W / 4) } := by
    have hc : 0 < W ∧ W < 4096 ∧ W % 16 = 0 ∧ u₃.sp = u₁.sp ∧ u₃.wr = u₁.wr ∧
        u₁.wr.head? = some ⟨u₁.sp, W⟩ := ⟨hW.1, hW.2.1, hW.2.2, rfl, rfl, rfl⟩
    simp only [isa, pop, hc, and_self, ↓reduceIte]
  let u₄ : State := { u₃ with
    sp := u₃.sp + BitVec.ofNat 64 W
    wr := u₃.wr.tail
    mem := lose u₃.mem u₃.sp W u₃.unknowns
    unknowns := (fun n => u₃.unknowns (n + W / 4)) }
  refine ⟨u₄, ?_, ?_⟩
  · have := Exec.frame (M := isa) hpush (Exec.block hblk) hpop
    simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at this
    exact this
  · have h16 : 16 * (W / 16) = W := by omega
    constructor
    · funext q
      by_cases hq : q = .x9
      · subst hq; simp [u₄, u₃, u₂, u₁, b, State.write]
      · simp [u₄, u₃, u₂, u₁, State.write, State.setV, hq]
    · funext w
      by_cases hw : w = .v31
      · subst hw; simp [u₄, u₃, u₂, u₁, State.write, State.setV]
      · simp [u₄, u₃, u₂, u₁, State.write, State.setV, hw]
    · simp only [u₄, u₃, u₂, u₁, b, State.write, State.setV]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := u.sp.isLt
      omega
    all_goals simp [u₄, u₃, u₂, u₁, b, State.write, State.setV, h16]

end VG.AArch64.Scrub

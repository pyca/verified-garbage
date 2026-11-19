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

/-! ## Chosen granules -/

/-- Whether `x` is in one of the 16-byte granules `ks` from `b`. -/
def inG (b : Addr) (ks : List Nat) (x : Addr) : Bool :=
  ks.any fun k => decide (16 * k ≤ (x - b).toNat ∧ (x - b).toNat < 16 * k + 16)

/-- `m`, with the granules `ks` from `b` zero. -/
def zeroG (b : Addr) (ks : List Nat) (m : Mem) : Mem := fun x => if inG b ks x then 0 else m x

theorem zeroG_cons {b : Addr} {k : Nat} {ks : List Nat} {W : Nat} (hk : 16 * k + 16 ≤ W) (hW : W < 2 ^ 16)
    (m : Mem) :
    zeroG b ks (m.write (b + BitVec.ofNat 64 (16 * k)) 16 (0 : BitVec 128)) = zeroG b (k :: ks) m := by
  funext x
  have hlt : 16 * k < 2 ^ 64 := by omega
  have hx : (x - (b + BitVec.ofNat 64 (16 * k))).toNat =
      ((x - b).toNat + (2 ^ 64 - 16 * k)) % 2 ^ 64 := by
    rw [show x - (b + BitVec.ofNat 64 (16 * k)) = (x - b) - BitVec.ofNat 64 (16 * k) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  have ht := (x - b).isLt
  simp only [zeroG, inG, List.any_cons, Mem.write, hx]
  by_cases h₁ : 16 * k ≤ (x - b).toNat ∧ (x - b).toNat < 16 * k + 16
  · have : ((x - b).toNat + (2 ^ 64 - 16 * k)) % 2 ^ 64 < 16 := by omega
    simp only [h₁, ↓reduceIte, this]
    split <;> simp
  · have : ¬ ((x - b).toNat + (2 ^ 64 - 16 * k)) % 2 ^ 64 < 16 := by omega
    simp only [h₁, decide_false, Bool.false_or, this, ↓reduceIte]

/-- The trace of `scrubStoresL ks` from `x9 = b`. -/
def storesTraceL (b : Addr) (ks : List Nat) : List Leak :=
  ks.map fun k => .addr (b + BitVec.ofNat 64 (16 * k))

/-- Each of the granules `ks` from `b` is in a writable region. -/
def GranulesIn (wr : List Region) (b : Addr) (ks : List Nat) : Prop :=
  ∀ k ∈ ks, InRegions wr (b + BitVec.ofNat 64 (16 * k)) 16

/-- The granules `ks` of the `W` bytes from `b` are in the region of them. -/
theorem granulesIn_of {wr : List Region} {b : Addr} {W : Nat} (hW : W < 2 ^ 16) (hR : (⟨b, W⟩ : Region) ∈ wr)
    {ks : List Nat} (hks : ∀ k ∈ ks, 16 * k + 16 ≤ W) : GranulesIn wr b ks := fun k hk' => by
  have hk := hks k hk'
  refine ⟨_, hR, ?_⟩
  unfold Region.Contains
  simp only [BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem storesL_run {W : Nat} (hW : W < 2 ^ 16) (b : Addr) :
    ∀ (ks : List Nat) (u : State), u.gpr .x9 = b → u.v .v31 = 0 → GranulesIn u.wr b ks →
      (∀ k ∈ ks, 16 * k + 16 ≤ W) →
      execBlock isa (scrubStoresL ks) u = some ({ u with mem := zeroG b ks u.mem }, storesTraceL b ks)
  | [], u, _, _, _, _ => by
    simp only [scrubStoresL, List.map_nil, execBlock, storesTraceL]
    congr 2
  | k :: ks, u, hb, hv, hR, hks => by
    have hk := hks k (List.mem_cons_self ..)
    have hoff : 16 * k % 16 = 0 ∧ 16 * k < 4096 * 16 := ⟨by omega, by omega⟩
    have hin : InRegions u.wr (b + BitVec.ofNat 64 (16 * k)) 16 := hR k (List.mem_cons_self ..)
    have hex : exec (.strq .v31 .x9 (16 * k)) u =
        some { u with mem := u.mem.write (b + BitVec.ofNat 64 (16 * k)) 16 0 } := by
      simp only [exec, addr, hoff, and_self, ↓reduceIte, Option.bind_some, State.store, hb, hin, hv]
    have ih := storesL_run hW b ks { u with mem := u.mem.write (b + BitVec.ofNat 64 (16 * k)) 16 0 }
      hb hv (fun k' h => hR k' (List.mem_cons_of_mem _ h)) (fun k' h => hks k' (List.mem_cons_of_mem _ h))
    have h1 : execBlock isa [.strq .v31 .x9 (16 * k)] u =
        some ({ u with mem := u.mem.write (b + BitVec.ofNat 64 (16 * k)) 16 0 },
          [.addr (b + BitVec.ofNat 64 (16 * k))]) := by
      simp only [execBlock, isa]
      rw [hex]
      simp [addrs, hb]
    rw [show scrubStoresL (k :: ks) = [.strq .v31 .x9 (16 * k)] ++ scrubStoresL ks from rfl,
      execBlock_append, h1, Option.bind_some, ih]
    rw [zeroG_cons hk hW]
    simp [storesTraceL]

/-- The trace of `scrubTailG W ks` from the stack pointer `sp`. -/
def tailTraceG (sp : Addr) (W : Nat) (ks : List Nat) : List Leak :=
  storesTraceL (sp - BitVec.ofNat 64 W) ks

/-- What `scrubTailG W ks` leaves (see `tailG_run`). -/
structure TailRunG (W : Nat) (ks : List Nat) (u u' : State) : Prop where
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
  mem : u'.mem = lose (zeroG (u.sp - BitVec.ofNat 64 W) ks u.mem) (u.sp - BitVec.ofNat 64 W) W u.unknowns

theorem tailG_run {W : Nat} (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) {ks : List Nat}
    (hks : ∀ k ∈ ks, 16 * k + 16 ≤ W) (u : State) (hsp : W ≤ u.sp.toNat) :
    ∃ u', Exec isa (scrubTailG W ks) u (tailTraceG u.sp W ks) u' ∧ TailRunG W ks u u' := by
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
  have hs := storesL_run (by omega) b ks u₂ hb₂ hv₂ (granulesIn_of (by omega) hR hks) hks
  have hblk : execBlock isa (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL ks) u₁ =
      some ({ u₂ with mem := zeroG b ks u₂.mem }, storesTraceL b ks) := by
    rw [show (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL ks : List Instr) =
        [.vop (.movi0 .v31), .addSp .x9 0] ++ scrubStoresL ks from rfl,
      execBlock_append, h₂, Option.bind_some, hs]
    rfl
  let u₃ : State := { u₂ with mem := zeroG b ks u₂.mem }
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
  · constructor
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
    all_goals simp [u₄, u₃, u₂, u₁, b, State.write, State.setV]

/-! ## Two frames

An `alloc` takes less than 4096 bytes. `scrubTailL W` zeroes `W` bytes in
two frames, of `W - 4080` bytes and below it 4080; once both are released,
the memory is what one frame of `W` bytes leaves (`lose_lose`), and the
unknowns are those of `W` bytes, so it ends as `scrubTailG W` does
(`TailRunG`). -/

theorem toNat_addr_sub {x y : Addr} : (x - y).toNat = (x.toNat + (2 ^ 64 - y.toNat)) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]; omega

/-- A released frame of `B` bytes from `a` and then one of `A` bytes above
it, with the unknowns the first left, are one frame of `B + A` bytes. -/
theorem lose_lose {m : Mem} {a : Addr} {A B : Nat} {u : Nat → BitVec 64} (hB : B % 8 = 0)
    (hAB : B + A < 2 ^ 64) :
    lose (lose m a B u) (a + BitVec.ofNat 64 B) A (fun n => u (n + B / 4)) = lose m a (B + A) u := by
  funext x
  have ht := (x - a).isLt
  have hx : (x - (a + BitVec.ofNat 64 B)).toNat = ((x - a).toNat + (2 ^ 64 - B)) % 2 ^ 64 := by
    simp only [toNat_addr_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := x.isLt; have := a.isLt
    rw [Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega)]
    omega
  unfold lose
  dsimp only
  rw [hx]
  by_cases h₁ : (x - a).toNat < B
  · have h₂ : ¬ ((x - a).toNat + (2 ^ 64 - B)) % 2 ^ 64 < A := by omega
    have h₃ : (x - a).toNat < B + A := by omega
    simp only [h₂, h₁, h₃, ↓reduceIte]
  · have e : ((x - a).toNat + (2 ^ 64 - B)) % 2 ^ 64 = (x - a).toNat - B := by omega
    have e₁ : 2 * (((x - a).toNat - B) / 8) + B / 4 = 2 * ((x - a).toNat / 8) := by omega
    have e₂ : 2 * (((x - a).toNat - B) / 8) + 1 + B / 4 = 2 * ((x - a).toNat / 8) + 1 := by omega
    have e₃ : ((x - a).toNat - B) % 8 = (x - a).toNat % 8 := by omega
    rw [e]
    simp only [h₁, ↓reduceIte, e₁, e₂, e₃]
    by_cases h₃ : (x - a).toNat - B < A
    · have h₄ : (x - a).toNat < B + A := by omega
      simp only [h₃, h₄, ↓reduceIte]
    · have h₄ : ¬ (x - a).toNat < B + A := by omega
      simp only [h₃, h₄, ↓reduceIte]

theorem tailL_run {W : Nat} (hW : 4080 < W ∧ W < 8176 ∧ W % 16 = 0) (u : State) (hsp : W ≤ u.sp.toNat) :
    ∃ u', Exec isa (scrubTailL W) u (tailTraceG u.sp W (List.range (W / 16))) u' ∧
      TailRunG W (List.range (W / 16)) u u' := by
  have hspl := u.sp.isLt
  let ks := List.range (W / 16)
  let b := u.sp - BitVec.ofNat 64 W
  let o := u.sp - BitVec.ofNat 64 (W - 4080)
  have hbt : b.toNat = u.sp.toNat - W := by
    simp only [b, toNat_addr_sub, BitVec.toNat_ofNat]; omega
  have hot : o.toNat = u.sp.toNat - (W - 4080) := by
    simp only [o, toNat_addr_sub, BitVec.toNat_ofNat]; omega
  have hob : o - BitVec.ofNat 64 4080 = b := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_addr_sub, hot, hbt, BitVec.toNat_ofNat]; omega
  have hbo : b + BitVec.ofNat 64 4080 = o := by rw [← hob, BitVec.sub_add_cancel]
  let u₁ : State := { u with sp := o, wr := ⟨o, W - 4080⟩ :: u.wr }
  have hpush : isa.push (.alloc (W - 4080)) u = some u₁ := by
    have : 0 < W - 4080 ∧ W - 4080 < 4096 ∧ (W - 4080) % 16 = 0 ∧ W - 4080 ≤ u.sp.toNat :=
      ⟨by omega, by omega, by omega, by omega⟩
    simp only [isa, push, this, and_self, ↓reduceIte]; rfl
  let u₁' : State := { u₁ with sp := b, wr := ⟨b, 4080⟩ :: u₁.wr }
  have hpush' : isa.push (.alloc 4080) u₁ = some u₁' := by
    have : 4080 ≤ u₁.sp.toNat := by show 4080 ≤ o.toNat; omega
    simp only [isa, push, this, and_self]
    simp only [u₁', u₁, hob]; rfl
  let u₂ : State := (u₁'.setV .v31 0).write .x .x9 u₁'.sp
  have h₂ : execBlock isa [.vop (.movi0 .v31), .addSp .x9 0] u₁' = some (u₂, []) := by
    simp [execBlock, isa, exec, VOp.eval, addrs, u₂, State.setV]
  have hb₂ : u₂.gpr .x9 = b := by simp [u₂, u₁', State.write]
  have hv₂ : u₂.v .v31 = 0 := by simp [u₂, State.write, State.setV]
  have hR : GranulesIn u₂.wr b ks := by
    intro k hk
    have hk' := List.mem_range.mp hk
    by_cases hlo : 16 * k + 16 ≤ 4080
    · refine ⟨⟨b, 4080⟩, by simp [u₂, u₁', State.write, State.setV], ?_⟩
      unfold Region.Contains
      simp only [BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · refine ⟨⟨o, W - 4080⟩, by simp [u₂, u₁', u₁, State.write, State.setV], ?_⟩
      unfold Region.Contains
      dsimp only
      rw [← hbo, ← BitVec.sub_sub, BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add,
        BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * k < 2 ^ 64)]
      omega
  have hs := storesL_run (W := W) (by omega) b ks u₂ hb₂ hv₂ hR (fun k hk => by have := List.mem_range.mp hk; omega)
  have hblk : execBlock isa (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL ks) u₁' =
      some ({ u₂ with mem := zeroG b ks u₂.mem }, storesTraceL b ks) := by
    rw [show (.vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStoresL ks : List Instr) =
        [.vop (.movi0 .v31), .addSp .x9 0] ++ scrubStoresL ks from rfl,
      execBlock_append, h₂, Option.bind_some, hs]
    rfl
  let u₃ : State := { u₂ with mem := zeroG b ks u₂.mem }
  let u₄ : State := { u₃ with
    sp := u₃.sp + BitVec.ofNat 64 4080, wr := u₃.wr.tail,
    mem := lose u₃.mem u₃.sp 4080 u₃.unknowns, unknowns := fun n => u₃.unknowns (n + 4080 / 4) }
  have hpop' : isa.pop (.free 4080) u₁' u₃ = some u₄ := by
    have hc : 0 < 4080 ∧ 4080 < 4096 ∧ 4080 % 16 = 0 ∧ u₃.sp = u₁'.sp ∧ u₃.wr = u₁'.wr ∧
        u₁'.wr.head? = some ⟨u₁'.sp, 4080⟩ := ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩
    simp only [isa, pop, hc, and_self, ↓reduceIte]
    rfl
  have hsp₄ : u₄.sp = o := by
    show u₁'.sp + BitVec.ofNat 64 4080 = o
    exact hbo
  let u₅ : State := { u₄ with
    sp := o + BitVec.ofNat 64 (W - 4080), wr := u₄.wr.tail,
    mem := lose u₄.mem o (W - 4080) u₄.unknowns, unknowns := fun n => u₄.unknowns (n + (W - 4080) / 4) }
  have hpop : isa.pop (.free (W - 4080)) u₁ u₄ = some u₅ := by
    have hc : 0 < W - 4080 ∧ W - 4080 < 4096 ∧ (W - 4080) % 16 = 0 ∧ u₄.sp = u₁.sp ∧ u₄.wr = u₁.wr ∧
        u₁.wr.head? = some ⟨u₁.sp, W - 4080⟩ := ⟨by omega, by omega, by omega, hsp₄, rfl, rfl⟩
    simp only [isa, pop, hc, and_self, ↓reduceIte]
    rfl
  refine ⟨u₅, ?_, ?_⟩
  · have := Exec.frame (M := isa) hpush (Exec.frame (M := isa) hpush' (Exec.block hblk) hpop') hpop
    simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at this
    exact this
  · constructor
    · funext q
      by_cases hq : q = .x9
      · subst hq; simp [u₅, u₄, u₃, u₂, u₁', b, State.write]
      · simp [u₅, u₄, u₃, u₂, u₁', u₁, State.write, State.setV, hq]
    · funext w
      by_cases hw : w = .v31
      · subst hw; simp [u₅, u₄, u₃, u₂, u₁', State.write, State.setV]
      · simp [u₅, u₄, u₃, u₂, u₁', u₁, State.write, State.setV, hw]
    · show o + BitVec.ofNat 64 (W - 4080) = u.sp
      exact BitVec.sub_add_cancel _ _
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [u₅, u₄, u₃, u₂, u₁', u₁, State.write, State.setV]
      funext n
      exact congrArg u.unknowns (by omega)
    · have key := lose_lose (m := zeroG b ks u.mem) (a := b) (A := W - 4080) (B := 4080) (u := u.unknowns)
        (by decide) (by omega)
      rw [show 4080 + (W - 4080) = W by omega, hbo] at key
      simp only [u₅, u₄, u₃, u₂, u₁', u₁, State.write, State.setV]
      exact key

end VG.AArch64.Scrub

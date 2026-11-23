module

public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# The run of the stack's clearing (AArch64)

`tailG_run`: `scrubTailG W ks` (`Impl/Scrub/AArch64/Scrub.lean`) runs from
any state whose stack pointer has `W` bytes below it, with a trace of the
stack pointer alone. It writes `x9` (the frame's base) and `v31` (zero), and
leaves the granules `ks` of the `W` bytes below the stack pointer zeroed and
then released (`lose`), the rest of memory, the regions, the stack pointer
and the flags as they were. `scrubAll` zeroes every granule
(`ks = List.range (W / 16)`); `tailL_run` is the same for `scrubTailL`, whose
`W` bytes take two frames.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.AArch64 VG.Impl.Scrub.AArch64

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

/-! ## The loop

`scrubLoopBody W` zeroes the `W` bytes at `x9` (the frame's base) by passes of
four granules (`scrubPass`), then a store for each granule left. -/

/-- `inG` of the first `K` granules: the first `16 K` bytes. -/
theorem inG_range (b x : Addr) (K : Nat) : inG b (List.range K) x = decide ((x - b).toNat < 16 * K) := by
  simp only [inG]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h1, h2⟩; omega
  · intro h; exact ⟨(x - b).toNat / 16, by omega, by omega, by omega⟩

/-- Zeroing the `c` granules from `b + 16 a` after the `a` from `b` zeroes the
`a + c` from `b`. -/
theorem zeroG_range_append {b : Addr} {a c : Nat} (h : 16 * (a + c) < 2 ^ 64) (m : Mem) :
    zeroG (b + BitVec.ofNat 64 (16 * a)) (List.range c) (zeroG b (List.range a) m) =
      zeroG b (List.range (a + c)) m := by
  funext x
  have hlt : 16 * a < 2 ^ 64 := by omega
  have hx : (x - (b + BitVec.ofNat 64 (16 * a))).toNat = ((x - b).toNat + (2 ^ 64 - 16 * a)) % 2 ^ 64 := by
    rw [show x - (b + BitVec.ofNat 64 (16 * a)) = (x - b) - BitVec.ofNat 64 (16 * a) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  have ht := (x - b).isLt
  simp only [zeroG, inG_range, hx]
  by_cases h1 : (x - b).toNat < 16 * a
  · have h2 : (x - b).toNat < 16 * (a + c) := by omega
    simp only [h1, h2, decide_true, ↓reduceIte, ite_self]
  · by_cases h2 : (x - b).toNat < 16 * (a + c)
    · have : ((x - b).toNat + (2 ^ 64 - 16 * a)) % 2 ^ 64 < 16 * c := by omega
      simp only [h2, this, decide_true, ↓reduceIte]
    · have : ¬ ((x - b).toNat + (2 ^ 64 - 16 * a)) % 2 ^ 64 < 16 * c := by omega
      simp only [h1, h2, this, decide_false, ↓reduceIte, Bool.false_eq_true]

/-- Each granule of the `W` bytes from `b` is in a writable region. -/
def AllIn (wr : List Region) (b : Addr) (W : Nat) : Prop :=
  ∀ k, 16 * k + 16 ≤ W → InRegions wr (b + BitVec.ofNat 64 (16 * k)) 16

/-- The granules `ks` from `b + 16 a` are writable. -/
theorem granulesIn_off {wr : List Region} {b : Addr} {W a : Nat} (hR : AllIn wr b W)
    {ks : List Nat} (hks : ∀ k ∈ ks, 16 * (a + k) + 16 ≤ W) :
    GranulesIn wr (b + BitVec.ofNat 64 (16 * a)) ks := fun k hk' => by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← Nat.mul_add]
  exact hR _ (hks k hk')

/-- The granules of the region of the `W` bytes from `b` are in it. -/
theorem allIn_of {wr : List Region} {b : Addr} {W : Nat} (hW : W < 2 ^ 16) (hR : (⟨b, W⟩ : Region) ∈ wr) :
    AllIn wr b W := fun k hk =>
  granulesIn_of (ks := [k]) hW hR (fun k' h => by rw [List.mem_singleton.mp h]; exact hk) k (List.mem_singleton_self _)

/-- The trace of `n` passes of the loop from `x9 = p`. -/
def passesTr (p : Addr) : Nat → List Leak
  | 0 => []
  | 1 => storesTraceL p (List.range 4) ++ [.branch false]
  | n + 2 => storesTraceL p (List.range 4) ++ .branch true :: passesTr (p + BitVec.ofNat 64 64) (n + 1)

/-- `u` with `x9` at `p` and `x10` at `z`, and the memory `m`. -/
abbrev passSt (u : State) (p z : BitVec 64) (m : Mem) : State :=
  { u with gpr := fun q => if q = .x9 then p else if q = .x10 then z else u.gpr q, mem := m }

theorem passSt_passSt (u : State) (p z p' z' : BitVec 64) (m m' : Mem) :
    passSt (passSt u p z m) p' z' m' = passSt u p' z' m' := by
  simp only [passSt]
  congr 1
  funext q
  by_cases h9 : q = .x9
  · simp [h9]
  · by_cases h10 : q = .x10 <;> simp [h9, h10]

/-- One pass of the loop, from a state whose `x9` is `16 (4 i)` bytes into the
region of `W` bytes from `b`, whose first `4 i` granules of the memory `m₀`
are zero, with `j + 1` in `x10`: the first `4 (i + 1)` granules zeroed, `x9`
past them and `j` in `x10`. -/
theorem pass_run {b : Addr} {W : Nat} (hW : W < 2 ^ 16) (m₀ : Mem) (j i : Nat) (u : State)
    (hn : 64 * (i + 1) ≤ W) (hR : AllIn u.wr b W)
    (h9 : u.gpr .x9 = b + BitVec.ofNat 64 (16 * (4 * i))) (h10 : u.gpr .x10 = BitVec.ofNat 64 (j + 1))
    (hv : u.v .v31 = 0) (hm : u.mem = zeroG b (List.range (4 * i)) m₀) :
    execBlock isa scrubPass u = some (passSt u (b + BitVec.ofNat 64 (16 * (4 * (i + 1)))) (BitVec.ofNat 64 j)
      (zeroG b (List.range (4 * (i + 1))) m₀), storesTraceL (u.gpr .x9) (List.range 4)) := by
  have hks : ∀ k ∈ List.range 4, 16 * (4 * i + k) + 16 ≤ W := fun k hk => by
    have := List.mem_range.mp hk; omega
  have hks' : ∀ k ∈ List.range 4, 16 * k + 16 ≤ 64 := fun k hk => by
    have := List.mem_range.mp hk; omega
  have hgi : GranulesIn u.wr (u.gpr .x9) (List.range 4) := by
    rw [h9]; exact granulesIn_off hR hks
  have hs := storesL_run (W := 64) (by decide) (u.gpr .x9) (List.range 4) u rfl hv hgi hks'
  have hm₁ : zeroG (u.gpr .x9) (List.range 4) u.mem = zeroG b (List.range (4 * (i + 1))) m₀ := by
    rw [h9, hm, zeroG_range_append (by omega), show 4 * i + 4 = 4 * (i + 1) by omega]
  have hx9 : u.gpr .x9 + BitVec.ofNat 64 64 = b + BitVec.ofNat 64 (16 * (4 * (i + 1))) := by
    rw [h9, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 16 * (4 * i) + 64 = 16 * (4 * (i + 1)) by omega]
  have hx10 : u.gpr .x10 - BitVec.ofNat 64 1 = BitVec.ofNat 64 j := by
    rw [h10]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [show scrubPass = scrubStoresL (List.range 4) ++ [.addImm .x .x9 .x9 64, .subImm .x .x10 .x10 1]
    from rfl, execBlock_append, hs, Option.bind_some]
  simp only [execBlock, isa, exec, show (64 : Nat) < 4096 by decide, show (1 : Nat) < 4096 by decide,
    ↓reduceIte, Option.map_some, addrs, List.map_nil, List.append_nil, State.read, State.write,
    Size.bits, BitVec.setWidth_eq, hm₁, Option.some.injEq, Prod.mk.injEq, and_true]
  simp only [passSt]
  congr 1
  funext q
  by_cases hq10 : q = .x10
  · subst hq10; simp only [reduceCtorEq, ↓reduceIte, hx10]
  · by_cases hq9 : q = .x9
    · subst hq9; simp only [reduceCtorEq, ↓reduceIte, hx9]
    · simp [hq9, hq10]

/-- `n` passes of the loop, as `pass_run`, from `n` in `x10`: the first
`4 (i + n)` granules zeroed, `x9` past them and `x10` zero. -/
theorem passes_run {b : Addr} {W : Nat} (hW : W < 2 ^ 16) (m₀ : Mem) :
    ∀ (n i : Nat) (u : State), 0 < n → 64 * (i + n) ≤ W → AllIn u.wr b W →
      u.gpr .x9 = b + BitVec.ofNat 64 (16 * (4 * i)) → u.gpr .x10 = BitVec.ofNat 64 n → u.v .v31 = 0 →
      u.mem = zeroG b (List.range (4 * i)) m₀ →
      Exec isa (.loop (.block scrubPass) (.nonzero .x .x10)) u (passesTr (u.gpr .x9) n)
        (passSt u (b + BitVec.ofNat 64 (16 * (4 * (i + n)))) 0 (zeroG b (List.range (4 * (i + n))) m₀))
  | 0, _, _, h, _, _, _, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, i, u, _, hn, hR, h9, h10, hv, hm => by
    have hp := pass_run hW m₀ 0 i u hn hR h9 h10 hv hm
    have hz : isa.eval (.nonzero .x .x10) (passSt u (b + BitVec.ofNat 64 (16 * (4 * (i + 1)))) (BitVec.ofNat 64 0)
        (zeroG b (List.range (4 * (i + 1))) m₀)) = some false := by
      simp [eval, State.read]
    exact Exec.loopExit (Exec.block hp) hz
  | n + 2, i, u, _, hn, hR, h9, h10, hv, hm => by
    have hp := pass_run hW m₀ (n + 1) i u (by omega) hR h9 h10 hv hm
    let u₁ := passSt u (b + BitVec.ofNat 64 (16 * (4 * (i + 1)))) (BitVec.ofNat 64 (n + 1))
      (zeroG b (List.range (4 * (i + 1))) m₀)
    have hnz : isa.eval (.nonzero .x .x10) u₁ = some true := by
      simp only [eval, u₁, State.read, reduceCtorEq, ↓reduceIte, Size.bits, BitVec.setWidth_eq,
        Option.some.injEq, bne_iff_ne, ne_eq]
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    have ih := passes_run hW m₀ (n + 1) (i + 1) u₁ (by omega) (by omega) hR
      (by simp [u₁]) (by simp [u₁]) (by simp [u₁, hv]) (by simp [u₁])
    have e := Exec.loopNext (Exec.block hp) hnz ih
    have hx : u₁.gpr .x9 = u.gpr .x9 + BitVec.ofNat 64 64 := by
      simp only [u₁, ↓reduceIte, h9, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [show 16 * (4 * i) + 64 = 16 * (4 * (i + 1)) by omega]
    rw [hx, passSt_passSt, show i + 1 + (n + 1) = i + (n + 2) by omega] at e
    exact e

theorem zeroG_nil (b : Addr) (m : Mem) : zeroG b [] m = m := by
  funext x; simp [zeroG, inG]

/-- The trace of `scrubLoopBody W` from `x9 = b`. -/
def loopBodyTr (b : Addr) (W : Nat) : List Leak :=
  passesTr b (W / 64) ++ storesTraceL (b + BitVec.ofNat 64 (16 * (4 * (W / 64)))) (List.range (W % 64 / 16))

/-- `scrubLoopBody W`, `64 ≤ W`, from a state that may write the `W` bytes at
its stack pointer `b`, zeroes them, with the trace of their addresses and the
loop's branches alone, and leaves `q31` zero, `x9` past the passes' granules
and `x10` zero. -/
theorem loopBody_run {b : Addr} {W : Nat} (hW : W < 2 ^ 16) (h64 : 64 ≤ W) (h16 : W % 16 = 0) (u : State)
    (hR : AllIn u.wr b W) (hb : u.sp = b) :
    Exec isa (scrubLoopBody W) u (loopBodyTr b W)
      (passSt (u.setV .v31 0) (b + BitVec.ofNat 64 (16 * (4 * (W / 64)))) 0 (zeroG b (List.range (W / 16)) u.mem)) := by
  let n := W / 64
  let u₀ := passSt (u.setV .v31 0) b (BitVec.ofNat 64 n) u.mem
  have h₀ : execBlock isa [.vop (.movi0 .v31), .addSp .x9 0, .movz .x .x10 (BitVec.ofNat 16 n) 0] u =
      some (u₀, []) := by
    simp only [execBlock, isa, exec, VOp.eval, show (0 : Nat) < 4096 by decide, Size.bits,
      show 16 * 0 < 64 by decide, ↓reduceIte, Option.map_some, addrs, List.map_nil, List.append_nil,
      Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [u₀, passSt, State.write, State.setV, hb]
    congr 1
    funext q
    by_cases hq10 : q = .x10
    · subst hq10
      have hmz : BitVec.setWidth 64 (BitVec.ofNat 16 n) <<< (16 * 0) = BitVec.ofNat 64 n := by
        rw [Nat.mul_zero, BitVec.shiftLeft_zero]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
      simp only [reduceCtorEq, ↓reduceIte, hmz, BitVec.setWidth_eq]
    · by_cases hq9 : q = .x9
      · subst hq9; simp
      · simp [hq9, hq10]
  have hp := passes_run (b := b) hW u.mem n 0 u₀ (by omega) (by omega) hR
    (by simp [u₀]) (by simp [u₀]) (by simp [u₀, State.setV]) (by simp [u₀, zeroG_nil])
  simp only [Nat.zero_add] at hp
  rw [show u₀.gpr .x9 = b by simp [u₀]] at hp
  let u₁ := passSt u₀ (b + BitVec.ofNat 64 (16 * (4 * n))) 0 (zeroG b (List.range (4 * n)) u.mem)
  have hks : ∀ k ∈ List.range (W % 64 / 16), 16 * (4 * n + k) + 16 ≤ W := fun k hk => by
    have := List.mem_range.mp hk; omega
  have hks' : ∀ k ∈ List.range (W % 64 / 16), 16 * k + 16 ≤ 64 := fun k hk => by
    have := List.mem_range.mp hk; omega
  have hs := storesL_run (W := 64) (by decide) (b + BitVec.ofNat 64 (16 * (4 * n))) (List.range (W % 64 / 16)) u₁
    (by simp [u₁]) (by simp [u₁, u₀, State.setV]) (granulesIn_off hR hks) hks'
  have hm : zeroG (b + BitVec.ofNat 64 (16 * (4 * n))) (List.range (W % 64 / 16)) u₁.mem =
      zeroG b (List.range (W / 16)) u.mem := by
    simp only [u₁]
    rw [zeroG_range_append (by omega), show 4 * n + W % 64 / 16 = W / 16 by omega]
  rw [hm] at hs
  have e := Exec.seq (Exec.block h₀) (Exec.seq hp (Exec.block hs))
  rw [List.nil_append] at e
  have hfin : ({ u₁ with mem := zeroG b (List.range (W / 16)) u.mem } : State) =
      passSt (u.setV .v31 0) (b + BitVec.ofNat 64 (16 * (4 * (W / 64)))) 0 (zeroG b (List.range (W / 16)) u.mem) := by
    show passSt u₀ _ 0 _ = _
    exact passSt_passSt _ _ _ _ _ _ _
  rw [hfin] at e
  exact e

/-- What `scrubTailLoop W` and `scrubTailG W` leave: `TailRunG`, with `x9`
`g9` of the stack pointer and `x10` `f10` of its value. -/
structure TailRunF (g9 : Addr → BitVec 64) (f10 : BitVec 64 → BitVec 64) (W : Nat) (u u' : State) : Prop where
  gpr : u'.gpr = fun q => if q = .x9 then g9 u.sp else if q = .x10 then f10 (u.gpr .x10) else u.gpr q
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
  mem : u'.mem = lose (zeroG (u.sp - BitVec.ofNat 64 W) (List.range (W / 16)) u.mem) (u.sp - BitVec.ofNat 64 W) W u.unknowns

theorem TailRunG.toF {W : Nat} {u u' : State} (h : TailRunG W (List.range (W / 16)) u u') :
    TailRunF (fun sp => sp - BitVec.ofNat 64 W) id W u u' where
  gpr := by
    rw [h.gpr]; funext q
    by_cases h9 : q = .x9
    · simp [h9]
    · by_cases h10 : q = .x10
      · subst h10; simp
      · simp [h9, h10]
  v := h.v
  sp := h.sp
  rd := h.rd
  wr := h.wr
  c := h.c
  nf := h.nf
  zf := h.zf
  vf := h.vf
  dit := h.dit
  unknowns := h.unknowns
  mem := h.mem

/-- The trace of `scrubTailLoop W` from the stack pointer `sp`. -/
def tailLoopTr (sp : Addr) (W : Nat) : List Leak := loopBodyTr (sp - BitVec.ofNat 64 W) W

/-- `scrubTailLoop W` zeroes the `W` bytes below the stack pointer and
releases them, as `scrubTailG W` does but for `x9` and `x10`. -/
theorem tailLoop_run {W : Nat} (hW : 64 ≤ W ∧ W < 4096 ∧ W % 16 = 0) (u : State) (hsp : W ≤ u.sp.toNat) :
    ∃ u', Exec isa (scrubTailLoop W) u (tailLoopTr u.sp W) u' ∧
      TailRunF (fun sp => sp - BitVec.ofNat 64 W + BitVec.ofNat 64 (16 * (4 * (W / 64)))) (fun _ => 0) W u u' := by
  let b := u.sp - BitVec.ofNat 64 W
  let u₁ : State := { u with sp := b, wr := ⟨b, W⟩ :: u.wr }
  have hpush : isa.push (.alloc W) u = some u₁ := by
    simp only [isa, push, show 0 < W by omega, hW.2.1, hW.2.2, hsp, and_self, ↓reduceIte]; rfl
  have hb := loopBody_run (by omega) hW.1 hW.2.2 u₁ (allIn_of (by omega) (by simp [u₁])) rfl
  let u₃ := passSt (u₁.setV .v31 0) (b + BitVec.ofNat 64 (16 * (4 * (W / 64)))) 0 (zeroG b (List.range (W / 16)) u₁.mem)
  have hpop : isa.pop (.free W) u₁ u₃ = some { u₃ with
      sp := u₃.sp + BitVec.ofNat 64 W, wr := u₃.wr.tail,
      mem := lose u₃.mem u₃.sp W u₃.unknowns, unknowns := fun n => u₃.unknowns (n + W / 4) } := by
    have hc : 0 < W ∧ W < 4096 ∧ W % 16 = 0 ∧ u₃.sp = u₁.sp ∧ u₃.wr = u₁.wr ∧
        u₁.wr.head? = some ⟨u₁.sp, W⟩ := ⟨by omega, hW.2.1, hW.2.2, rfl, rfl, rfl⟩
    simp only [isa, pop, hc, and_self, ↓reduceIte]
  refine ⟨{ u₃ with
      sp := u₃.sp + BitVec.ofNat 64 W, wr := u₃.wr.tail,
      mem := lose u₃.mem u₃.sp W u₃.unknowns, unknowns := fun n => u₃.unknowns (n + W / 4) }, ?_, ?_⟩
  · have := Exec.frame (M := isa) hpush hb hpop
    simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at this
    exact this
  · constructor
    · funext q
      by_cases h9 : q = .x9
      · subst h9; simp [u₃, b]
      · by_cases h10 : q = .x10
        · subst h10; simp [u₃]
        · simp [u₃, u₁, State.setV, h9, h10]
    · funext w
      by_cases hw : w = .v31
      · subst hw; simp [u₃, u₁, State.setV]
      · simp [u₃, u₁, State.setV, hw]
    · simp only [u₃, u₁, b, State.setV]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      have := u.sp.isLt
      omega
    all_goals simp [u₃, u₁, b, State.setV]

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

/-- `scrubTailL W` zeroes the `W` bytes below the stack pointer and releases
them, as `scrubTailLoop W` does. -/
theorem tailL_run {W : Nat} (hW : 4080 < W ∧ W < 8176 ∧ W % 16 = 0) (u : State) (hsp : W ≤ u.sp.toNat) :
    ∃ u', Exec isa (scrubTailL W) u (tailLoopTr u.sp W) u' ∧
      TailRunF (fun sp => sp - BitVec.ofNat 64 W + BitVec.ofNat 64 (16 * (4 * (W / 64)))) (fun _ => 0) W u u' := by
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
  have hR : AllIn u₁'.wr b W := by
    intro k hk'
    by_cases hlo : 16 * k + 16 ≤ 4080
    · refine ⟨⟨b, 4080⟩, by simp [u₁'], ?_⟩
      unfold Region.Contains
      simp only [BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · refine ⟨⟨o, W - 4080⟩, by simp [u₁', u₁], ?_⟩
      unfold Region.Contains
      dsimp only
      rw [← hbo, ← BitVec.sub_sub, BitVec.add_sub_comm, BitVec.sub_self, BitVec.zero_add,
        BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * k < 2 ^ 64)]
      omega
  have hblk := loopBody_run (by omega) (by omega) hW.2.2 u₁' hR rfl
  let u₃ : State := passSt (u₁'.setV .v31 0) (b + BitVec.ofNat 64 (16 * (4 * (W / 64)))) 0 (zeroG b ks u₁'.mem)
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
  · have := Exec.frame (M := isa) hpush (Exec.frame (M := isa) hpush' hblk hpop') hpop
    simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at this
    exact this
  · constructor
    · funext q
      by_cases h9 : q = .x9
      · subst h9; simp [u₅, u₄, u₃, b]
      · by_cases h10 : q = .x10
        · subst h10; simp [u₅, u₄, u₃]
        · simp [u₅, u₄, u₃, u₁', u₁, State.setV, h9, h10]
    · funext w
      by_cases hw : w = .v31
      · subst hw; simp [u₅, u₄, u₃, u₁', State.setV]
      · simp [u₅, u₄, u₃, u₁', u₁, State.setV, hw]
    · show o + BitVec.ofNat 64 (W - 4080) = u.sp
      exact BitVec.sub_add_cancel _ _
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [u₅, u₄, u₃, u₁', u₁, State.setV]
      funext n
      exact congrArg u.unknowns (by omega)
    · have key := lose_lose (m := zeroG b ks u.mem) (a := b) (A := W - 4080) (B := 4080) (u := u.unknowns)
        (by decide) (by omega)
      rw [show 4080 + (W - 4080) = W by omega, hbo] at key
      simp only [u₅, u₄, u₃, u₁', u₁, State.setV]
      exact key

end VG.AArch64.Scrub

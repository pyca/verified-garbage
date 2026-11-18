module

public import VerifiedGarbage.Proof.Argon2.MemoryInit
public import VerifiedGarbage.Proof.Argon2.Matrix
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Locals
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Calls
import VerifiedGarbage.Proof.Argon2.Arm.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.Arm.Mix
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Argon2.Arm.Derive.Clear`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `r6` (`blocks · 256`), with `r5` the next word's address and `r7`
zero.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_subs wp_str op2_imm op2_lsl)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := State.addr (memP s₀)

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    State.addr (x + BitVec.ofNat 32 d + BitVec.ofNat 32 k) = State.addr x + BitVec.ofNat 64 (d + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact addr_add (by omega_using [h])

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : Inv s₀ s) {R : Region} (hR : R ∈ bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : Inv s₀ t :=
  h.step u.sp (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- The loop's state after `j` words. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  r5 : s.gpr .r5 = memP s₀ + BitVec.ofNat 32 (4 * j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (blocksN s₀ * 256 - j)
  r7 : s.gpr .r7 = 0
  zero : ∀ i < 4 * j, s.mem (memB s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [memR s₀] s₁.mem s.mem

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks_pos : 1 ≤ blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (prm s₀).segmentLen by have := hp.segLen_two; omega_using [this])
  omega_using [this]

theorem clearLoop_ok {s₁ : State} (h : CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.Arm.Derive.clearWord) .ne) s₁ (CI s₀ s₁ (blocksN s₀ * 256)) := by
  have hm := hp.mem_fits
  have hb := hp.blocks_lt
  have b1 := blocks_pos hp
  refine WP.loop (M := isa) (fun n s => ∃ j, n = blocksN s₀ * 256 - j ∧ j < blocksN s₀ * 256 ∧ CI s₀ s₁ j s)
    ?_ (blocksN s₀ * 256) s₁ ⟨0, by omega_using [], by omega_using [b1], h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have ea : State.addr (s.gpr .r5 + BitVec.ofNat 32 0) = memB s₀ + BitVec.ofNat 64 (4 * j) := by
    rw [c.r5, addr32 (by omega_using [hm, hj]), Nat.add_zero]
  have hc : (memR s₀).Contains (memB s₀ + BitVec.ofNat 64 (4 * j)) 4 :=
    Offset.contains_base _ (by omega_using [hj]) (by omega_using [hm, hj])
  simp only [Impl.Argon2.Arm.Derive.clearWord]
  refine wp_str (by decide) ea (by rw [c.inv.wr]; exact ⟨_, mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.store (R := memR s₀) (by simp) hc u₁
  refine wp_add (op2_imm (by decide)) fun t₂ u₂ => wp_subs (op2_imm (by decide)) fun t u zf => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u (by decide)
  have e₁ : t.gpr .r6 = BitVec.ofNat 32 (blocksN s₀ * 256 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  have next : CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.r5, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r7]
    · rw [u.mem, u₂.mem, u₁.mem, c.r7, writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show memB s₀ + BitVec.ofNat 64 i = memB s₀ + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega_using [hi'])],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  have z : VG.Arm.eval .ne t = some (!decide (blocksN s₀ * 256 - (j + 1) = 0)) := by
    rw [MdStream.Arm.eval_ne, zf, ← u.gpr, e₁, MdStream.Arm.ofNat_beq_zero (by omega_using [hm])]
  by_cases done : j + 1 = blocksN s₀ * 256
  · refine .inl ⟨by rw [z]; simp; omega_using [done], done ▸ next⟩
  · refine .inr ⟨by rw [z]; simp; omega_using [hj, done], blocksN s₀ * 256 - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, done], next⟩

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have eb : blocksN s₀ = (arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.Arm.Derive.clear Impl.Argon2.Arm.Derive.clearSetup
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_ldarg hp (h.upd u₁ (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.upd u₃ (by decide)).upd u₄ (by decide)
  refine (clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega_using [hi])⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [shl_nat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
    omega_using [eb]
  · rw [show s.mem = s₄.mem by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.HCall`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` with its register arguments in
`r0`–`r3` and `scratch` (from `r12`) pushed with `lr`, from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 40 bytes below the locals.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat pushed_arg pushed_argAddr frameCall_ok stkR_inner stkR_sub)
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_stack : armStack Impl.Argon2.Arm.HPrime.code = 32 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

/-- The registers `hPrimeCall` pushes. -/
abbrev hregs : List Reg := [.r12, .lr]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem call_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (call_stk hp)

theorem loc_call : (locR s₀).Disjoint (callR s₀) := by
  have hE := E_nat hp
  have := hp.sp_lo
  have := E_hi hp
  show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
  rw [← addr_sub' (by omega_arith)]
  exact disj32 (.inr (by rw [sub_toNat' (by omega_arith)]; omega_arith)) (by omega_arith) (by rw [sub_toNat' (by omega_arith)]; omega_arith)

theorem loc_sub_stk : Region.Sub (locR s₀) (stkR0 s₀) := by
  simpa using frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (loc_sub_stk hp)

/-- The regions H′ is given. -/
abbrev hRd (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩]
abbrev hWr (s₀ s : State) : List Region := [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀]

/-- What H′ needs, from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) (hdx : s.gpr .r12 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) :
    HPrime.hPrimeArm.pre ((pushed hregs s).callEntry.withRegions (hRd s) (hWr s₀ s)) ∧
      Covers (hRd s ++ hWr s₀ s) ((pushed hregs s).rd ++ (pushed hregs s).wr) ∧
      Covers (hWr s₀ s) (pushed hregs s).wr := by
  have hE := E_nat hp
  have hlo := hp.sp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega_arith
  have a0 : ∀ {rd wr}, stackArg ((pushed hregs s).callEntry.withRegions rd wr) 0 = scrP s₀ := by
    intro rd wr; rw [pushed_arg hn (by decide)]; exact hdx
  have eA : ∀ {rd wr}, stackArgAddr ((pushed hregs s).callEntry.withRegions rd wr) 0 =
      State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length) := pushed_argAddr hn
  have eSp : ∀ {rd wr}, ((pushed hregs s).callEntry.withRegions rd wr).sp = s.sp - BitVec.ofNat 32 8 := by
    intro rd wr; simp [pushed_sp]
  have g : ∀ r, r ∉ linkRegs → ∀ {rd wr}, ((pushed hregs s).callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun r hr rd wr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  have cI : Covers [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  have I_scr : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  have S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack and argument.
  have cA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩ (callR s₀) := by
    rw [sp]
    show Region.Sub ⟨State.addr (E s₀) - BitVec.ofNat 64 8, 4⟩ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    have t8 : (E s₀ - BitVec.ofNat 32 8).toNat = (E s₀).toNat - 8 := sub_toNat' (by omega_arith)
    have t40 : (E s₀ - BitVec.ofNat 32 40).toNat = (E s₀).toNat - 40 := sub_toNat' (by omega_arith)
    rw [← addr_sub' (x := E s₀) (k := 8) (by omega_arith), ← addr_sub' (x := E s₀) (k := 40) (by omega_arith)]
    exact sub32 (by rw [t8, t40]; omega_arith) (by rw [t8, t40]; omega_arith)
  have cS : Region.Sub (stkR (E s₀ - BitVec.ofNat 32 8) 32) (callR s₀) :=
    stkR_inner (sp := E s₀) (a := 32) (k := 8) (b := 40) (by omega_arith) (by omega_arith)
  have cS' : Region.Sub (stkR (s.sp - BitVec.ofNat 32 8) 32) (callR s₀) := by rw [sp]; exact cS
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeArm, State.withRegions_rd, State.withRegions_wr, a0, eA, eSp,
      g .r0 (by decide), g .r1 (by decide), g .r2 (by decide), g .r3 (by decide)]
    refine ⟨trivial, trivial, I_scr, O_scr, O_call.symm.sub_left cA, S_call.symm.sub_left cA,
      I_call.symm.sub_left cS', O_call.symm.sub_left cS', S_call.symm.sub_left cS', hinfit, houtfit, by omega_arith,
      ?_, ?_, hL⟩
    · rw [sub_toNat' (by omega_arith), sp]; omega_arith
    · rw [sub_toNat' (by omega_arith), sp]; omega_arith
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_rd, pushed_wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [addr_sub' hn]
      simp only [Region.Contains, List.length_cons, List.length_nil] at hc ⊢
      omega_arith
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) (hdx : s.gpr .r12 = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) →
      Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀, callR s₀] s.mem t.mem →
      bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        Spec.Argon2.hPrime (s.gpr .r3).toNat
          (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) → Q t) :
    WP isa Impl.Argon2.Arm.Derive.hPrimeCall s Q := by
  have hE := E_nat hp
  have hlo := hp.sp_lo
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega_arith
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  obtain ⟨pre, cv, cw⟩ := hcall_pre hp h hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine frameCall_ok (rs := hregs) (t := .r12) (by decide) (by decide) (by decide) (k := HPrime.hPrimeArm)
    HPrime.hPrime_verified.1 (K := 40) (by rw [hPrime_stack]; decide) (by rw [sp]; omega_arith) pre cv cw
    fun t mL uL hfl af post => ?_
  simp only [HPrime.hPrimeArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
    pushed_gpr] at post
  have bk : bytesAt (pushed hregs s).mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat :=
    bytes_keep (VG.Proof.Argon2.Arm.pushed_stk hn)
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right (by rw [sp]; exact stkR_sub (by decide) (by omega_arith)))
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .r1).isLt (by decide)))
  rw [bk] at post
  have O_call : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (callR s₀) := by
    refine (call_disj hp (R := RO) ?_).symm.sub_left sO
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO ⊢
    rcases hRO with rfl | rfl <;> simp
  have bo : bytesAt mL (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat :=
    bytes_keep hfl
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact O_call.sub_right (by rw [sp]; exact stkR_sub (by decide) (by omega_arith)))
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .r3).isLt (by decide)))
  have f₁ : Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, scrR s₀, callR s₀] s.mem mL :=
    af.frame.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨callR s₀, by simp, by rw [sp]; exact fun _ h => h⟩
  refine k _ (h.step af.sp (af.cs .r11 (by decide) (by decide)) af.rd af.wr (f₁.sub fun q hq => ?_))
    (fun q hq hl => af.cs q hq hl) f₁ (by rw [bo]; simpa using post)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block zeroBlock parseBlock)
open VG.Impl.Argon2.Arm.Derive (ld st)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega_arith) (by have := j.isLt; omega_arith)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain h0 : m a = 0 := by simpa using h 0 (by omega_arith)
    obtain h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega_arith)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega_arith)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : initCell p h0 0 k = zeroBlock := by
  unfold initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega_arith), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold initCell
  rw [cell_div (by omega_arith), cell_mod (by omega_arith)]
  exact ite_eq_left ⟨by omega_arith, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    initCell p h0 (l + 1) k = initCell p h0 l k := by
  unfold initCell
  obtain hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega_arith), ite_eq_left hc]
    · rw [ite_eq_right (by omega_arith), ite_eq_right hc]

/-- `a - b` is zero exactly when `a = b`, for 32-bit numbers. -/
theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      obtain e' := congrArg BitVec.toNat e
      have z : (0 : BitVec 32).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, z] at e'
      omega_arith
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr hne

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) (State.addr (E s₀)) n =
      bytesAt m (State.addr (E s₀)) n := by
  have := E_hi hp
  refine bytes_keep
    ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
      (Region.contains_self _ _))
    (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inl (by rw [loc_nat hp (d := d) (by omega_arith)]; omega_arith)) (by omega_arith)
    (by rw [loc_nat hp (d := d) (by omega_arith)]; omega_arith)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, bytes_word, bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (memR s₀) ∨ Region.Sub O (outR s₀)) :
    ∀ r ∈ [O, scrR s₀, callR s₀], Region.Disjoint ⟨State.addr (E s₀), 64⟩ r := by
  obtain sub : Region.Sub ⟨State.addr (E s₀), 64⟩ (locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((loc_disj' hp (R := memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((loc_disj' hp (R := outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sub
  · exact (loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch` and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < blocksN s₀) :
    ∀ r ∈ [scrR s₀, callR s₀], Region.Disjoint ⟨matrixCell (memB s₀) k, 1024⟩ r := by
  obtain sub : Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < blocksN s₀) :
    State.addr (memP s₀ + BitVec.ofNat 32 (k * 1024)) = matrixCell (memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  exact addr_add (by omega_arith)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < blocksN s₀) :
    Region.Sub ⟨matrixCell (memB s₀) k, 1024⟩ (memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < blocksN s₀) (hk : k < blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (memB s₀) j, 1024⟩ ⟨matrixCell (memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega_arith) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2)
    (r5 : s.gpr .r5 = BitVec.ofNat 32 l)
    (r6 : s.gpr .r6 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.Arm.Derive.initBlock c) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = h0 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧
      blockAt t.mem (matrixCell (memB s₀) (l * (prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < blocksN s₀, k ≠ l * (prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  obtain hE := E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  obtain hcell : l * (prm s₀).laneLen + c < blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  obtain hec : encodable (BitVec.ofNat 32 c) = true := by
    rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl <;> decide
  unfold Impl.Argon2.Arm.Derive.initBlock
  refine WP.seq (wp_mov (op2_imm hec) fun s₁ u₁ => ?_)
  obtain i₁ := h.upd u₁ (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  obtain i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine wp_ldarg hp i₇ (i := 15) (by decide) fun s₈ u₈ => WP.block_nil ?_
  obtain i₈ := i₇.upd u₈ (by decide)
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain g₈ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₈.gpr r = s.gpr r :=
    fun r a b d e f => by
      rw [u₈.other _ f, u₇.other _ e, u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  obtain r0₈ : s₈.gpr .r0 = E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      i₃.r11]
  obtain r1₈ : (s₈.gpr .r1).toNat = 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
  obtain r3₈ : (s₈.gpr .r3).toNat = 1024 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
  obtain r2₈ : s₈.gpr .r2 = s.gpr .r6 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, g₂, u₁.other _ (by decide)]
  obtain O : State.addr (s₈.gpr .r2) = matrixCell (memB s₀) (l * (prm s₀).laneLen + c) := by
    rw [r2₈, r6, cell_addr hp hcell]
  obtain sO : Region.Sub ⟨State.addr (s₈.gpr .r2), (s₈.gpr .r3).toNat⟩ (memR s₀) := by
    rw [O, r3₈]; exact cell_in_mem hcell
  obtain hcell' : (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  refine hcall_ok hp i₈ u₈.gpr
    ⟨locR s₀, by simp, 0, by rw [r0₈]; simp, by rw [r1₈]; show 0 + 72 ≤ 144; omega_arith⟩ (by rw [r0₈, r1₈]; omega_arith)
    ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [r3₈]; exact hcell'⟩
    (by rw [r2₈, r6, r3₈, add_nat (x := memP s₀) (k := (l * (prm s₀).laneLen + c) * 1024) (by omega_arith)]; omega_arith)
    (by rw [r3₈]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      obtain hd' := prm_offs d hd
      rw [lw_keep hp fr (call_sub (.inl sO)) hd'.1, lw_mem m₈, o₃ d (by omega_arith) (by omega_arith),
        o₂ d (by omega_arith) (by omega_arith), lw_mem u₁.mem]
  · rw [bytes_keep fr (h0_call hp (.inl sO)) (by omega_arith), m₈, m₃,
      loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .r5 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [cs .r6 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← r3₈, post, r3₈, r0₈, r1₈, bytes72, m₈]
    obtain w64 : s₃.mem.readW (State.addr (E s₀) + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← loc_addr hp (by omega_arith)]
      show lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    obtain w68 : s₃.mem.readW (State.addr (E s₀) + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← loc_addr hp (by omega_arith)]
      show lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), r5]
    rw [w64, w68, m₃, loc_bytes_store hp (by decide) (by decide), m₂, loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    obtain fs : Frame [⟨State.addr (E s₀ + BitVec.ofNat 32 64), 4⟩, ⟨State.addr (E s₀ + BitVec.ofNat 32 68), 4⟩]
        s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [blockAt_keep fr (fun r hr => ?_), m₈]
    · -- The stores to the locals.
      refine blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((loc_disj hp (d := 64) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
      · exact ((loc_disj hp (d := 68) (by decide) (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, r3₈]; exact cell_other hp hk hcell ne
      · exact cell_disj hp hk _ (by simp)
      · exact cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0
  r5 : s.gpr .r5 = BitVec.ofNat 32 l
  r6 : s.gpr .r6 = memP s₀ + BitVec.ofNat 32 (l * (prm s₀).laneLen * 1024)
  cells : ∀ k < blocksN s₀, blockAt s.mem (matrixCell (memB s₀) k) = initCell (prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  Prm.of_lw pr fun d _ => lw_mem h d

theorem r6_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < lanesN s₀) (h : LI s₀ h0 l s) :
    WP isa Impl.Argon2.Arm.Derive.initLane s fun t =>
      LI s₀ h0 (l + 1) t ∧ VG.Arm.eval .ne t = some (!decide (l + 1 = lanesN s₀)) := by
  obtain L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_arith
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.initLane
  refine WP.seq ((initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.r5
    (by rw [h.r6, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  obtain i₂ := i₁.upd u₂ (by decide)
  refine WP.seq ((initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1)
    (by decide) (by rw [u₂.other _ (by decide), e₁, h.r5])
    (by rw [u₂.gpr, d₁, h.r6, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.Arm.Derive.nextLane]
  refine wp_ldloc hp i₃ (d := Impl.Argon2.Arm.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add (op2_reg _ _) fun s₅ u₅ => wp_sub (op2_imm (by decide)) fun s₆ u₆ =>
      wp_add (op2_imm (by decide)) fun s₇ u₇ => ?_
  obtain i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine wp_ldarg hp i₇ (i := 7) (by decide) fun s₈ u₈ => ?_
  obtain i₈ := i₇.upd u₈ (by decide)
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain r5₈ : s₈.gpr .r5 = BitVec.ofNat 32 (l + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.r5, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₈.step f.sp (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₈])
  · rw [f.mem, m₈, b₃]
  · rw [f.gpr, r5₈]
  · rw [f.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃,
      u₂.gpr, d₁, h.r6, p₃.stride, r6_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₈]
    by_cases k1 : k = l * (prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (prm s₀).laneLen = l * (prm s₀).laneLen + 0 from rfl, w₁]
      exact (initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega_arith), h.cells k hk, initCell_old _ _ k0 k1]
  · rw [MdStream.Arm.eval_ne, z, u₈.gpr, r5₈, show arg s₀ 7 = BitVec.ofNat 32 (lanesN s₀) by simp,
      ofNat_sub_beq (by omega_arith) (by omega_arith)]

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  refine (clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [memR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => lw_keep hp f₁ fsub (prm_offs d hd).1
  · rw [bytes_keep f₁ (fun r hr => ?_) (by omega_arith), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj' hp (R := memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧
      bytesAt s.mem (State.addr (E s₀)) 64 = h0 ∧ ∀ i < blocksN s₀ * 1024,
        s.mem (memB s₀ + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [ld .r6 (Impl.Argon2.Arm.Derive.argOff 13), .mov .r5 (.imm 0)]) s (LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun s₃ u₃ =>
    WP.block_nil ?_
  obtain i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [initCell_zero, m₃]
    refine blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega_arith)

theorem memoryInit_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.memoryInit s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      Represents t.mem (memB s₀) (prm s₀).blocks (Spec.Argon2.initMemory (prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.Arm.Derive.memoryInit
  refine WP.seq ((clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ LI s₀ h0 l t) ?_
    (lanesN s₀) s₃ ⟨0, by omega_arith, by omega_arith, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 = lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], hu.inv, hu.pr, ?_⟩
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    obtain hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, initCell, done]
    have : k / (prm s₀).laneLen < lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]
  · refine .inr ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], lanesN s₀ - (l + 1), by omega_arith, l + 1, rfl, by omega_arith, hu⟩

end

end VG.Proof.Argon2.Arm.Derive

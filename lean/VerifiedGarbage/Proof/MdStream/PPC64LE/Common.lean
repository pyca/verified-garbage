module

public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.MdStream.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha256.Stream
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming Merkle–Damgård hash functions on PPC64LE: common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Shape`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), saving and restoring the
caller's registers, and weakest-precondition rules for the instruction forms
used. The same structure as on AArch64 (`VG.Proof.MdStream.AArch64`).
-/

@[expose] public section

namespace VG.Proof.MdStream.PPC64LE

open VG VG.PPC64LE VG.Impl.MdStream.PPC64LE
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  N : 0 < P.N ∧ P.N ≤ 64
  so : P.so % 8 = 0 ∧ P.so ≤ 1024
  B : P.B = 64 ∨ P.B = 128
  L : 0 < P.L ∧ P.L ≤ 16

theorem Dims.pos {P : Params} (hd : Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

/-- The shift count of the block size. -/
theorem Dims.log {P : Params} (hd : Dims P) :
    1 ≤ Impl.MdStream.PPC64LE.lg P ∧ Impl.MdStream.PPC64LE.lg P ≤ 7 ∧
      2 ^ Impl.MdStream.PPC64LE.lg P = P.B := by
  unfold Impl.MdStream.PPC64LE.lg
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- `x >>> log₂ B`. -/
theorem Dims.shr {P : Params} (hd : Dims P) {a : Nat} (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> Impl.MdStream.PPC64LE.lg P = BitVec.ofNat 64 (a / P.B) := by
  rw [ofNat_shr h, hd.log.2.2]

/-- `x <<< log₂ B`. -/
theorem Dims.shl {P : Params} (hd : Dims P) {a : Nat} (h : P.B * a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< Impl.MdStream.PPC64LE.lg P = BitVec.ofNat 64 (P.B * a) := by
  rw [ofNat_shl (by rw [hd.log.2.2]; exact h), hd.log.2.2]

/-- `x &&& (B - 1)`. -/
theorem Dims.and {P : Params} (hd : Dims P) (x : BitVec 64) :
    x &&& BitVec.ofNat 64 (P.B - 1) = BitVec.ofNat 64 (x.toNat % P.B) := by
  have := and_mask (n := Impl.MdStream.PPC64LE.lg P) (by have := hd.log; omega) x
  rwa [hd.log.2.2] at this

/-- The block size fits `li`'s immediate. -/
theorem Dims.B_lt {P : Params} (hd : Dims P) : P.B < 2 ^ 15 := by
  rcases hd.B with h | h <;> omega

theorem Dims.mod {P : Params} (hd : Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

/-! ## Saving the caller's registers -/

section
variable (P : Params)

/-- The caller's nonvolatile registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The memory after saving `r26`–`r31` (values `g`) at `b + so …`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 P.so) (g .r26)).writeW (b + BitVec.ofNat 64 (P.so + 8)) (g .r27)).writeW
    (b + BitVec.ofNat 64 (P.so + 16)) (g .r28)).writeW (b + BitVec.ofNat 64 (P.so + 24)) (g .r29)).writeW
    (b + BitVec.ofNat 64 (P.so + 32)) (g .r30)).writeW (b + BitVec.ofNat 64 (P.so + 40)) (g .r31)

theorem save_eq (b : Reg) : save P b = [.store .d .r26 b P.so, .store .d .r27 b (P.so + 8),
    .store .d .r28 b (P.so + 16), .store .d .r29 b (P.so + 24), .store .d .r30 b (P.so + 32),
    .store .d .r31 b (P.so + 40)] := rfl

theorem restore_eq : restore P = [.load .d .r26 .r27 P.so, .load .d .r28 .r27 (P.so + 16),
    .load .d .r29 .r27 (P.so + 24), .load .d .r30 .r27 (P.so + 32), .load .d .r31 .r27 (P.so + 40),
    .load .d .r27 .r27 (P.so + 8)] := rfl

end

section
variable {P : Params}

theorem saveMem_saved (hd : Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Saved P b g (saveMem P m b g) := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saveMem, Mem.readW_writeW_self64,
    readW_writeW_save_so this.2, readW_writeW_save_so_l this.2]

theorem saveMem_frame (hd : Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, P.so + 48⟩] m (saveMem P m b g) := by
  have := hd.so
  have c : ∀ d : Nat, d + 8 ≤ P.so + 48 → (⟨b, P.so + 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => contains_offset hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
compression function uses. -/
theorem saved_offset (hd : Dims P) {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
  have := hd.so
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- `std`'s displacement: a multiple of 4 below 2¹⁵. -/
theorem so_ds (hd : Dims P) {d : Nat} (hd₁ : d ≤ 40) (hd₂ : d % 8 = 0) :
    P.so + d < 2 ^ 15 ∧ (P.so + d) % 4 = 0 := by
  have := hd.so; omega

/-- Saving `r26`–`r31` with the scratch pointer in `b`. -/
theorem save_ok (hd : Dims P) {b : Reg} (hb : b ≠ .r0) {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem P s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save P b ++ rest)) s Q := by
  have := hd.so
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_std (by omega) rfl (hin _ (by omega) (by omega)) (fun s₁ g₁ => ?_) hb
  refine wp_std (by omega) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin _ (by omega) (by omega))
    (fun s₂ g₂ => ?_) hb
  refine wp_std (by omega) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₃ g₃ => ?_) hb
  refine wp_std (by omega) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₄ g₄ => ?_) hb
  refine wp_std (by omega) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₅ g₅ => ?_) hb
  refine wp_std (by omega) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) (fun s₆ g₆ => ?_) hb
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

/-- Restoring `r26`–`r31` from the save area at `scr`. -/
theorem restore_ok (hd : Dims P) {s : State} {scr : Addr} (h27 : s.gpr .r27 = scr)
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved P scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved P, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ (saved P).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (restore P)) s Q := by
  have := hd.so
  have v : ∀ r d, (r, d) ∈ saved P → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  rw [restore_eq]
  refine wp_ld (by omega) (by rw [h27]) (hin _ (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ld (by omega) (by rw [u₁.other _ (by decide), h27])
    (by rw [u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ld (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h27])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ld (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h27])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin _ (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .r26 _ (by simp [saved])]
    · rw [u₆.gpr, m5, v .r27 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .r28 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .r29 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .r30 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .r31 _ (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

end

/-- The nonvolatile registers our own code never writes: only the
compression function may, and it restores them. -/
def untouched : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25]

theorem untouched_pres : ∀ r ∈ untouched, r ∈ preserved := by decide

/-- The nonvolatile registers are the caller's again once `restore` has run
and `untouched` hold their values. -/
theorem preserved_of {P : Params} {s₀ s' : State} (hsv : ∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ [Reg.r26, .r27, .r28, .r29, .r30, .r31] := by decide
  rcases key r hr with h | h
  · exact hu r h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.r26, P.so) (by simp [saved])
    · exact hsv (.r27, P.so + 8) (by simp [saved])
    · exact hsv (.r28, P.so + 16) (by simp [saved])
    · exact hsv (.r29, P.so + 24) (by simp [saved])
    · exact hsv (.r30, P.so + 32) (by simp [saved])
    · exact hsv (.r31, P.so + 40) (by simp [saved])

/-! ## Storing a word in the buffer -/

/-- `storeWord` stores `r8` at `r26 + r30 + N`, writing only `r11`. -/
theorem storeWord_ok {P : Params} (hN : P.N < 2 ^ 15) {rest : List Instr} {s : State} {Q : State → Prop}
    {a : Addr} (ha : s.gpr .r26 + s.gpr .r30 + BitVec.ofNat 64 P.N = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW a (s.gpr .r8) → WP isa (.block rest) s' Q) :
    WP isa (.block (storeWord P ++ rest)) s Q := by
  unfold storeWord
  split
  · rename_i h4
    simp only [List.cons_append, List.nil_append]
    refine wp_add fun s₁ u₁ => wp_std (a := a) ⟨hN, h4⟩ (by rw [u₁.gpr]; exact ha) (by rw [u₁.wr]; exact hout)
      fun s₂ g₂ => k s₂ (fun r hr => by rw [g₂.gpr, u₁.other r hr]) (by rw [g₂.rd, u₁.rd])
        (by rw [g₂.wr, u₁.wr]) (by rw [g₂.sp, u₁.sp]) (by rw [g₂.mem, u₁.mem, u₁.other _ (by decide)])
  · simp only [List.cons_append, List.nil_append]
    refine wp_add fun s₁ u₁ => wp_addi hN fun s₂ u₂ => wp_std (a := a) ⟨by decide, by decide⟩
      (by rw [u₂.gpr, u₁.gpr]; exact (BitVec.add_zero _).trans ha) (by rw [u₂.wr, u₁.wr]; exact hout)
      fun s₃ g₃ => k s₃ (fun r hr => by rw [g₃.gpr, u₂.other r hr, u₁.other r hr])
        (by rw [g₃.rd, u₂.rd, u₁.rd]) (by rw [g₃.wr, u₂.wr, u₁.wr]) (by rw [g₃.sp, u₂.sp, u₁.sp])
        (by rw [g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.other _ (by decide)])

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`r3` with the `r5` blocks at `r4`, with scratch space `r6` (`so` bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, P.N⟩
    let blocks : Region := ⟨s.gpr .r4, P.B * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, P.so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .r3) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .r3)) s.mem (s.gpr .r4) (s.gpr .r5).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- The contract of `update`: if the state at `r3` represents a message of
`r4` bytes (modulo 2⁶⁴) from any initial hash value, it then represents that
message followed by the `r6` bytes at `r5`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, P.N + P.B⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, P.so + 48⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .r3) (m ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The contract of a `finalize` writing the first `D` bytes of the final
hash value (all `N` of them, or a truncated digest, such as SHA-384's) to
`r5`, if the state at `r3` represents a message of `r4` bytes. -/
def finKD (D : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, P.N + P.B⟩
    let out : Region := ⟨s.gpr .r5, D⟩
    let scratch : Region := ⟨s.gpr .r6, P.so + 48⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .r3) m → H.lenOk m.length →
    s.gpr .r4 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .r5) D = (H.hash iv m).take D
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `r29` at `r26 + N + B - L`, writing only `r8` and `r11`, and
`P.out` writes the first `D` bytes of the digest of the hash value at `r26`
to `r28`, writing only `r8` and `r11`. -/
structure ShapeD {P : Params} (H : Md P.B P.N P.L) (D : Nat) : Prop where
  le : D ≤ P.N
  len : ∀ s : State, InRegions s.wr (s.gpr .r26 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .r26 + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .r29))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .r26) P.N → InRegions s.wr (s.gpr .r28) D →
    Region.Disjoint ⟨s.gpr .r26, P.N⟩ ⟨s.gpr .r28, D⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .r28) ((H.digest (H.stateAt s.mem (s.gpr .r26))).take D)

/-- What `compressAt` needs of the compression function it calls: that it is
correct, and pushes no frames. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  noFrames : code.noFrames = true

/-- `CalleeOk` does not depend on the length field or the digest. -/
theorem CalleeOk.withOut {P : Params} {H : Md P.B P.N P.L} {code : Prog isa} (hf : CalleeOk H code)
    (o : List Instr) : CalleeOk (P := { P with out := o }) H code :=
  ⟨hf.verified, hf.noFrames⟩

/-! ## The compression function -/

/-- `n` sets `r5` to `v`, given that only `r3` changed since the state `s`. -/
def SetsN (n : Instr) (s : State) (v : BitVec 64) : Prop :=
  ∀ (s₁ : State) (is : List Instr) (Q : State → Prop), (∀ r, r ≠ .r3 → s₁.gpr r = s.gpr r) →
    (∀ s', Upd s₁ s' .r5 v → WP isa (.block is) s' Q) → WP isa (.block (n :: is)) s₁ Q

theorem setsN_one (s : State) : SetsN (.li .r5 1) s (BitVec.ofNat 64 1) :=
  fun _ _ _ _ k => wp_li (by decide) k

theorem setsN_r9 (s : State) : SetsN (mov .r5 .r9) s (s.gpr .r9) :=
  fun _ _ _ he k => wp_mov fun s' u => k s' (by rwa [he _ (by decide)] at u)

/-- Compressing the `k` blocks at `r4` (their number set in `r5` by `n`) into
the hash value at `r26`, with scratch space at `r27`: the nonvolatile
registers are kept. -/
theorem compressWith_ok {P : Params} {H : Md P.B P.N P.L} {n : Instr} {s : State} {v : BitVec 64}
    (hn : SetsN n s v) {k : Nat} (hk : v.toNat = k) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {st scr src : Addr}
    (h26 : s.gpr .r26 = st) (h27 : s.gpr .r27 = scr) (h4 : s.gpr .r4 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B * k⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B * k⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B * k⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compressBlocks (H.stateAt s.mem st) s.mem src k → Q s') :
    WP isa (compressWith n name code) s Q := by
  unfold compressWith
  refine WP.seq (wp_mov fun s₁ u₁ => hn s₁ _ _ u₁.other fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e3 : s₃.gpr .r3 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h26]
  have e4 : s₃.gpr .r4 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h4]
  have e5 : s₃.gpr .r5 = v := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e6 : s₃.gpr .r6 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h27]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r3 ∧ r ≠ .r5 ∧ r ≠ .r6 := by
      revert r; decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c3 : s₃.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans e3
  have c4 : s₃.callEntry.gpr .r4 = src := (State.callEntry_gpr _ (by decide)).trans e4
  have c5 : s₃.callEntry.gpr .r5 = v := (State.callEntry_gpr _ (by decide)).trans e5
  have c6 : s₃.callEntry.gpr .r6 = scr := (State.callEntry_gpr _ (by decide)).trans e6
  refine WP.call (k := compressK H) hf.verified
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5, c6, hk]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf' hcs _ hpost
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, hk, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr => (hcs r hr).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf') hpost

/-- Compressing the block at `r4` into the hash value at `r26`, with scratch
space at `r27`: the nonvolatile registers are kept. -/
theorem compressAt_ok {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s : State} {st scr src : Addr}
    (h26 : s.gpr .r26 = st) (h27 : s.gpr .r27 = scr) (h4 : s.gpr .r4 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q :=
  compressWith_ok (k := 1) (setsN_one s) (by rfl) hf h26 h27 h4 d₁ (by rwa [Nat.mul_one]) (by rwa [Nat.mul_one])
    (by rwa [Nat.mul_one]) hw
    fun s' hrd hwr hcs hsp hf' hs => hQ s' hrd hwr hcs hsp hf' (by rw [hs, Md.compressBlocks_one])

end VG.Proof.MdStream.PPC64LE

module

public import VerifiedGarbage.Impl.MdStream.RISCV64
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Streaming Merkle–Damgård hash functions on RISC-V: common lemmas

Untrusted: everything here is checked by Lean. The contracts the generic
proofs are written against, what they need of a hash function's length
field and digest (`ShapeD`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), and saving and
restoring our caller's registers in the frame. The structure of SHA-256's
RISC-V proof (`Proof/Sha256/RISCV64/Stream/Common.lean`), and of the
generic PPC64LE proof (`Proof/MdStream/PPC64LE/Common.lean`).
-/

@[expose] public section

namespace VG.Proof.MdStream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.MdStream.RISCV64
open VG.Spec.Sha256 (bytesAt)
open VG.WriteBytes (writeBytes)

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {N : Nat} (H : Md 64 N 8)

/-- The contract of the compression function: updates the hash value at
`a0` with the `a2` blocks at `a1`, with scratch space `a3` (80 bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, N⟩
    let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 80⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .a0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- The contract of `update`: if the state at `a0` represents a message of
`a1` bytes (modulo 2⁶⁴) from any initial hash value, it then represents that
message followed by the `a3` bytes at `a2`. Its frame is the 144 bytes below
the stack pointer. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, N + 64⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- The contract of a `finalize` writing the first `D` bytes of the final
hash value to `a2`, if the state at `a0` represents a message of `a1`
bytes. Its frame is the 144 bytes below the stack pointer. -/
def finKD (D : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, N + 64⟩
    let out : Region := ⟨s.gpr .a2, D⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .a0) m → H.lenOk m.length →
    s.gpr .a1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .a2) D = (H.hash iv m).take D
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end

/-! ## What each hash function's own code must do -/

/-- The sizes the generic proofs support: the buffer's bytes are within
reach of a 12-bit offset. -/
def Dims (P : Params) : Prop := P.N ≤ 64

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `s4` at `s1 + N + 56`, writing only `t1` and `t3`, and `P.out`
writes the first `D` bytes of the digest of the hash value at `s1` to `s3`,
writing only `t1` and `t2`. -/
structure ShapeD {P : Params} (H : Md 64 P.N 8) (D : Nat) : Prop where
  le : D ≤ P.N
  len : ∀ s : State, InRegions s.wr (s.gpr .s1 + BitVec.ofNat 64 (P.N + 56)) 8 →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s1 + BitVec.ofNat 64 (P.N + 56)) (H.lenOf (s.gpr .s4))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .s1) P.N → InRegions s.wr (s.gpr .s3) D →
    Region.Disjoint ⟨s.gpr .s1, P.N⟩ ⟨s.gpr .s3, D⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((H.digest (H.stateAt s.mem (s.gpr .s1))).take D)

/-- What `compressAt` needs of the compression function it calls: that it is
correct, and pushes no frames. -/
structure CalleeOk {N : Nat} (H : Md 64 N 8) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  noFrames : code.noFrames = true

/-! ## The called compression function -/

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- Compressing the block at `a1` into the hash value at `s1`, with scratch
space at `s2`: the callee-saved registers are kept. -/
theorem compressAt_ok {N : Nat} {H : Md 64 N 8} {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s : State} {st scr src : Addr}
    (h1 : s.gpr .s1 = st) (h2 : s.gpr .s2 = scr) (ha1 : s.gpr .a1 = src)
    (d₁ : Region.Disjoint ⟨st, N⟩ ⟨scr, 80⟩) (d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, N⟩)
    (d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 80⟩)
    (hc : Covers [⟨src, 64⟩, ⟨st, N⟩, ⟨scr, 80⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, N⟩, ⟨scr, 80⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, 80⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q := by
  unfold compressAt
  refine WP.seq (wp_mv fun s₁ u₁ => wp_li (imm := 1) (by decide) fun s₂ u₂ =>
    wp_mv fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .a0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
  have e1 : s₃.gpr .a1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha1]
  have e2 : s₃.gpr .a2 = BitVec.ofNat 64 1 := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .a3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h2]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .a0 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
      revert r; decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .a1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .a2 = BitVec.ofNat 64 1 :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .a3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := compressK H) hf.verified
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, N⟩, ⟨scr, 80⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf' hcs _ hpost
    simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, Md.compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr => (hcs r hr).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf') hpost

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h]
  rw [e, BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## Saving the caller's registers -/

/-- The memory after saving `ra` and `s1`–`s6` (values `g`) at `b + 80 … b + 128`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((((m.writeW (b + BitVec.ofNat 64 80) (g .ra)).writeW (b + BitVec.ofNat 64 88) (g .s1)).writeW
    (b + BitVec.ofNat 64 96) (g .s2)).writeW (b + BitVec.ofNat 64 104) (g .s3)).writeW
    (b + BitVec.ofNat 64 112) (g .s4)).writeW (b + BitVec.ofNat 64 120) (g .s5)).writeW
    (b + BitVec.ofNat 64 128) (g .s6)

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 =
      m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h (by omega) (by omega)) (by decide)

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ saved, (saveMem m b g).readW (b + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [saveMem, Mem.readW_writeW_self64, readW_writeW_save, Nat.reduceAdd, Nat.reducePow,
    Nat.reduceLT, Nat.reduceLeDiff, true_or]

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, frameBytes⟩] m (saveMem m b g) := by
  have c : ∀ d : Nat, d + 8 ≤ 144 → (⟨b, frameBytes⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base b (by simp only [frameBytes]; omega) (by omega)
  simp only [saveMem]
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 80 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 88 (by omega))).writeW (List.mem_singleton_self _) _
    (c 96 (by omega))).writeW (List.mem_singleton_self _) _ (c 104 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 112 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega)) |>.writeW (List.mem_singleton_self _) _ (c 128 (by omega))

theorem save_eq : save = [.addSp .t0 0, .store .d .ra .t0 80, .store .d .s1 .t0 88,
    .store .d .s2 .t0 96, .store .d .s3 .t0 104, .store .d .s4 .t0 112, .store .d .s5 .t0 120,
    .store .d .s6 .t0 128] := rfl

/-- An 8-byte aligned offset of a 16-byte aligned frame. -/
theorem frame_al {b : Addr} (hb : b.toNat % 16 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 32) :
    (b + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]
  have := b.isLt
  omega

/-- Saving `ra` and `s1`–`s6` in the frame at the stack pointer, whose
address is left in `t0`. -/
theorem save_ok {rest : List Instr} {s : State} {Q : State → Prop} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, 80 ≤ d → d + 8 ≤ 144 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr .t0 = s.sp → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → s'.mem = saveMem s.mem s.sp s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₀ u₀ => ?_
  have g0 : s₀.gpr .t0 = s.sp := by rw [u₀.gpr]; exact BitVec.add_zero _
  have st : ∀ d, d % 8 = 0 → 80 ≤ d → d + 8 ≤ 144 → ∀ s' : State, s'.gpr .t0 = s.sp → s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s'.wr (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₁ h₂ s' h₀ hw => ⟨by rw [h₀], frame_al hal hd (by omega), by rw [hw]; exact hin d h₁ h₂⟩
  have w0 : s₀.wr = s.wr := u₀.wr
  obtain ⟨a1, l1, i1⟩ := st 80 (by decide) (by omega) (by omega) s₀ g0 w0
  refine wp_sd (by decide) a1 l1 i1 fun s₁ g₁ => ?_
  have t1 : s₁.gpr .t0 = s.sp := by rw [g₁.gpr, g0]
  obtain ⟨a2, l2, i2⟩ := st 88 (by decide) (by omega) (by omega) s₁ t1 (by rw [g₁.wr, w0])
  refine wp_sd (by decide) a2 l2 i2 fun s₂ g₂ => ?_
  have t2 : s₂.gpr .t0 = s.sp := by rw [g₂.gpr, t1]
  obtain ⟨a3, l3, i3⟩ := st 96 (by decide) (by omega) (by omega) s₂ t2 (by rw [g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a3 l3 i3 fun s₃ g₃ => ?_
  have t3 : s₃.gpr .t0 = s.sp := by rw [g₃.gpr, t2]
  obtain ⟨a4, l4, i4⟩ := st 104 (by decide) (by omega) (by omega) s₃ t3
    (by rw [g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a4 l4 i4 fun s₄ g₄ => ?_
  have t4 : s₄.gpr .t0 = s.sp := by rw [g₄.gpr, t3]
  obtain ⟨a5, l5, i5⟩ := st 112 (by decide) (by omega) (by omega) s₄ t4
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a5 l5 i5 fun s₅ g₅ => ?_
  have t5 : s₅.gpr .t0 = s.sp := by rw [g₅.gpr, t4]
  obtain ⟨a6, l6, i6⟩ := st 120 (by decide) (by omega) (by omega) s₅ t5
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a6 l6 i6 fun s₆ g₆ => ?_
  have t6 : s₆.gpr .t0 = s.sp := by rw [g₆.gpr, t5]
  obtain ⟨a7, l7, i7⟩ := st 128 (by decide) (by omega) (by omega) s₆ t6
    (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
  refine wp_sd (by decide) a7 l7 i7 fun s₇ g₇ => ?_
  have gg : s₇.gpr = s₀.gpr := by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  refine k s₇ (by rw [gg, g0]) (fun r hr => by rw [gg, u₀.other r hr])
    (by rw [g₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, u₀.rd])
    (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, w0])
    (by rw [g₇.sp, g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp, u₀.sp]) ?_
  have o : ∀ r, r ≠ .t0 → s₀.gpr r = s.gpr r := fun r hr => u₀.other r hr
  rw [g₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem, u₀.mem]
  simp only [saveMem, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, o _ (show Reg.ra ≠ .t0 by decide),
    o _ (show Reg.s1 ≠ .t0 by decide), o _ (show Reg.s2 ≠ .t0 by decide),
    o _ (show Reg.s3 ≠ .t0 by decide), o _ (show Reg.s4 ≠ .t0 by decide),
    o _ (show Reg.s5 ≠ .t0 by decide), o _ (show Reg.s6 ≠ .t0 by decide)]

theorem restore_eq : restore = [.load .d .ra .s2 80, .load .d .s1 .s2 88, .load .d .s3 .s2 104,
    .load .d .s4 .s2 112, .load .d .s5 .s2 120, .load .d .s6 .s2 128, .load .d .s2 .s2 96] := rfl

/-- Restoring `ra` and `s1`–`s6` from the frame at `scr` (in `s2`). -/
theorem restore_ok {s : State} {scr : Addr} (h2 : s.gpr .s2 = scr) (hal : scr.toNat % 16 = 0)
    (hin : ∀ d, 80 ≤ d → d + 8 ≤ 144 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : ∀ p ∈ saved, s.mem.readW (scr + BitVec.ofNat 64 p.2) 64 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  have al : ∀ d, d % 8 = 0 → d < 2 ^ 32 → (scr + BitVec.ofNat 64 d).toNat % 8 = 0 :=
    fun d hd hd' => frame_al hal hd hd'
  rw [restore_eq]
  refine wp_ld (by decide) (by rw [h2]) (al 80 (by decide) (by decide)) (hin 80 (by omega) (by omega))
    fun s₁ u₁ => ?_
  refine wp_ld (by decide) (by rw [u₁.other _ (by decide), h2]) (al 88 (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact hin 88 (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ld (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 104 (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 104 (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 112 (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 112 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ld (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h2])
    (al 120 (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 120 (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ld (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 128 (by decide) (by decide))
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 128 (by omega) (by omega))
    fun s₆ u₆ => ?_
  refine wp_ld (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h2])
    (al 96 (by decide) (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 96 (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ?_
  have m6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₇ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₇.mem, m6])
    (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        v .ra 80 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, v .s1 88 (by simp [saved])]
    · rw [u₇.gpr, m6, v .s2 96 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, v .s3 104 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem,
        u₂.mem, u₁.mem, v .s4 112 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
        v .s5 120 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
        v .s6 128 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other _ h3, u₆.other _ h7, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h2',
      u₁.other _ h1]

/-! ## Registers -/

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers we do not save: the compression function
preserves them, and no other instruction writes them. -/
def nvRegs : List Reg := [.s0, .s7, .s8, .s9, .s10, .s11]

theorem nv_pres : ∀ r ∈ nvRegs, r ∈ preserved := by decide

/-- `nvRegs.all fun r => o != some r` as one `match`. -/
def keepsN : Option Reg → Bool
  | some .s0 | some .s7 | some .s8 | some .s9 | some .s10 | some .s11 => false
  | _ => true

theorem keepsN_all (l : List Instr) (h : (l.all fun i => keepsN (dstOf i)) = true) :
    ∀ r ∈ nvRegs, ∀ i ∈ l, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp h i hi
  rw [e] at h
  simp only [nvRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepsN] at h

/-! ## The frame -/

/-- The frame's region in the state its body starts in. -/
theorem allocd_wr (n : Nat) (s : State) :
    (allocd n s).wr = ⟨s.sp - BitVec.ofNat 64 n, n⟩ :: s.wr := rfl

theorem allocd_sp (n : Nat) (s : State) : (allocd n s).sp = s.sp - BitVec.ofNat 64 n := rfl

theorem allocd_gpr (n : Nat) (s : State) : (allocd n s).gpr = s.gpr := rfl
theorem allocd_mem (n : Nat) (s : State) : (allocd n s).mem = s.mem := rfl
theorem allocd_rd (n : Nat) (s : State) : (allocd n s).rd = s.rd := rfl

/-- The frame is 16-byte aligned. -/
theorem frame_aligned {sp : Addr} (h : sp.toNat % 16 = 0) (h' : 144 ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 144).toNat % 16 = 0 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

end VG.Proof.MdStream.RISCV64

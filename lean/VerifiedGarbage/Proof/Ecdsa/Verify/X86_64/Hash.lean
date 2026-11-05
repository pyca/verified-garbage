module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ECDSA verification of the hash function's output on x86-64: the conversion

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Ecdsa/Verify/RISCV64/Hash.lean`): `convert_mem`: `convert len wide`
writes `fixedDigest len wide` of the hash at `rsi` (`rdx` bytes) to the first
`len` bytes of the buffer at `r9`, changing only the buffer's 80 bytes in
memory.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64.VerifyHash

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, arithFlags, State.setFlags, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_shl {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d <<< n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shl d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (64 - n)))
    (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none)
    (some ((s.gpr d <<< n) == 0)) (some (s.gpr d <<< n).msb)).setReg d (s.gpr d <<< n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

end

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega

theorem ea_at (s : State) (r : Reg) (d : Nat) : s.ea (at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp [State.ea, at_]

theorem ea_base (s : State) (r : Reg) : s.ea { base := r } = s.gpr r := by
  simp [State.ea]

/-! ## The conversion -/

variable {len : Nat} {s : State}

/-- What `convert` needs of its state: the hash's bytes readable, the
buffer's 80 bytes writable and apart from them, neither wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  rd : ∀ i < (s.gpr .rdx).toNat, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) 1
  wr : ∀ i < 80, InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .r9, 80⟩ : Region).Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  fitB : (s.gpr .r9).toNat + 80 ≤ 2 ^ 64
  fitD : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- The hash. -/
abbrev hashOf (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat

/-- The registers `convert` keeps: all but `r10`, `r11`, `rsi` and `rdx`. -/
def Kp (s t : State) : Prop := ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rsi → r ≠ .rdx → t.gpr r = s.gpr r

/-- The buffer's contents and what `convert` changes in memory and registers. -/
structure MPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .r9 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .r9, 80⟩] s.mem t.mem
  keep : Kp s t
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem hash_byte {i : Nat} (hi : i < (s.gpr .rdx).toNat) :
    (hashOf s).getD i 0 = s.mem (s.gpr .rsi + BitVec.ofNat 64 i) :=
  bytesAt_getD _ _ _ _ hi

/-- A byte of the buffer is not one of the hash's. -/
theorem buf_not_hash (hp : CPre len s) {x : Addr} (hx : (⟨s.gpr .r9, 80⟩ : Region).Contains x 1) {i : Nat}
    (hi : i < (s.gpr .rdx).toNat) : x ≠ s.gpr .rsi + BitVec.ofNat 64 i := by
  rintro rfl
  exact hp.sep _ hx (Offset.contains_base _ (by omega) (by omega))

/-- After `k` bytes of a copy from `src + i` to `dst + i`. -/
structure LInv (s : State) (src dst : Addr) (k : Nat) (u : State) : Prop where
  copied : ∀ j < k, u.mem (dst + BitVec.ofNat 64 j) = s.mem (src + BitVec.ofNat 64 j)
  frame : Frame [⟨dst, k⟩] s.mem u.mem
  rsi : u.gpr .rsi = s.gpr .rsi
  r9 : u.gpr .r9 = s.gpr .r9
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  keep : ∀ r, r ≠ .r10 → u.gpr r = s.gpr r

/-- A hash of at least `len` bytes: its leftmost `len`. -/
theorem long_ok (wide : Bool) {s₁ : State} (hp : CPre len s) (hg : s₁.gpr = s.gpr) (hm : s₁.mem = s.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hl : len ≤ (s.gpr .rdx).toNat) :
    WP isa (.block (copyLong len)) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  have hD := hp.fitD
  refine WP.mono (wp_range_flatMap (M := isa) (LInv s (s.gpr .rsi) (s.gpr .r9)) (fun k u hk h => ?_) len
    (Nat.le_refl _) s₁ ⟨fun _ h => absurd h (by omega), by rw [hm]; exact Frame.refl _ _, by rw [hg], by rw [hg],
      hrd, hwr, fun r _ => by rw [hg]⟩) fun t ht => ⟨fun i hi => ?_, ?_,
        fun r h1 _ _ _ => ht.keep r h1, ht.rd, ht.wr⟩
  · refine wp_movzx8 (a := s.gpr .rsi + BitVec.ofNat 64 k) (by rw [ea_at, h.rsi])
      (by rw [h.rd, h.wr]; exact hp.rd k (by omega)) fun u₁ g₁ => ?_
    refine wp_store8 (a := s.gpr .r9 + BitVec.ofNat 64 k) (by rw [ea_at, g₁.other _ (by decide), h.r9])
      (by rw [g₁.wr, h.wr]; exact hp.wr k (by omega)) fun u₂ e₂ m₂ rd₂ wr₂ => WP.block_nil ?_
    have hv : (u₁.gpr .r10).setWidth 8 = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) := by
      rw [g₁.gpr, h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact buf_not_hash hp (contains_sub hc (by omega)) (i := k) (by omega) rfl]
      simp
    have hm₂ : u₂.mem = u.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 k) (s.mem (s.gpr .rsi + BitVec.ofNat 64 k)) := by
      rw [m₂, hv, g₁.mem]
    refine ⟨fun j hj => ?_, ?_, by rw [e₂, g₁.other _ (by decide), h.rsi], by rw [e₂, g₁.other _ (by decide), h.r9],
      by rw [rd₂, g₁.rd, h.rd], by rw [wr₂, g₁.wr, h.wr], fun r hr => by rw [e₂, g₁.other _ hr, h.keep r hr]⟩
    · rw [hm₂]
      by_cases e : j = k
      · subst e; rw [byte_writeW_eq]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e]; exact h.copied j (by omega)
    · rw [hm₂]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_prefix _ (by omega)⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [ht.copied i hi, ← hash_byte (by omega), fixedDigest, ite_eq_left (by rw [length_bytesAt]; exact hl),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  · exact ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_prefix _ (by omega)⟩

/-- The buffer holds the zeros and the hash (`tz`), in a state with the
entry's buffer pointer and permissions. -/
structure ZInv (len : Nat) (s u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .r9 + BitVec.ofNat 64 j) = tz len (hashOf s) j
  frame : Frame [⟨s.gpr .r9, 80⟩] s.mem u.mem
  r9 : u.gpr .r9 = s.gpr .r9
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  keep : Kp s u

/-- After `k` bytes of the shift. -/
structure SInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .r9 + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j
  frame : Frame [⟨s.gpr .r9, 80⟩] s.mem u.mem
  r9 : u.gpr .r9 = s.gpr .r9
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  keep : Kp s u

theorem shift_ok (hp : CPre len s) (hl : (s.gpr .rdx).toNat < len) {u : State} (hz : ZInv len s u) :
    WP isa (.block (shiftBytes len)) u (MPost len true s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  refine WP.mono (wp_range_flatMap (M := isa) (SInv len s) (fun k u₁ hk h => ?_) len (Nat.le_refl _) u
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hz.mem j hj, hz.frame, hz.r9, hz.rd, hz.wr,
      hz.keep⟩)
    fun t ht => ⟨fun i hi => ?_, ht.frame, ht.keep, ht.rd, ht.wr⟩
  · have hw : ∀ j < 80, InRegions u₁.wr (s.gpr .r9 + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [h.wr]; exact hp.wr j hj
    refine wp_movzx8 (a := s.gpr .r9 + BitVec.ofNat 64 k) (by rw [ea_at, h.r9])
      (inRegions_wr (hw k (by omega))) fun u₂ g₂ => ?_
    refine wp_movzx8 (a := s.gpr .r9 + BitVec.ofNat 64 (k + 1)) (by rw [ea_at, g₂.other _ (by decide), h.r9])
      (by rw [g₂.rd, g₂.wr]; exact inRegions_wr (hw (k + 1) (by omega))) fun u₃ g₃ => ?_
    refine wp_shl (by decide) fun u₄ g₄ => wp_shr (by decide) fun u₅ g₅ => wp_add fun u₆ g₆ => ?_
    refine wp_store8 (a := s.gpr .r9 + BitVec.ofNat 64 k)
      (by rw [ea_at, g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide),
        g₃.other _ (by decide), g₂.other _ (by decide), h.r9])
      (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr]; exact hw k (by omega)) fun u₇ e₇ m₇ rd₇ wr₇ => WP.block_nil ?_
    have hv : (u₆.gpr .r10).setWidth 8 = sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1)) := by
      rw [g₆.gpr, g₅.other _ (by decide), g₅.gpr, g₄.gpr, g₄.other _ (by decide), g₃.gpr,
        g₃.other _ (by decide), g₂.gpr, g₂.mem, h.mem k (by omega), h.mem (k + 1) (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
      exact shift_byte _ _
    have hm : u₇.mem = u₁.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 k)
        (sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1))) := by
      rw [m₇, hv, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem]
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
    · rw [hm]
      by_cases e : j = k
      · subst e; rw [byte_writeW_eq, ite_eq_left (by omega)]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.mem j hj]
        by_cases hjk : j < k
        · rw [ite_eq_left hjk, ite_eq_left (by omega)]
        · rw [ite_eq_right hjk, ite_eq_right (by omega)]
    · rw [hm]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [e₇, g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide),
        g₃.other _ (by decide), g₂.other _ (by decide), h.r9]
    · rw [rd₇, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, h.rd]
    · rw [wr₇, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, h.wr]
    · rw [e₇, g₆.other _ h1, g₅.other _ h2, g₄.other _ h1, g₃.other _ h2, g₂.other _ h1, h.keep r h1 h2 h3 h4]
  · rw [ht.mem i (by omega), ite_eq_left hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]
    rfl

theorem tail_ok (wide : Bool) (hp : CPre len s) (hl : (s.gpr .rdx).toNat < len) {u : State}
    (hz : ZInv len s u) :
    WP isa (.block (if wide then shiftBytes len else [])) u (MPost len wide s) := by
  cases wide with
  | true => exact shift_ok hp hl hz
  | false =>
    refine WP.block_nil ⟨fun i hi => ?_, hz.frame, hz.keep, hz.rd, hz.wr⟩
    rw [hz.mem i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

/-- After `k` of `N` bytes of `copyLoop` from `s₀`. -/
structure CopyInv (N : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k < N
  hsrc : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 k
  hdst : s.gpr .r11 = s₀.gpr .r11 + BitVec.ofNat 64 k
  hcnt : s.gpr .rdx = BitVec.ofNat 64 (N - k)
  copied : ∀ j < k, s.mem (s₀.gpr .r11 + BitVec.ofNat 64 j) = s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 j)
  frame : Frame [⟨s₀.gpr .r11, N⟩] s₀.mem s.mem
  r9 : s.gpr .r9 = s₀.gpr .r9
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : Kp s₀ s

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide

theorem ofNat_beq_zero' {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- `copyLoop` copies `N ≥ 1` bytes between separate buffers. -/
theorem copyLoop_ok (s₀ : State) {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (hc : s₀.gpr .rdx = BitVec.ofNat 64 N)
    (hr : ∀ i < N, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < N, InRegions s₀.wr (s₀.gpr .r11 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s₀.gpr .r11) N (s₀.gpr .rsi) N) :
    WP isa copyLoop s₀ fun t =>
      (∀ i < N, t.mem (s₀.gpr .r11 + BitVec.ofNat 64 i) = s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 i)) ∧
      Frame [⟨s₀.gpr .r11, N⟩] s₀.mem t.mem ∧ t.gpr .r9 = s₀.gpr .r9 ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      Kp s₀ t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = N - k ∧ CopyInv N s₀ k t) ?_ N s₀
    ⟨0, rfl, hN, by simp, by simp, by simp [hc], fun j hj => absurd hj (by omega), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  rintro n t ⟨k, rfl, I⟩
  have hk := I.le
  refine wp_movzx8 (a := s₀.gpr .rsi + BitVec.ofNat 64 k) (by rw [ea_base, I.hsrc])
    (by rw [I.rd, I.wr]; exact hr k hk) fun u₁ g₁ => ?_
  refine wp_store8 (a := s₀.gpr .r11 + BitVec.ofNat 64 k) (by rw [ea_base, g₁.other _ (by decide), I.hdst])
    (by rw [g₁.wr, I.wr]; exact hw k hk) fun u₂ e₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun u₃ g₃ => wp_addi fun u₄ g₄ => wp_subi fun u₅ g₅ hz₅ => WP.block_nil ?_
  have hv : (u₁.gpr .r10).setWidth 8 = s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 k) := by
    rw [g₁.gpr, I.frame _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ hcon (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)]
    simp
  have hm : u₅.mem = t.mem.writeW (s₀.gpr .r11 + BitVec.ofNat 64 k) (s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 k)) := by
    rw [g₅.mem, g₄.mem, g₃.mem, m₂, hv, g₁.mem]
  have hcnt : u₅.gpr .rdx = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [g₅.gpr, g₄.other _ (by decide), g₃.other _ (by decide), e₂, g₁.other _ (by decide), I.hcnt, sx1,
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have hcopied : ∀ j < k + 1, u₅.mem (s₀.gpr .r11 + BitVec.ofNat 64 j) = s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm]
    by_cases e : j = k
    · subst e; rw [byte_writeW_eq]
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e]; exact I.copied j (by omega)
  have hframe : Frame [⟨s₀.gpr .r11, N⟩] s₀.mem u₅.mem := by
    rw [hm]; exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hr9 : u₅.gpr .r9 = s₀.gpr .r9 := by
    rw [g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide), e₂, g₁.other _ (by decide), I.r9]
  have hrd : u₅.rd = s₀.rd := by rw [g₅.rd, g₄.rd, g₃.rd, rd₂, g₁.rd, I.rd]
  have hwr : u₅.wr = s₀.wr := by rw [g₅.wr, g₄.wr, g₃.wr, wr₂, g₁.wr, I.wr]
  have hkp : Kp s₀ u₅ := fun r h1 h2 h3 h4 => by
    rw [g₅.other _ h4, g₄.other _ h2, g₃.other _ h3, e₂, g₁.other _ h1, I.keep r h1 h2 h3 h4]
  have hzf : u₅.zf = some (decide (N - (k + 1) = 0)) := by
    rw [hz₅, g₄.other _ (by decide), g₃.other _ (by decide), e₂, g₁.other _ (by decide), I.hcnt, sx1,
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      show N - k - 1 = N - (k + 1) by omega, ofNat_beq_zero' (by omega)]
  by_cases e : k + 1 = N
  · refine .inl ⟨by simp only [eval, hzf, e, Nat.sub_self, decide_true, Option.map_some, Bool.not_true],
      fun i hi => hcopied i (by omega), hframe, hr9, hrd, hwr, hkp⟩
  · refine .inr ⟨by simp only [eval, hzf, show N - (k + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false], N - (k + 1), by omega, k + 1, rfl, by omega, ?_, ?_, hcnt, hcopied, hframe, hr9, hrd, hwr, hkp⟩
    · rw [g₅.other _ (by decide), g₄.other _ (by decide), g₃.gpr, e₂, g₁.other _ (by decide), I.hsrc, sx1,
        show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]
    · rw [g₅.other _ (by decide), g₄.gpr, g₃.other _ (by decide), e₂, g₁.other _ (by decide), I.hdst, sx1,
        show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]

/-- After `k` of the zero bytes. -/
structure ZsInv (s : State) (k : Nat) (u : State) : Prop where
  zero : ∀ j < k, u.mem (s.gpr .r9 + BitVec.ofNat 64 j) = 0
  frame : Frame [⟨s.gpr .r9, 72⟩] s.mem u.mem
  gpr : ∀ r, r ≠ .r10 → u.gpr r = s.gpr r
  r10 : u.gpr .r10 = 0
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem zeros_ok (hp : CPre len s) {s₁ : State} (hg : s₁.gpr = s.gpr) (hm : s₁.mem = s.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) : WP isa (.block zeros) s₁ (ZsInv s 72) := by
  have hB := hp.fitB
  unfold zeros
  refine wp_mov32i fun s₂ g₂ => ?_
  refine wp_range_flatMap (M := isa) (ZsInv s) (fun k u hk h => ?_) 72 (Nat.le_refl _) s₂
    ⟨fun _ h => absurd h (by omega), by rw [g₂.mem, hm]; exact Frame.refl _ _,
      fun r hr => by rw [g₂.other r hr, hg], by rw [g₂.gpr]; rfl, by rw [g₂.rd, hrd], by rw [g₂.wr, hwr]⟩
  refine wp_store8 (a := s.gpr .r9 + BitVec.ofNat 64 k) (by rw [ea_at, h.gpr _ (by decide)])
    (by rw [h.wr]; exact hp.wr k (by omega)) fun u₂ e₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have hm₂ : u₂.mem = u.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 k) (0 : Byte) := by rw [m₂, h.r10]; rfl
  refine ⟨fun j hj => ?_, ?_, fun r hr => by rw [e₂, h.gpr r hr], by rw [e₂, h.r10], by rw [rd₂, h.rd],
    by rw [wr₂, h.wr]⟩
  · rw [hm₂]
    by_cases e : j = k
    · subst e; rw [byte_writeW_eq]
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e]; exact h.zero j (by omega)
  · rw [hm₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem short_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (hg : s₁.gpr = s.gpr) (hm : s₁.mem = s.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hl : (s.gpr .rdx).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  unfold short
  refine WP.seq (WP.block_append (WP.mono (zeros_ok hp hg hm hrd hwr) fun s₂ h₂ => ?_))
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ hz₆ =>
    WP.block_nil ?_
  have ex : ∀ r, r ≠ .r11 → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₆, u₅.other r h1, u₄.other r h1, u₃.other r h1, h₂.gpr r h2]
  have e1 : s₆.gpr .rsi = s.gpr .rsi := ex _ (by decide) (by decide)
  have e2 : s₆.gpr .rdx = s.gpr .rdx := ex _ (by decide) (by decide)
  have e9 : s₆.gpr .r9 = s.gpr .r9 := ex _ (by decide) (by decide)
  have et2 : s₆.gpr .r11 = s.gpr .r9 + BitVec.ofNat 64 (len - (s.gpr .rdx).toNat) := by
    rw [g₆, u₅.gpr, u₄.other .rdx (by decide), u₃.other .rdx (by decide), h₂.gpr .rdx (by decide), u₄.gpr,
      u₃.gpr, h₂.gpr .r9 (by decide), sx_ofNat (by omega)]
    conv => lhs; rw [← ofNat_toNat64 (s.gpr .rdx)]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]
  have em : s₆.mem = s₂.mem := by rw [m₆, u₅.mem, u₄.mem, u₃.mem]
  have ewr : s₆.wr = s.wr := by rw [wr₆, u₅.wr, u₄.wr, u₃.wr, h₂.wr]
  have erd : s₆.rd = s.rd := by rw [rd₆, u₅.rd, u₄.rd, u₃.rd, h₂.rd]
  have hz : ∀ j < 72, s₆.mem (s.gpr .r9 + BitVec.ofNat 64 j) = 0 := by
    intro j hj; rw [em]; exact h₂.zero j hj
  have hzf : Frame [⟨s.gpr .r9, 80⟩] s.mem s₆.mem := by
    rw [em]; exact h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_prefix _ (by omega)⟩
  have hdig : ∀ i < (s.gpr .rdx).toNat, s₆.mem (s.gpr .rsi + BitVec.ofNat 64 i) =
      s.mem (s.gpr .rsi + BitVec.ofNat 64 i) := by
    intro i hi
    exact hzf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact buf_not_hash hp hc hi rfl
  have hzero : (s.gpr .rdx &&& s.gpr .rdx == 0) = decide ((s.gpr .rdx).toNat = 0) := by
    rw [BitVec.and_self]
    by_cases h0 : (s.gpr .rdx).toNat = 0
    · rw [decide_eq_true h0]; simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
    · rw [decide_eq_false h0]; simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; exact h0 (by rw [e]; rfl)
  refine WP.seq (WP.ite (decide ((s.gpr .rdx).toNat = 0)) (by rw [show isa.eval .e s₆ = s₆.zf from rfl, hz₆, ← g₆, e2, hzero])
    (fun h0 => ?_) (fun h0 => ?_))
  · have hd0 : (s.gpr .rdx).toNat = 0 := of_decide_eq_true h0
    refine WP.block_nil (tail_ok wide hp hl ⟨fun j hj => ?_, hzf, e9, erd, ewr, fun r h1 h2 _ _ => ex r h2 h1⟩)
    rw [hz j hj, tz, ite_eq_right (by rw [length_bytesAt, hd0]; omega)]
  · have hd0 : (s.gpr .rdx).toNat ≠ 0 := of_decide_eq_false h0
    refine WP.mono (copyLoop_ok s₆ (N := (s.gpr .rdx).toNat) (by omega) (s.gpr .rdx).isLt
      (by rw [e2, ofNat_toNat64]) (fun i hi => ?_) (fun i hi => ?_) ?_)
      fun t ⟨hc, hf, h9, hrd', hwr', hkp⟩ => tail_ok wide hp hl ⟨fun j hj => ?_, ?_, ?_, ?_, ?_,
        fun r h1 h2 h3 h4 => by rw [hkp r h1 h2 h3 h4, ex r h2 h1]⟩
    · rw [erd, ewr, e1]; exact hp.rd i hi
    · rw [ewr, et2, Offset.add_add]; exact hp.wr _ (by omega)
    · intro x h1 h2
      rw [et2] at h1
      rw [e1] at h2
      exact hp.sep x (in_buf (off := len - (s.gpr .rdx).toNat) (n := (s.gpr .rdx).toNat)
        (by unfold Region.Contains; simp only; omega) (by omega)) (by unfold Region.Contains; simp only; omega)
    · by_cases hin : len - (s.gpr .rdx).toNat ≤ j ∧ j < len
      · have e := hc (j - (len - (s.gpr .rdx).toNat)) (by omega)
        rw [et2, e1, Offset.add_add, show len - (s.gpr .rdx).toNat + (j - (len - (s.gpr .rdx).toNat)) = j by
          omega, hdig _ (by omega)] at e
        rw [e, tz, ite_eq_left (by rw [length_bytesAt]; exact hin), length_bytesAt, hash_byte (by omega)]
      · rw [hf _ fun r hr hcon => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [et2] at hcon
          unfold Region.Contains at hcon
          simp only at hcon
          have := (Offset.lt_iff (s.gpr .r9 + BitVec.ofNat 64 j) (s.gpr .r9) (d := len - (s.gpr .rdx).toNat)
            (n := (s.gpr .rdx).toNat) (by omega)).mp (by omega)
          rw [Mem.sub_ofNat_toNat _ (by omega)] at this
          omega, hz j hj, tz, ite_eq_right (by rw [length_bytesAt]; exact hin)]
    · refine hzf.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hr; subst hr
      rw [et2]; exact Offset.sub_base _ (by omega)
    · rw [h9, e9]
    · rw [hrd', erd]
    · rw [hwr', ewr]

theorem convert_mem (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (MPost len wide s) := by
  have h66 := hp.len66
  unfold convert
  refine WP.seq (wp_cmpi fun s₁ g₁ m₁ rd₁ wr₁ c₁ => WP.block_nil ?_)
  rw [sx_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c₁
  refine WP.ite (decide ((s.gpr .rdx).toNat < len)) c₁ (fun h => short_ok wide hp g₁ m₁ rd₁ wr₁ (of_decide_eq_true h))
    (fun h => long_ok wide hp g₁ m₁ rd₁ wr₁ (Nat.le_of_not_lt (of_decide_eq_false h)))

end VG.Proof.Ecdsa.Verify.X86_64

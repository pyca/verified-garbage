module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Ecdsa.X86_64.VerifyHash
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

/-- No instruction of `convert` writes `rsp`. -/
theorem convert_spSafe (wide : Bool) : (convert len wide).all (fun i => !isa.writesSp i) = true := by
  cases wide <;>
    simp [convert, short, zeros, copyLong, copyLoop, shiftBytes, Code.all, List.all_flatMap, isa, Instr.dst]

/-- No instruction of `convert` loads MXCSR. -/
theorem convert_mx (wide : Bool) : (convert len wide).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq]
  cases wide <;>
    simp [convert, short, zeros, copyLong, copyLoop, shiftBytes, instrs, List.all_flatMap, loadsMxcsr]

/-- What `convert` leaves. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .r9 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .r9, 80⟩] s.mem t.mem
  keep : Kp s t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mx : t.mxcsr = s.mxcsr
  syms : t.syms = s.syms

theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) :=
  WP.mono_syms (WP.mono_mx (convert_mx wide) (convert_mem wide hp) fun _ h m => And.intro h m)
    fun _ ⟨h, m⟩ sy => ⟨h.buf, h.frame, h.keep, h.rd, h.wr, m, sy⟩

/-! ## The contracts, by register -/

variable (I : Spec.Ecdsa.Instance)

/-- The regions of `hashed`'s arguments: `public` in `rdi`, the hash in `rsi`
(`rdx` bytes), `sig` in `rcx`, `scratch` in `r8`, the buffer in `r9`. -/
structure IPre (st : Nat) (s : State) : Prop where
  stk : st = 0 ∨ st ≤ (s.gpr .rsp).toNat
  rd : s.rd = [⟨s.gpr .rdi, 2 * I.curve.len + 1⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .r9, 80⟩]
  d04 : (⟨s.gpr .rdi, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩
  d05 : (⟨s.gpr .rdi, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .r9, 80⟩
  d14 : (⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩
  d15 : (⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 80⟩
  d34 : (⟨s.gpr .rcx, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩
  d35 : (⟨s.gpr .rcx, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r9, 80⟩
  d45 : (⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩ : Region).Disjoint ⟨s.gpr .r9, 80⟩
  below : ∀ r ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) st : List Region),
    r.Disjoint ⟨s.gpr .rdi, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ∧
      r.Disjoint ⟨s.gpr .rcx, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩ ∧
      r.Disjoint ⟨s.gpr .r9, 80⟩
  f0 : (s.gpr .rdi).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  f3 : (s.gpr .rcx).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f4 : (s.gpr .r8).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64
  f5 : (s.gpr .r9).toNat + 80 ≤ 2 ^ 64

theorem hashSig_words : ((I.verifyHashSig.withScratch "buf" .u8 80).words abi.ptrBits).length ≤ 6 := by
  simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.withScratch, Sig.words, Param.words]

/-- `verifyHashContract`'s postcondition. -/
abbrev hPost : I.verifyHashSig.Post abi.ptrBits := fun pk digest digestLen sig _scratch m _m' r =>
  r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m digest digestLen.toNat))
      (Spec.Ecdsa.bytesAt m sig (2 * I.curve.len))
    then 1 else 0

/-- `verifyHashContract`'s leak. -/
abbrev hLeak : Curry (I.verifyHashSig.words abi.ptrBits) (Mem → List Nat) :=
  fun pk digest digestLen sig _scratch m =>
    (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m digest digestLen.toNat ++
      Spec.Ecdsa.bytesAt m sig (2 * I.curve.len)).map (·.toNat)

/-- What the verification that takes the `len` bytes needs, by register:
`public` in `rdi`, the bytes in `rsi`, `sig` in `rdx`, `scratch` in `rcx`. -/
structure KPre (st : Nat) (s : State) : Prop where
  stk : st = 0 ∨ st ≤ (s.gpr .rsp).toNat
  rd : s.rd = [⟨s.gpr .rdi, 2 * I.curve.len + 1⟩, ⟨s.gpr .rsi, I.curve.len⟩, ⟨s.gpr .rdx, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .rcx, Spec.Ecdsa.scratchWords * 8⟩]
  d03 : (⟨s.gpr .rdi, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .rcx, Spec.Ecdsa.scratchWords * 8⟩
  d13 : (⟨s.gpr .rsi, I.curve.len⟩ : Region).Disjoint ⟨s.gpr .rcx, Spec.Ecdsa.scratchWords * 8⟩
  d23 : (⟨s.gpr .rdx, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .rcx, Spec.Ecdsa.scratchWords * 8⟩
  below : ∀ r ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) st : List Region),
    r.Disjoint ⟨s.gpr .rdi, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .rsi, I.curve.len⟩ ∧
      r.Disjoint ⟨s.gpr .rdx, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .rcx, Spec.Ecdsa.scratchWords * 8⟩
  f0 : (s.gpr .rdi).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .rsi).toNat + I.curve.len ≤ 2 ^ 64
  f2 : (s.gpr .rdx).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f3 : (s.gpr .rcx).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64

/-- The key's bytes, at `rdi`. -/
abbrev pkB (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (2 * I.curve.len + 1)

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- `hashed`'s contract, by register, with the tables `K`. -/
def hashR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := IPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .rax).setWidth 32 =
    vres I s.mem (s.gpr .rdi) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .rcx)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧
    (pkB I s₁ ++ hashOf s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .rcx) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ hashOf s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .rcx) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-- The contract of the verification that takes the `len` bytes, by register. -/
def coreR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := KPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .rax).setWidth 32 =
    vres I s.mem (s.gpr .rdi)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) I.curve.len)) (s.gpr .rdx)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .rsi) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .rdx) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .rsi) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .rdx) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-! ## Running the verification on the bytes -/

/-- Verified code run from `s` with narrower permissions: its run from `s`. -/
theorem WP.narrowRun {c : Prog isa} {P : State → Prop} {Q : State → State → Prop}
    (hv : ∀ s, P s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s s') {s : State}
    {rd wr : List Region} (hpre : P (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : Covers wr s.wr) :
    WP isa c s fun s' => abiPreserved s s' ∧ Q (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, s₁, he, ha, hq⟩ := hv _ hpre
  obtain ⟨hr, hwr⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  have e : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  exact ⟨t, _, he', ⟨ha.1, ha.2.1, ha.2.2⟩, by rw [e]; exact hq⟩

theorem length_constRegs (K : List (String × List (BitVec 64))) (s : State) :
    (constRegs K s).length = K.length := by simp [constRegs, Abi.constRegions]

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

/-- The state after `convert` (`u`) and the moves of the arguments (`v`). -/
structure VFacts (s u v : State) : Prop where
  rdi : v.gpr .rdi = s.gpr .rdi
  rsi : v.gpr .rsi = s.gpr .r9
  rdx : v.gpr .rdx = s.gpr .rcx
  rcx : v.gpr .rcx = s.gpr .r8
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  pres : ∀ r ∈ calleeSaved, v.gpr r = s.gpr r
  mx : v.mxcsr = s.mxcsr
  syms : v.syms = s.syms

theorem VFacts.rsp {s u v : State} (h : VFacts s u v) : v.gpr .rsp = s.gpr .rsp :=
  h.pres _ (by decide)

/-- The verification's readable regions: the key, the `len` bytes, the
signature, and the tables. -/
abbrev rdV (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  [⟨s.gpr .rdi, 2 * I.curve.len + 1⟩, ⟨s.gpr .r9, I.curve.len⟩, ⟨s.gpr .rcx, 2 * I.curve.len⟩] ++ constRegs K s

/-- Its writable region: `scratch`. -/
abbrev wrV (s : State) : List Region := [⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩]

section
variable {I} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

theorem hs_rd {s : State} (hs : (hashR I K st).pre s) :
    s.rd = [⟨s.gpr .rdi, 2 * I.curve.len + 1⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩,
      ⟨s.gpr .rcx, 2 * I.curve.len⟩] ++ constRegs K s := by
  have e := hs.1.rd
  simp only [stripConsts, State.withRegions_rd, State.withRegions_gpr] at e
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, e, hs.2.1]

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I K st).pre s) : CPre I.curve.len s := by
  have hp := hs.1
  have hn := nBits_pos I.curve
  have hwr : s.wr = [⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .r9, 80⟩] := hp.wr
  have f5 : (s.gpr .r9).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have f1 : (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 := hp.f1
  refine ⟨by split at hL <;> omega, h66,
    fun i hi => ⟨⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => ⟨⟨s.gpr .r9, 80⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩, hp.d15.symm, f5, f1⟩
  · rw [hs_rd hs]; simp
  · rw [hwr]; simp

theorem args_ok {s u : State} (hu : CPost I.curve.len wide s u) : WP isa (.block args) u (VFacts s u) := by
  refine WP.mono_syms (WP.mono_mx (c := .block args) rfl (Q := fun v => v.gpr .rdi = s.gpr .rdi ∧
      v.gpr .rsi = s.gpr .r9 ∧ v.gpr .rdx = s.gpr .rcx ∧ v.gpr .rcx = s.gpr .r8 ∧ v.mem = u.mem ∧
      v.rd = s.rd ∧ v.wr = s.wr ∧ (∀ r ∈ calleeSaved, v.gpr r = s.gpr r))
    (wp_mov fun v₁ g₁ => wp_mov fun v₂ g₂ => wp_mov fun v g₃ => WP.block_nil ?_) fun v hv hm => And.intro hv hm)
    fun v ⟨hv, hm⟩ hsv => ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1,
      hv.2.2.2.2.2.2.2, hm.trans hu.mx, hsv.trans hu.syms⟩
  have k := hu.keep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), k _ (by decide) (by decide)
      (by decide) (by decide)]
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, k _ (by decide) (by decide) (by decide) (by decide)]
  · rw [g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), k _ (by decide) (by decide) (by decide) (by decide)]
  · rw [g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), k _ (by decide) (by decide) (by decide) (by decide)]
  · rw [g₃.mem, g₂.mem, g₁.mem]
  · rw [g₃.rd, g₂.rd, g₁.rd, hu.rd]
  · rw [g₃.wr, g₂.wr, g₁.wr, hu.wr]
  · have h : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃.other _ h.2.2.1, g₂.other _ h.2.1, g₁.other _ h.1, k r h.2.2.2.1 h.2.2.2.2 h.1 h.2.1]

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K st).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    (coreR I K st).pre (v.withRegions (rdV I K s) (wrV s)) ∧
      Covers (rdV I K s ++ wrV s) (v.rd ++ v.wr) ∧ Covers (wrV s) v.wr := by
  obtain ⟨hp, hk⟩ := hs
  have hrdS := hs_rd ⟨hp, hk⟩
  have hwr : s.wr = [⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .r9, 80⟩] := hp.wr
  have vsp := hv.rsp
  obtain ⟨va0, va1, va2, va3, vmem, vrd, vwr, -, -, hsy'⟩ := hv
  have hL80 : I.curve.len ≤ 80 := by omega
  have f0 := hp.f0
  have f3 := hp.f3
  have f4 := hp.f4
  have f5 : (s.gpr .r9).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have hcR : constRegs K v = constRegs K s := by simp only [constRegs, hsy']
  let rd' : List Region := rdV I K s
  let wr' : List Region := wrV s
  have hsc : (⟨s.gpr .r8, Spec.Ecdsa.scratchWords * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hbf : (⟨s.gpr .r9, 80⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hstrip : stripConsts K (v.withRegions rd' wr') =
      (v.withRegions [⟨s.gpr .rdi, 2 * I.curve.len + 1⟩, ⟨s.gpr .r9, I.curve.len⟩,
        ⟨s.gpr .rcx, 2 * I.curve.len⟩] wr') := by
    simp only [stripConsts, State.withRegions_rd, State.withRegions_withRegions, State.withRegions_wr, rd']
    congr 1
    rw [List.length_append, length_constRegs, List.take_left' (by simp)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hstrip]
    have hb := hp.below
    simp only [stripConsts_gpr] at hb
    refine ⟨by rw [State.withRegions_gpr, vsp]; exact hp.stk,
      by simp only [State.withRegions_rd, State.withRegions_gpr, va0, va1, va2],
      by simp only [State.withRegions_wr, State.withRegions_gpr, va3, wr'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_gpr, va0, va3]; exact hp.d04
    · simp only [State.withRegions_gpr, va1, va3]
      exact (hp.d45.sub_right (sub_prefix _ hL80)).symm
    · simp only [State.withRegions_gpr, va2, va3]; exact hp.d34
    · intro r hr
      simp only [State.withRegions_gpr, vsp] at hr
      obtain ⟨b0, -, b3, b4, b5⟩ := hb r hr
      simp only [State.withRegions_gpr, va0, va1, va2, va3]
      exact ⟨b0, b5.sub_right (sub_prefix _ hL80), b3, b4⟩
    · simp only [State.withRegions_gpr, va0]; exact f0
    · simp only [State.withRegions_gpr, va1]; omega
    · simp only [State.withRegions_gpr, va2]; exact f3
    · simp only [State.withRegions_gpr, va3]; exact f4
  · have htab : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved st s, t.Disjoint r := hk.2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (rd'.drop (rd'.length - K.length)) = constRegs K v
      rw [hcR]
      simp only [rd', List.length_append, length_constRegs, List.length_cons, List.length_nil]
      rw [show 0 + 1 + 1 + 1 + K.length - K.length = 3 by omega, List.drop_left' (by simp)]
    · intro c hc i hi
      show v.mem.readW (v.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
      have ht : (⟨s.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs K s :=
        List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc
      have hfit : (s.syms c.1).toNat + 8 * c.2.length ≤ 2 ^ 64 := (htab _ ht).1
      rw [hsy', vmem, Frame.readW hu.frame (r := ⟨s.syms c.1, 8 * c.2.length⟩)
        (Offset.contains_base _ (by omega) (by omega))
        (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (htab _ ht).2.1 _ hbf) (by decide)]
      exact hk.2.1 c hc i hi
    · intro t ht
      rw [show constRegs K (v.withRegions rd' wr') = constRegs K s from hcR] at ht
      obtain ⟨a, b, c⟩ := htab t ht
      refine ⟨a, fun r hr => b r ?_, fun r hr => c r ?_⟩
      · simp only [State.withRegions_wr, List.mem_singleton] at hr; subst hr; exact hsc
      · simpa [abi, State.withRegions_gpr, vsp] using hr
    · intro t ht
      rw [show constRegs K (v.withRegions rd' wr') = constRegs K s from hcR] at ht
      exact hk.2.2.2 t ht
  · refine Covers.of_sub fun r hr => ?_
    rw [vrd, vwr]
    simp only [rdV, wrV, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | rfl | hr | hr
    · exact covers_self (by rw [hrdS]; simp)
    · exact ⟨_, List.mem_append_right _ hbf, 0, by simp, by simp; omega⟩
    · exact covers_self (by rw [hrdS]; simp)
    · exact covers_self (by rw [hrdS]; simp [hr])
    · simp only [List.not_mem_nil, or_false] at hr; subst hr
      exact covers_self (List.mem_append_right _ hsc)
  · refine Covers.of_sub fun r hr => ?_
    simp only [wrV, List.mem_singleton] at hr; subst hr
    rw [vwr]; exact covers_self hsc

theorem vpost {s u v : State}
    (hs : (hashR I K st).pre s) (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (s.gpr .r9) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .rdi) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .rdi) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .rcx) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .rcx) (2 * I.curve.len) := by
  have hp := hs.1
  have f0 := hp.f0
  have f3 := hp.f3
  refine ⟨bytesAt_ext (length_fixedDigest _ _ _) fun i hi => by rw [hv.mem]; exact hu.buf i hi, ?_, ?_⟩
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d05 (by omega)
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d35 (by omega)

/-- The return address, at `rsp`, is outside the buffer, so `convert` keeps it. -/
theorem ret_kept {s u : State} (hs : (hashR I K st).pre s) (hu : CPost I.curve.len wide s u) :
    u.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hb := (hs.1.below ⟨s.gpr .rsp, 8⟩ (List.mem_cons_self ..)).2.2.2.2
  simp only [stripConsts_gpr] at hb
  exact Frame.readW hu.frame (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hb) (by decide)

end

theorem hashed_correct {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (s : State) (hs : (hashR I K st).pre s) :
    ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧ abiPreserved s s' ∧ (hashR I K st).post s s' := by
  unfold hashed
  refine WP.seq (WP.mono (convert_ok wide (cpre_of hL h66 hs)) fun u hu => ?_)
  refine WP.seq (WP.mono (args_ok hu) fun v hv => ?_)
  obtain ⟨hpre, hc, hw⟩ := vpre h66 hs hu hv
  refine WP.mono (WP.narrowRun hcv hpre hc hw) fun s' ⟨habi, hpost⟩ =>
    ⟨⟨fun r hr => (habi.1 r hr).trans (hv.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [← hv.rsp, habi.2.1, hv.mem, hv.rsp]; exact ret_kept hs hu
  · rw [habi.2.2, hv.mx]
  · obtain ⟨e1, e2, e3⟩ := vpost hs hu hv
    have hq : (s'.gpr .rax).setWidth 32 = vres I v.mem (s.gpr .rdi)
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt v.mem (s.gpr .r9) I.curve.len)) (s.gpr .rcx) := by
      have := hpost
      simp only [coreR, State.withRegions_gpr, State.withRegions_mem, hv.rdi, hv.rsi, hv.rdx] at this
      exact this
    show (s'.gpr .rax).setWidth 32 = vres I s.mem (s.gpr .rdi) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .rcx)
    rw [hq, e1, hashToInt_fixedDigest hL]
    simp only [vres, e2, e3]

/-! ## Constant time -/

/-- Inlined verified code: two runs, from states that narrow to ones its
contract relates, leak the same. -/
theorem RelCT.inlineV {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.withRegions rd₁ wr₁) ∧ k.pre (s₂.withRegions rd₂ wr₂) ∧
      k.pub (s₁.withRegions rd₁ wr₁) (s₂.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

/-- The arguments' moves leak nothing. -/
theorem args_taint : (taint.check (Taint.ofRegs [.rdi, .rcx, .r8, .r9]) (.block args)
    (.block [] 256)).isSome = true := by
  decide

section
variable {I} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

/-- Two runs as `hashR` relates them. -/
abbrev HP (s₁ s₂ : State) : Prop := (hashR I K st).pre s₁ ∧ (hashR I K st).pre s₂ ∧ (hashR I K st).pub s₁ s₂

theorem hashed_ct {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (hct : ConstantTime isa (coreR I K st).pre (coreR I K st).pub core) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I K st).pre (hashR I K st).pub (hashed I.curve.len wide core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧ HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ CPost I.curve.len wide σ₂ x₂)
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (fun s₁ s₂ h => ?_) htc).wpDep
      (F := fun (s t : State) => CPost I.curve.len wide s t) fun s₁ s₂ h =>
        ⟨convert_ok wide (cpre_of hL h66 h.1), convert_ok wide (cpre_of hL h66 h.2.1)⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
    obtain ⟨-, -, -, p0, p1, p2, p3, p4, p5, -⟩ := h
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    refine ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rcx, .r8, .r9]) (fun s₁ s₂ h => ?_) args_taint).wp
      (F₁ := fun v => (HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧
        CPost I.curve.len wide σ₂ x₂) ∧ VFacts σ₁ x₁ v) (F₂ := VFacts σ₂ x₂)
      fun u₁ u₂ ⟨e₁, e₂, hp, c₁, c₂⟩ => by
        subst e₁ e₂; exact ⟨WP.mono (args_ok c₁) fun _ h => ⟨⟨hp, c₁, c₂⟩, h⟩, args_ok c₂⟩).mono
      (fun _ _ h => h) fun v₁ v₂ ⟨_, ⟨⟨hp, c₁, c₂⟩, f₁⟩, f₂⟩ => ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩
    obtain ⟨e₁, e₂, ⟨-, -, -, p0, -, -, p3, p4, p5, -⟩, c₁, c₂⟩ := h
    subst e₁ e₂
    have k₁ := c₁.keep
    have k₂ := c₂.keep
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₁ _ (by decide) (by decide) (by decide) (by decide), k₂ _ (by decide) (by decide) (by decide) (by decide), p0]
    · rw [k₁ _ (by decide) (by decide) (by decide) (by decide), k₂ _ (by decide) (by decide) (by decide) (by decide), p3]
    · rw [k₁ _ (by decide) (by decide) (by decide) (by decide), k₂ _ (by decide) (by decide) (by decide) (by decide), p4]
    · rw [k₁ _ (by decide) (by decide) (by decide) (by decide), k₂ _ (by decide) (by decide) (by decide) (by decide), p5]
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 c₁ f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 c₂ f₂
    refine ⟨_, _, _, _, q₁, q₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
    obtain ⟨psp, p0, p1, p2, p3, p4, p5, pl, psy⟩ := hp.2.2
    obtain ⟨b₁, k₁, g₁⟩ := vpost hp.1 c₁ f₁
    obtain ⟨b₂, k₂, g₂⟩ := vpost hp.2.1 c₂ f₂
    obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [pkB, length_bytesAt])
      (by simp only [hashOf, length_bytesAt, p2]) pl
    refine ⟨by simp only [State.withRegions_gpr, f₁.rsp, f₂.rsp, psp],
      by simp only [State.withRegions_gpr, f₁.rdi, f₂.rdi, p0],
      by simp only [State.withRegions_gpr, f₁.rsi, f₂.rsi, p5], by simp only [State.withRegions_gpr, f₁.rdx, f₂.rdx, p3],
      by simp only [State.withRegions_gpr, f₁.rcx, f₂.rcx, p4], ?_, fun c hc => ?_⟩
    · simp only [pkB, State.withRegions_mem, State.withRegions_gpr, f₁.rdi, f₁.rsi, f₁.rdx, f₂.rdi, f₂.rsi, f₂.rdx]
      rw [b₁, k₁, g₁, b₂, k₂, g₂]
      simp only [pkB] at ek
      rw [ek, eh, eg]
    · show v₁.syms c.1 = v₂.syms c.1
      rw [f₁.syms, f₂.syms]; exact psy c hc
end

/-! ## The contracts of `Spec/`, by register -/

section
variable {I}

theorem scratch_bytes : Spec.Ecdsa.scratchWords * 8 = 8192 := rfl

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  simp [stripConsts, State.withRegions]

theorem constsOk_nil (st : Nat) (s : State) : ConstsOk [] st s := by
  simp [ConstsOk, constRegs, Abi.constRegions, Abi.constsHeld]

theorem below8_mem (sp : Addr) : (⟨sp - 8#64, 8⟩ : Region) ∈ (⟨sp, 8⟩ :: stackBelow sp 8 : List Region) := by
  simp [stackBelow]

/-- The verification's precondition under `abi`, from `KPre`. -/
theorem core_pre {s : State} (h : KPre I 8 s) : (I.verifyContract abi 8).pre s := by
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86_64.abi, X86_64.argRegs]
  have hwr := h.wr
  rw [scratch_bytes] at hwr
  obtain ⟨r0, r1, r2, r3⟩ := h.below _ (List.mem_cons_self ..)
  obtain ⟨b0, b1, b2, b3⟩ := h.below _ (below8_mem _)
  exact ⟨h.stk.resolve_left (by decide), h.rd, hwr, h.d03, h.d13, h.d23, r0, r1, r2, r3, b0, b1, b2, b3,
    h.f0, h.f1, h.f2, h.f3⟩

theorem core_post {s s' : State} (h : (I.verifyContract abi 8).post s s') :
    (s'.gpr .rax).setWidth 32 = vres I s.mem (s.gpr .rdi)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) I.curve.len)) (s.gpr .rdx) := by
  sig_post [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86_64.abi, X86_64.argRegs] at h
  exact h

theorem core_pub {s₁ s₂ : State} (h : s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
    s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .rsi) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .rdx) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .rsi) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .rdx) (2 * I.curve.len)).map (·.toNat)) :
    (I.verifyContract abi 8).pub s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86_64.abi, X86_64.argRegs]
  obtain ⟨psp, p0, p1, p2, p3, pl⟩ := h
  exact ⟨psp, pl, p0, p1, p2, p3⟩

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_nil {core : Prog isa} (h : Verified target core (I.verifyContract abi 8)) :
    (∀ s, (coreR I [] 8).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I [] 8).post s s') ∧
      ConstantTime isa (coreR I [] 8).pre (coreR I [] 8).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I [] 8).pre s → (I.verifyContract abi 8).pre s := fun s hs => by
    have := hs.1; rw [stripConsts_nil] at this; exact core_pre this
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, -⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (core_pub ⟨psp, p0, p1, p2, p3, pl⟩) e₁ e₂

/-- The same, from its proof under `abi.withConsts` of its tables. -/
theorem coreR_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {core : Prog isa} (h : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 8)) :
    (∀ s, (coreR I (c₀ :: cs) 8).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I (c₀ :: cs) 8).post s s') ∧
      ConstantTime isa (coreR I (c₀ :: cs) 8).pre (coreR I (c₀ :: cs) 8).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I (c₀ :: cs) 8).pre s → (I.verifyContract (abi.withConsts (c₀ :: cs)) 8).pre s :=
    fun s hs => pre_consts.mpr ⟨core_pre hs.1, hs.2⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post (post_consts.mp hq)⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, psy⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂)
      (pub_consts.mpr ⟨core_pub ⟨psp, p0, p1, p2, p3, pl⟩, psy⟩) e₁ e₂

end

/-! ## `hashed`, under the contracts of `Spec/` -/

section
variable {I}

/-- `hashed`'s contract under `abi`, with the buffer as a last argument. -/
abbrev innerA : Contract isa :=
  Sig.scratchContract abi I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _) (hPost I) true 8
    (some (hLeak I))

/-- The same under `abi.withConsts`. -/
abbrev innerK (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) : Contract isa :=
  Sig.scratchContract (abi.withConsts (c₀ :: cs)) I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _)
    (hPost I) true 8 (some (hLeak I))

theorem pre_leak {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} :
    (sig.contract abi pre post wa st leak).pre s ↔ (sig.contract abi pre post wa st none).pre s := Iff.rfl

theorem inner_ipre {s : State} (h : (innerA (I := I)).pre s) : IPre I 8 s := by
  have h' := (pre_regs (hashSig_words I) rfl).mp h
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.withScratch, Sig.bufs, regArgs, argRegs, Sig.words,
    Param.words, Elem.size, List.pairwise_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.take, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil] at h'
  simp at h'
  obtain ⟨hstk, hrd, hwr, ⟨⟨d04, d05⟩, ⟨d14, d15⟩, ⟨d34, d35⟩, d45⟩, ⟨hr, hb⟩, ⟨f0, f1, f3, f4, f5⟩, -⟩ := h'
  refine ⟨.inr hstk, hrd, hwr, d04, d05, d14, d15, d34, d35, d45, fun r hr' => ?_, f0, f1, f3, f4, by omega⟩
  rcases List.mem_cons.mp hr' with rfl | hr'
  · exact hr
  · exact hb r hr'

theorem inner_post {s s' : State} (h : (hashR I [] 8).post s s') : (innerA (I := I)).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs]
  exact h

theorem inner_pub {K : List (String × List (BitVec 64))} {s₁ s₂ : State} (h : (innerA (I := I)).pub s₁ s₂)
    (hsy : ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1) : (hashR I K 8).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨psp, pl, p0, p1, p2, p3, p4, p5⟩ := h
  exact ⟨psp, p0, p1, p2, p3, p4, p5, pl, hsy⟩

/-- `hashed` under `abi`. -/
theorem hashed_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 8)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerA (I := I)).pre s) :
    Verified target (hashed I.curve.len wide core) (innerA (I := I)) := by
  obtain ⟨hcv, hct⟩ := coreR_nil hcore
  refine Verified.of_correct (T := target) (k := hashR I [] 8) (k' := innerA (I := I))
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc)
    ⟨fun s hs => ⟨by rw [stripConsts_nil]; exact inner_ipre hs, constsOk_nil 8 s⟩,
      fun s s' _ h => inner_post h, fun s₁ s₂ _ _ h => inner_pub h fun _ h => absurd h List.not_mem_nil, hsat⟩

/-- `hashed` under `abi.withConsts` of the verification's tables. -/
theorem hashed_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 8)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerK (I := I) c₀ cs).pre s) :
    Verified target (hashed I.curve.len wide core) (innerK (I := I) c₀ cs) := by
  obtain ⟨hcv, hct⟩ := coreR_cons hcore
  refine Verified.of_correct (T := target) (k := hashR I (c₀ :: cs) 8) (k' := innerK (I := I) c₀ cs)
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc) ⟨fun s hs => ?_,
      fun s s' _ h => post_consts.mpr (inner_post h), fun s₁ s₂ _ _ h => ?_, hsat⟩
  · obtain ⟨h₁, h₂⟩ := pre_consts.mp hs
    exact ⟨inner_ipre h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := pub_consts.mp h
    exact inner_pub h₁ h₂

/-- `hashed` writes `rsp` nowhere if the verification does not. -/
theorem hashed_spSafe {wide : Bool} {core : Prog isa} (h : core.all (fun i => !isa.writesSp i) = true) :
    (hashed I.curve.len wide core).all (fun i => !isa.writesSp i) = true := by
  show ((convert I.curve.len wide).all _ && ((Code.block args : Prog isa).all _ && core.all _)) = true
  rw [convert_spSafe, h]
  rfl

/-- `hashed` uses the verification's stack. -/
theorem hashed_depth {wide : Bool} {core : Prog isa} :
    (hashed I.curve.len wide core).x86_64Depth = core.x86_64Depth := by
  cases wide <;> simp [hashed, convert, short, copyLoop, Code.x86_64Depth]

end

/-! ## The frame, with a leak

`Verified.stackScratch` and `narrow_pub` (`Proof/Framework/X86_64/StackScratch.lean`)
for a contract with a leak, as on RISC-V: `narrow` keeps the memory, so the
leak is the same. -/

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat}

/-- The public data of a contract whose arguments are all in registers, with
its leak. -/
theorem pub_regsL {stack : Nat} {s₁ s₂ : State} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : (sig.words abi.ptrBits).length ≤ 6) (hl : Sig.noLists sig.params = true) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.gpr .rsp = s₂.gpr .rsp ∧ leakAgree leak (regArgs sig s₁) s₁.mem (regArgs sig s₂) s₂.mem) ∧
      ∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 6 := hk
    simpa [argRegs] using this
  have hD := fun vs => Sig.descs_of_noLists 64 sig.params vs hl
  simp only [Sig.contract, abi, List.length_map, hk', ite_true, hD, List.not_mem_nil, false_implies,
    implies_true, and_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

theorem narrow_pubL (hk : (sig.words abi.ptrBits).length < 6) {s₁ s₂ : State}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂) (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regsL (by omega) hl] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  have hp' : (sig.contract abi pre post wa (stack + bytes)).pub s₁ s₂ :=
    (pub_regs (by omega) hl).mpr ⟨hsp, hpa⟩
  have hn := (pub_regs (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)
    (Sig.noLists_withScratch nm e n hl)).mp (narrow_pub (nm := nm) hk hp' hl)
  refine (pub_regsL (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)
    (Sig.noLists_withScratch nm e n hl)).mpr ⟨⟨hn.1, ?_⟩, hn.2⟩
  have l₁ := regArgs_length sig s₁ (by omega)
  have l₂ := regArgs_length sig s₂ (by omega)
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_mem, narrow_mem]
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _ =
      Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _
    rw [Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₁,
      Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₂]
    exact hlk

/-- `Verified.stackScratch`, with any leak. -/
theorem stackScratchL {c : Prog isa} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (Impl.StackScratch.X86_64.withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (Impl.StackScratch.X86_64.withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c)
        s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_pre hk hb hst hs hl)
    exact ⟨t, s₃, he, hq, withStackScratch_run hk hb hst hsafe hd hs he ha hl⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨t, _, hex, ha, ?_⟩
    refine (post_regs (pre := pre) (wa := wa) (stack := stack + bytes) (by omega)).mpr ?_
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) (wa := wa) (stack := stack)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hrax]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params post
      _ _ (hlen s (by omega))) s.mem) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrow_pre (post := post) hk hb hst h₁ hl) (narrow_pre (post := post) hk hb hst h₂ hl) (narrow_pubL hk hp hl) f₁ f₂

/-- The same, for code that reads the tables `c₀ :: cs`, under `abi.withConsts (c₀ :: cs)`. -/
theorem stackScratchLC {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))} {c : Prog isa}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length < 6)
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ 8 + n * e.size ≤ bytes)
    (hst : stack + bytes + 8 ≤ 2 ^ 64)
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ stack)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (Impl.StackScratch.X86_64.withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack).post
        (narrow sig e n bytes s) s₃ ∧
      Exec isa (Impl.StackScratch.X86_64.withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .rax) c)
        s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr .rax = s₃.gpr .rax := by
    intro s hs
    have hs' := (pre_regs (by omega) hl).mp (pre_consts.mp hs).1
    obtain ⟨hwf, -, hwr, -, hres, -, -⟩ := hs'
    simp only [stripConsts_gpr, stripConsts_wr] at hwf hwr hres
    have hsb : stack + bytes ≤ (s.gpr .rsp).toNat := by rcases hwf with h | h <;> omega
    have hretW : ∀ r ∈ s.wr, Region.Disjoint ⟨s.gpr .rsp, 8⟩ r := fun r hr => by
      rw [hwr] at hr
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hr
      exact hres _ (List.mem_cons_self ..) a (List.mem_filter.mp ha').1
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowK_pre hk hb hst hs hl)
    exact ⟨t, s₃, he, hq, withStackScratchK_run hk hb hst hsafe hd hsb hretW he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hrax⟩ := hrun s hs
    refine ⟨t, _, hex, ha, ?_⟩
    refine post_consts.mpr ((post_regs (pre := pre) (wa := wa) (stack := stack + bytes) (by omega)).mpr ?_)
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) (wa := wa) (stack := stack)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp (post_consts.mp hq)
    rw [narrow_regArgs hk] at hq'
    rw [hm, hrax]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params post
      _ _ (hlen s (by omega))) s.mem) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    exact hct _ _ _ _ _ _ (narrowK_pre (post := post) hk hb hst h₁ hl) (narrowK_pre (post := post) hk hb hst h₂ hl)
      (pub_consts.mpr ⟨narrow_pubL hk hp' hl, fun c hc => hsy c hc⟩) f₁ f₂

end

/-! ## `vg_ecdsa_<curve>_verify` -/

section
variable {I}

theorem hashSig_lt : (I.verifyHashSig.words abi.ptrBits).length < 6 := by
  simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words]

theorem frame_bytes : 0 < bufBytes ∧ bufBytes < 4096 ∧ bufBytes % 8 = 0 ∧ 8 + 80 * Elem.u8.size ≤ bufBytes := by
  decide

/-- `vg_ecdsa_<curve>_verify` under `abi`, from the verification of the `len`
bytes, which writes `rsp` nowhere (`hsp`) and uses 8 bytes of stack (`hd`). -/
theorem verifyHash_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 8))
    (hsp : core.all (fun i => !isa.writesSp i) = true) (hd : core.x86_64Depth ≤ 8) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract abi 96).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi 96) := by
  obtain ⟨s₀, h₀⟩ := hsat
  exact stackScratchL (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 8) (bytes := bufBytes)
    (hashed_verified_nil hL h66 hcore htc
      ⟨_, narrow_pre (nm := "buf") hashSig_lt frame_bytes (by decide) (pre_leak.mp h₀) rfl⟩)
    hashSig_lt frame_bytes (by decide) (hashed_spSafe hsp) (by rw [hashed_depth]; exact hd) ⟨s₀, h₀⟩ rfl

/-- `vg_ecdsa_<curve>_verify` under `abi.withConsts`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 8))
    (hsp : core.all (fun i => !isa.writesSp i) = true) (hd : core.x86_64Depth ≤ 8) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96) := by
  obtain ⟨s₀, h₀⟩ := hsat
  exact stackScratchLC (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 8) (bytes := bufBytes)
    (hashed_verified_cons hL h66 hcore htc
      ⟨_, narrowK_pre (nm := "buf") (post := hPost I) hashSig_lt frame_bytes (by decide) h₀ rfl⟩)
    hashSig_lt frame_bytes (by decide) (hashed_spSafe hsp) (by rw [hashed_depth]; exact hd) ⟨s₀, h₀⟩ rfl

end

/-! ## Satisfiability -/

section
variable {I}

/-- `s₀`, for the verification of the `len` bytes, with `len` in `rdx`, `sig`
in `rcx` and `scratch` in `r8`: the hash is the `len` bytes. -/
def hashSatState (L : Nat) (s₀ : State) : State :=
  { s₀ with gpr := fun r => match r with
      | .rdx => BitVec.ofNat 64 L | .rcx => s₀.gpr .rdx | .r8 => s₀.gpr .rcx | r => s₀.gpr r }

theorem hashSat_abi (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract abi 8).pre s₀)
    (hsp : 96 ≤ (s₀.gpr .rsp).toNat)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.gpr .rsp - 96#64, 96⟩ : Region).Disjoint r) :
    (I.verifyHashContract abi 96).pre (hashSatState I.curve.len s₀) := by
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    X86_64.abi, X86_64.argRegs] at h₀
  obtain ⟨-, hrd, hwr, d0, d1, d2, r0, r1, r2, r3, -, -, -, -, f0, f1, f2, f3⟩ := h₀
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    X86_64.abi, X86_64.argRegs, stackBelow]
  have hL : (BitVec.ofNat 64 I.curve.len).toNat = I.curve.len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [hL]
  rw [hrd, hwr] at hd
  exact ⟨hsp, hrd, hwr, d0, d1, d2, r0, r1, r2, r3, hd _ (by simp), hd _ (by simp), hd _ (by simp),
    hd _ (by simp), f0, f1, f2, f3⟩

/-- A state satisfying `verifyHashContract`'s precondition under `abi`, from
one of the verification's whose 96 bytes below `rsp` are free. -/
theorem hashSat_nil (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract abi 8).pre s₀)
    (hsp : 96 ≤ (s₀.gpr .rsp).toNat)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.gpr .rsp - 96#64, 96⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract abi 96).pre s :=
  ⟨_, hashSat_abi h66 h₀ hsp hd⟩

/-- The same under `abi.withConsts`. -/
theorem hashSat_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract (abi.withConsts (c₀ :: cs)) 8).pre s₀)
    (hsp : 96 ≤ (s₀.gpr .rsp).toNat)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.gpr .rsp - 96#64, 96⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96).pre s := by
  obtain ⟨h₁, hk⟩ := pre_consts.mp h₀
  refine ⟨hashSatState I.curve.len s₀, pre_consts.mpr ⟨?_, ?_⟩⟩
  · exact hashSat_abi h66 h₁ hsp fun r hr => hd r (by
      simp only [stripConsts, State.withRegions_rd, State.withRegions_wr, List.mem_append] at hr ⊢
      exact hr.imp (fun h => List.mem_of_mem_take h) id)
  · obtain ⟨k1, k2, k3, k4⟩ := hk
    refine ⟨k1, k2, fun t ht => ⟨(k3 t ht).1, (k3 t ht).2.1, fun r hr => ?_⟩, k4⟩
    have hr' : r = ⟨s₀.gpr .rsp, 8⟩ ∨ r = ⟨s₀.gpr .rsp - 96#64, 96⟩ := by
      simpa [abi, stackBelow, below, hashSatState] using hr
    rcases hr' with rfl | rfl
    · exact (k3 t ht).2.2 _ (List.mem_cons_self ..)
    · have htd : t ∈ s₀.rd := by
        rw [← List.take_append_drop (s₀.rd.length - (c₀ :: cs).length) s₀.rd, k1]
        exact List.mem_append_right _ ht
      exact (hd _ (List.mem_append_left _ htd)).symm

end

end VG.Proof.Ecdsa.Verify.X86_64

module

public import VerifiedGarbage.Impl.Mont.Arm.Dynamic
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Arm.Words

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the working space

The working space of the runtime-modulus arithmetic (`Ws`) is `Scr` without
its bound of 4096 bytes: its arrays lie past an immediate offset's reach, and
the code reaches them through pointers `r12 + K` that `ptr` sets
(`wp_ptr`). `ptrLoop_ok` runs `ptrLoop p body` from an invariant `P j` that
holds before the body runs for `j`, with `p = A + step·j` and `r9` at the end.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_movw wp_dp wp_cmp op2_reg eval_ne)

/-- The working space: `r12` holds its base `base`, it is the start of a
writable region (which may be longer) and it lies below `2³²`. -/
structure Ws (s : State) (base : Addr) (size : Nat) : Prop where
  wb : State.addr (s.gpr .r12) = base
  wr : ∃ len, size ≤ len ∧ len ≤ 2 ^ 32 ∧ (⟨base, len⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

theorem Ws.wb_toNat {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) :
    (s.gpr .r12).toNat = base.toNat := by
  rw [← hs.wb, VG.Proof.X25519.Arm.addr_toNat]

/-- `[r + d]`, with `r` at `K` bytes into the working space. -/
theorem Ws.ea {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {r : Reg} {K d : Nat}
    (hr : s.gpr r = s.gpr .r12 + BitVec.ofNat 32 K) (hd : K + d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 d) = off base (K + d) := by
  rw [hr, Offset.add_add, VG.Arm.addr_add (by have := hs.nowrap; have := hs.wb_toNat; omega), hs.wb]

/-- `[r12 + d]`. -/
theorem Ws.ea12 {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {d : Nat} (hd : d < size) :
    State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = off base d := by
  have := hs.ea (r := .r12) (K := 0) (d := d) (BitVec.add_zero _).symm (by omega)
  rwa [Nat.zero_add] at this

theorem Ws.read {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, List.mem_append_right _ hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Ws.write {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n :=
  have ⟨_, hl, hl', hR⟩ := hs.wr
  ⟨_, hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Ws.of_rest {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h : Rest rs s s') (hr : .r12 ∉ rs) : Ws s' base size :=
  ⟨by rw [h.gpr _ hr]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Ws.of_upd {s s' : State} {d : Reg} {v : BitVec 32} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h : Upd s s' d v) (hd : d ≠ .r12) : Ws s' base size :=
  ⟨by rw [h.other _ (Ne.symm hd)]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Ws.of_mupd {s s' : State} {m : Mem} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h : Mupd s s' m) : Ws s' base size :=
  ⟨by rw [h.gpr]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Ws.of_fupd {s s' : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h : Fupd s s') : Ws s' base size :=
  ⟨by rw [h.gpr]; exact hs.wb, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Ws.mono {s : State} {base : Addr} {size size' : Nat} (hs : Ws s base size) (h : size' ≤ size) :
    Ws s base size' :=
  have ⟨len, hl, hl', hR⟩ := hs.wr
  ⟨hs.wb, ⟨len, by omega, hl', hR⟩, by have := hs.nowrap; omega⟩

/-- A register after an update, for `simp` with literal registers. -/
theorem _root_.VG.Proof.X25519.Arm.Upd.get {s s' : State} {d : Reg} {v : BitVec 32} (h : Upd s s' d v) (r : Reg) :
    s'.gpr r = if r = d then v else s.gpr r := by
  by_cases e : r = d
  · subst e; simp only [↓reduceIte, h.gpr]
  · simp only [e, ↓reduceIte, h.other r e]

/-! ## Pointers -/

theorem movw_ofNat {k : Nat} (h : k < 2 ^ 16) : (BitVec.ofNat 16 k).setWidth 32 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `d = r12 + k`. -/
theorem wp_ptr {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {k : Nat} (hd : d ≠ .r12)
    (hk : k < 2 ^ 16) (c : ∀ s', Upd s s' d (s.gpr .r12 + BitVec.ofNat 32 k) → WP isa (.block is) s' Q) :
    WP isa (.block (ptr d k ++ is)) s Q := by
  simp only [ptr, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => c s₂ ?_
  have e : VG.Proof.X25519.Arm.dpVal .add (s₁.gpr .r12) (s₁.gpr d) = s.gpr .r12 + BitVec.ofNat 32 k := by
    show s₁.gpr .r12 + s₁.gpr d = _
    rw [u₁.other _ (Ne.symm hd), u₁.gpr, movw_ofNat hk]
  exact ⟨u₂.gpr.trans e, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem,
    u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : (BitVec.ofNat 32 n).rotateLeft (2 * 0) = BitVec.ofNat 32 n := by ext i; simp
    simp only [h0, decide_eq_true_eq, BitVec.toNat_ofNat]
    omega⟩

/-- `p += k`. -/
theorem wp_bump {s : State} {is : List Instr} {Q : State → Prop} {p : Reg} {k : Nat} (hk : k < 256)
    (c : ∀ s', Upd s s' p (s.gpr p + BitVec.ofNat 32 k) → WP isa (.block is) s' Q) :
    WP isa (.block (bump p k :: is)) s Q :=
  wp_dp (VG.Proof.X25519.Arm.op2_imm (encodable_lt hk)) c

/-! ## Loops over pointers -/

theorem sub_add_add (A : BitVec 32) (a b : Nat) :
    A + BitVec.ofNat 32 a - (A + BitVec.ofNat 32 b) = BitVec.ofNat 32 a - BitVec.ofNat 32 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := A.isLt
  omega

theorem cmp_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    have z : (0 : BitVec 32).toNat = 0 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, z] at this
    omega

/-- The loop: `body` runs for `j = 0, …, k - 1`, from `P j` with `p = A + step·j`
and `r9 = A + step·k`, to `P (j + 1)` with `p` moved up a step and `r9` kept.
The invariant may not depend on the flags. -/
theorem ptrLoop_ok {s : State} {p : Reg} {body : List Instr} {A : BitVec 32} {step k : Nat}
    (P : Nat → State → Prop) {Q : State → Prop} (hstep : 0 < step) (hk : 0 < k) (hk32 : step * k < 2 ^ 32)
    (hf : ∀ j u u', P j u → Fupd u u' → P j u') (h0 : P 0 s)
    (hp0 : s.gpr p = A) (h9 : s.gpr .r9 = A + BitVec.ofNat 32 (step * k))
    (hbody : ∀ j < k, ∀ t, P j t → t.gpr p = A + BitVec.ofNat 32 (step * j) →
      t.gpr .r9 = A + BitVec.ofNat 32 (step * k) →
      WP isa (.block body) t fun u => P (j + 1) u ∧ u.gpr p = A + BitVec.ofNat 32 (step * (j + 1)) ∧
        u.gpr .r9 = A + BitVec.ofNat 32 (step * k))
    (hQ : ∀ u, P k u → u.gpr p = A + BitVec.ofNat 32 (step * k) → Q u) :
    WP isa (ptrLoop p body) s Q := by
  unfold ptrLoop
  refine WP.loop (M := isa) (fun m t => ∃ j, m = k - j ∧ j < k ∧ P j t ∧
      t.gpr p = A + BitVec.ofNat 32 (step * j) ∧ t.gpr .r9 = A + BitVec.ofNat 32 (step * k)) ?_ k s
    ⟨0, rfl, hk, h0, by rw [hp0, Nat.mul_zero]; exact (BitVec.add_zero _).symm, h9⟩
  rintro m t ⟨j, rfl, hj, pj, ej, e9⟩
  refine VG.Proof.X25519.Arm.WP.append (hbody j hj t pj ej e9) fun u ⟨pu, eu, e9u⟩ => ?_
  refine wp_cmp (op2_reg _ _) fun u₁ f₁ z₁ => WP.block_nil ?_
  have p₁ : P (j + 1) u₁ := hf _ _ _ pu f₁
  have eu₁ : u₁.gpr p = A + BitVec.ofNat 32 (step * (j + 1)) := by rw [f₁.gpr]; exact eu
  have e9₁ : u₁.gpr .r9 = A + BitVec.ofNat 32 (step * k) := by rw [f₁.gpr]; exact e9u
  have hjs : step * (j + 1) ≤ step * k := Nat.mul_le_mul_left _ hj
  rw [eu, e9u, sub_add_add, cmp_ofNat (by omega) hk32] at z₁
  by_cases hjk : j + 1 = k
  · have : step * (j + 1) = step * k := by rw [hjk]
    exact .inl ⟨by rw [eval_ne, z₁]; simp [this], hQ _ (hjk ▸ p₁) (by rw [eu₁, hjk])⟩
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, p₁, eu₁, e9₁⟩
    rw [eval_ne, z₁]
    have : step * (j + 1) ≠ step * k := fun e => hjk (Nat.eq_of_mul_eq_mul_left hstep e)
    simp [this]

end VG.Proof.Mont.Arm.Dyn

import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.TCB.X86.Target
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.X25519.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Basic`. -/
section

/-!
# X25519 on x86 (32-bit): words of the working space

The working space, `W` bytes at `x` (`edi` in the code), holds words at
constant offsets (X25519's has 4096 bytes, Ed25519's 8192: the proofs hold for
any `W ≥ 4096`); a field element is eight of them (`fe`). A store to a word
leaves the others unchanged, and code that stores only to some regions of it
leaves the rest of memory unchanged (`Frame`).
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

variable {W : Nat}

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 32-bit word at `[x + d]`. -/
abbrev wd (m : Mem) (x : BitVec 32) (d : Nat) : BitVec 32 := m.readW (VG.X86.addr x d) 32

/-- The same, as a number. -/
abbrev wv (m : Mem) (x : BitVec 32) (d : Nat) : Nat := (VG.Proof.X25519.X86.wd m x d).toNat

/-- The number of the words `f 0, …, f (n - 1)`, in radix `2³²`. -/
def num (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X25519.X86.num f n + (2 ^ 32) ^ n * f n

/-- The eight words of a field element at `[x + o]`, as a number. -/
def fe (m : Mem) (x : BitVec 32) (o : Nat) : Nat := VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv m x (o + 4 * k)) 8

/-- The region of `n` bytes at `[x + d]`. -/
abbrev sub (x : BitVec 32) (d n : Nat) : Region := ⟨VG.X86.addr x d, n⟩

/-- The working space, of `W` bytes. -/
abbrev scR (W : Nat) (x : BitVec 32) : Region := ⟨x.setWidth 64, W⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = VG.X86.addr (s.gpr b) d := rfl

theorem addr_zero (x : BitVec 32) : VG.X86.addr x 0 = x.setWidth 64 := by simp [VG.X86.addr]

theorem sub_contains {x : BitVec 32} {a k d n : Nat} (hx : x.toNat + a + k ≤ 2 ^ 32) (h₁ : a ≤ d)
    (h₂ : d + n ≤ a + k) (hn : 0 < n) : (VG.Proof.X25519.X86.sub x a k).Contains (VG.X86.addr x d) n := by
  rw [VG.Proof.X25519.X86.sub, addr_eq (by omega_using [hx, h₁, h₂, hn]), addr_eq (by omega_using [hx, h₂, hn])]
  exact Offset.contains _ h₁ h₂ (by omega_using [hx])

theorem sub_disj {x : BitVec 32} {d n e k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32)
    (he : x.toNat + e + k ≤ 2 ^ 32) (h : d + n ≤ e ∨ e + k ≤ d) : (VG.Proof.X25519.X86.sub x d n).Disjoint (VG.Proof.X25519.X86.sub x e k) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) h₁
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) h₂
  rw [addr_eq (by omega_using [hd, hn])] at h₁
  rw [addr_eq (by omega_using [he, hk])] at h₂
  exact Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he]) a h₁ h₂

theorem scR_eq (W : Nat) (x : BitVec 32) : VG.Proof.X25519.X86.scR W x = VG.Proof.X25519.X86.sub x 0 W := by rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero]

theorem scR_contains {x : BitVec 32} (hx : x.toNat + W ≤ 2 ^ 32) {d n : Nat} (h : d + n ≤ W)
    (hn : 0 < n) : (VG.Proof.X25519.X86.scR W x).Contains (VG.X86.addr x d) n := by
  rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_contains (by omega_using [hx]) (Nat.zero_le d) (by omega_using [h]) hn

/-- The 32-bit word at `[x + d]`, after a store at `[x + e]` that does not overlap it. -/
theorem wd_write_ne (m : Mem) {x : BitVec 32} (w : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    VG.Proof.X25519.X86.wd (m.writeW (VG.X86.addr x e) w) x d = VG.Proof.X25519.X86.wd m x d :=
  Mem.readW_writeW_sep ((VG.Proof.X25519.X86.sub_disj hd he h).sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by decide)

theorem wd_write_self (m : Mem) (x : BitVec 32) (w : BitVec 32) (d : Nat) :
    VG.Proof.X25519.X86.wd (m.writeW (VG.X86.addr x d) w) x d = w :=
  Mem.readW_writeW_self32 _ _ _

/-- A word outside the regions a frame allows to change. -/
theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : BitVec 32} {d : Nat}
    (hd : ∀ r ∈ rs, (VG.Proof.X25519.X86.sub x d 4).Disjoint r) : VG.Proof.X25519.X86.wd m' x d = VG.Proof.X25519.X86.wd m x d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- A word of the working space outside a frame's region `[x + o, x + o + n)`. -/
theorem wd_frame1 {m m' : Mem} {x : BitVec 32} {o n d : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + W ≤ 2 ^ 32) (ho : o + n ≤ W) (hd : d + 4 ≤ W) (h : d + 4 ≤ o ∨ o + n ≤ d) :
    VG.Proof.X25519.X86.wd m' x d = VG.Proof.X25519.X86.wd m x d :=
  VG.Proof.X25519.X86.wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hd]) (by omega_using [hx, ho]) h

/-- Stores into a frame's region. -/
theorem frame_write1 {m m' : Mem} {x : BitVec 32} {o n : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + W ≤ 2 ^ 32) (ho : o + n ≤ W) {d : Nat} (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n)
    (w : BitVec 32) : Frame [VG.Proof.X25519.X86.sub x o n] m (m'.writeW (VG.X86.addr x d) w) :=
  hf.writeW (List.mem_singleton_self _) _
    (VG.Proof.X25519.X86.sub_contains (by omega_using [hx, ho]) h₁ h₂ (by decide))

/-- A region of the working space within another. -/
theorem sub_sub {x : BitVec 32} {o n o' n' : Nat} (hx : x.toNat + W ≤ 2 ^ 32) (h₁ : o' ≤ o)
    (h₂ : o + n ≤ o' + n') (hn : o < W) : Region.Sub (VG.Proof.X25519.X86.sub x o n) (VG.Proof.X25519.X86.sub x o' n') := by
  rw [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.sub, addr_eq (by omega_using [hx, hn]), addr_eq (by omega_using [hx, h₁, hn])]
  exact Offset.sub _ h₁ h₂

/-- A frame of a region is one of any region containing it. -/
theorem frameWiden {m m' : Mem} {x : BitVec 32} {o n o' n' : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + W ≤ 2 ^ 32) (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n')
    (hn : o < W) : Frame [VG.Proof.X25519.X86.sub x o' n'] m m' :=
  hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, List.mem_singleton.mp hr ▸ VG.Proof.X25519.X86.sub_sub hx h₁ h₂ hn⟩

/-- The code's view of the working space: `edi` points at it, it is
writable, and it does not wrap around the 32-bit address space. -/
structure Ctx (W : Nat) (x : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = x
  fit : x.toNat + W ≤ 2 ^ 32
  wr : VG.Proof.X25519.X86.scR W x ∈ s.wr
  room : 4096 ≤ W

namespace Ctx
variable {x : BitVec 32} {s : State} (h : VG.Proof.X25519.X86.Ctx W x s)
include h

theorem inW {d n : Nat} (hd : d + n ≤ W) (hn : 0 < n) : InRegions s.wr (VG.X86.addr x d) n :=
  ⟨_, h.wr, VG.Proof.X25519.X86.scR_contains h.fit hd hn⟩

theorem inRW {d n : Nat} (hd : d + n ≤ W) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (VG.X86.addr x d) n :=
  ⟨_, List.mem_append_right _ h.wr, VG.Proof.X25519.X86.scR_contains h.fit hd hn⟩

/-- The working space's first 4096 bytes, all the field arithmetic uses. -/
theorem fit4 : x.toNat + 4096 ≤ 2 ^ 32 := Nat.le_trans (Nat.add_le_add_left h.room _) h.fit

theorem inW4 {d n : Nat} (hd : d + n ≤ 4096) (hn : 0 < n) : InRegions s.wr (VG.X86.addr x d) n :=
  h.inW (Nat.le_trans hd h.room) hn

theorem inRW4 {d n : Nat} (hd : d + n ≤ 4096) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (VG.X86.addr x d) n :=
  h.inRW (Nat.le_trans hd h.room) hn

/-- The context survives a change of other registers and of memory. -/
theorem keep {s' : State} (he : s'.gpr .edi = s.gpr .edi) (hw : s'.wr = s.wr) : VG.Proof.X25519.X86.Ctx W x s' :=
  ⟨he.trans h.edi, h.fit, hw ▸ h.wr, h.room⟩

end Ctx

/-- What the arithmetic keeps: the counter `esi`, the base `edi`, `esp` and
the regions. -/
structure Keep (s s' : State) : Prop where
  esi : s'.gpr .esi = s.gpr .esi
  edi : s'.gpr .edi = s.gpr .edi
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : VG.Proof.X25519.X86.Keep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.X86.Keep s₁ s₂) (h₂ : VG.Proof.X25519.X86.Keep s₂ s₃) : VG.Proof.X25519.X86.Keep s₁ s₃ :=
  ⟨h₂.esi.trans h₁.esi, h₂.edi.trans h₁.edi, h₂.esp.trans h₁.esp, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem Keep.ctx {x : BitVec 32} {s s' : State} (h : VG.Proof.X25519.X86.Keep s s') (hc : VG.Proof.X25519.X86.Ctx W x s) : VG.Proof.X25519.X86.Ctx W x s' :=
  hc.keep h.edi h.wr

/-! ## Numbers of words -/

theorem num_succ (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num f (n + 1) = VG.Proof.X25519.X86.num f n + (2 ^ 32) ^ n * f n := rfl

theorem num_congr {f g : Nat → Nat} {n : Nat} (h : ∀ k < n, f k = g k) : VG.Proof.X25519.X86.num f n = VG.Proof.X25519.X86.num g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, ih fun k hk => h k (by omega_using [hk]), h n (by omega_using [])]

theorem num_lt {f : Nat → Nat} {n : Nat} (h : ∀ k < n, f k < 2 ^ 32) : VG.Proof.X25519.X86.num f n < (2 ^ 32) ^ n := by
  induction n with
  | zero => simp [VG.Proof.X25519.X86.num]
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ]
    have h1 := ih fun k hk => h k (by omega_using [hk])
    have h2 : f n + 1 ≤ 2 ^ 32 := h n (by omega_using [])
    have h3 : (2 ^ 32) ^ n * (f n + 1) ≤ (2 ^ 32) ^ n * 2 ^ 32 := Nat.mul_le_mul_left _ h2
    rw [← Nat.pow_succ] at h3
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega_using [h1, h3]

theorem num_add (f g : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num (fun k => f k + g k) n = VG.Proof.X25519.X86.num f n + VG.Proof.X25519.X86.num g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, ih, Nat.mul_add]; omega_using []

theorem num_mul (c : Nat) (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num (fun k => c * f k) n = c * VG.Proof.X25519.X86.num f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, ih, Nat.mul_add, Nat.mul_left_comm]

theorem fe_lt (m : Mem) (x : BitVec 32) (o : Nat) : VG.Proof.X25519.X86.fe m x o < 2 ^ 256 :=
  VG.Proof.X25519.X86.num_lt (f := fun k => VG.Proof.X25519.X86.wv m x (o + 4 * k)) fun _ _ => BitVec.isLt _

/-- A field element's words are unchanged if their region is. -/
theorem fe_frame {m m' : Mem} {x : BitVec 32} {o : Nat} (h : ∀ k < 8, VG.Proof.X25519.X86.wd m' x (o + 4 * k) = VG.Proof.X25519.X86.wd m x (o + 4 * k)) :
    VG.Proof.X25519.X86.fe m' x o = VG.Proof.X25519.X86.fe m x o :=
  VG.Proof.X25519.X86.num_congr fun k hk => by show (VG.Proof.X25519.X86.wd m' x (o + 4 * k)).toNat = (VG.Proof.X25519.X86.wd m x (o + 4 * k)).toNat; rw [h k hk]

/-- A field element outside a frame's region. -/
theorem fe_frame1 {m m' : Mem} {x : BitVec 32} {o n q : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + W ≤ 2 ^ 32) (ho : o + n ≤ W) (hq : q + 32 ≤ W) (h : q + 32 ≤ o ∨ o + n ≤ q) :
    VG.Proof.X25519.X86.fe m' x q = VG.Proof.X25519.X86.fe m x q :=
  VG.Proof.X25519.X86.fe_frame fun k hk => VG.Proof.X25519.X86.wd_frame1 hf hx ho (by omega_using [hq, hk]) (by omega_using [h, hk])

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Column`. -/
section

/-!
# X25519 on x86 (32-bit): columns

Each term of a column adds its value to the 96-bit accumulator `ebx + 2³² ecx +
2⁶⁴ ebp` (`acc`), as long as the sum fits; the end of a column stores the
accumulator's low word and shifts it down. `cols_ok` sums `n` columns into `n`
words and a carry, when no column reads a word an earlier one stored.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

variable {W : Nat}

/-- The accumulator `ebx + 2³² ecx + 2⁶⁴ ebp`. -/
abbrev acc (s : State) : Nat := VG.Proof.X25519.X86.v s .ebx + 2 ^ 32 * VG.Proof.X25519.X86.v s .ecx + 2 ^ 64 * VG.Proof.X25519.X86.v s .ebp

/-- The value of a term, for the working space at `x`. -/
def tval (m : Mem) (x : BitVec 32) : Term → Nat
  | .mulM a b => VG.Proof.X25519.X86.wv m x a * VG.Proof.X25519.X86.wv m x b
  | .mulM2 a b => 2 * (VG.Proof.X25519.X86.wv m x a * VG.Proof.X25519.X86.wv m x b)
  | .mulI a c => VG.Proof.X25519.X86.wv m x a * c.toNat
  | .addM a => VG.Proof.X25519.X86.wv m x a
  | .addI c => c.toNat
  | .addNot a => 2 ^ 32 - 1 - VG.Proof.X25519.X86.wv m x a

/-- The offsets of the words a term reads. -/
def treads : Term → List Nat
  | .mulM a b => [a, b]
  | .mulM2 a b => [a, b]
  | .mulI a _ => [a]
  | .addM a => [a]
  | .addI _ => []
  | .addNot a => [a]

/-- The value of a column. -/
def colv (m : Mem) (x : BitVec 32) (ts : List Term) : Nat := (ts.map (VG.Proof.X25519.X86.tval m x)).sum

theorem tval_congr {m m' : Mem} {x : BitVec 32} {t : Term} (h : ∀ d ∈ VG.Proof.X25519.X86.treads t, VG.Proof.X25519.X86.wd m' x d = VG.Proof.X25519.X86.wd m x d) :
    VG.Proof.X25519.X86.tval m' x t = VG.Proof.X25519.X86.tval m x t := by
  cases t with
  | mulM a b => simp only [VG.Proof.X25519.X86.tval, VG.Proof.X25519.X86.wv, h a (by simp [VG.Proof.X25519.X86.treads]), h b (by simp [VG.Proof.X25519.X86.treads])]
  | mulM2 a b => simp only [VG.Proof.X25519.X86.tval, VG.Proof.X25519.X86.wv, h a (by simp [VG.Proof.X25519.X86.treads]), h b (by simp [VG.Proof.X25519.X86.treads])]
  | mulI a c => simp only [VG.Proof.X25519.X86.tval, VG.Proof.X25519.X86.wv, h a (by simp [VG.Proof.X25519.X86.treads])]
  | addM a => simp only [VG.Proof.X25519.X86.tval, VG.Proof.X25519.X86.wv, h a (by simp [VG.Proof.X25519.X86.treads])]
  | addI c => rfl
  | addNot a => simp only [VG.Proof.X25519.X86.tval, VG.Proof.X25519.X86.wv, h a (by simp [VG.Proof.X25519.X86.treads])]

theorem colv_congr {m m' : Mem} {x : BitVec 32} {ts : List Term}
    (h : ∀ t ∈ ts, ∀ d ∈ VG.Proof.X25519.X86.treads t, VG.Proof.X25519.X86.wd m' x d = VG.Proof.X25519.X86.wd m x d) : VG.Proof.X25519.X86.colv m' x ts = VG.Proof.X25519.X86.colv m x ts := by
  simp only [VG.Proof.X25519.X86.colv]
  congr 1
  exact List.map_congr_left fun t ht => VG.Proof.X25519.X86.tval_congr (h t ht)

/-! ## Arithmetic -/

theorem carry_toNat {n : Nat} (h : n < 2 ^ 33) : (decide (2 ^ 32 ≤ n)).toNat = n / 2 ^ 32 := by
  by_cases h' : 2 ^ 32 ≤ n
  · simp only [h', decide_true, Bool.toNat_true]; omega_using [h, h']
  · simp only [h', decide_false, Bool.toNat_false]; omega_using [h']

theorem add3_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  cases c <;> rfl

/-- The accumulator after adding `x0 + 2³² x1` word by word, with carries. -/
theorem acc3 {a b c x0 x1 : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h0 : x0 < 2 ^ 32) (h1 : x1 < 2 ^ 32)
    (h : a + 2 ^ 32 * b + 2 ^ 64 * c + (x0 + 2 ^ 32 * x1) < 2 ^ 96) :
    (a + x0) % 2 ^ 32 + 2 ^ 32 * ((b + x1 + (a + x0) / 2 ^ 32) % 2 ^ 32) +
      2 ^ 64 * ((c + (b + x1 + (a + x0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) =
      a + 2 ^ 32 * b + 2 ^ 64 * c + (x0 + 2 ^ 32 * x1) := by
  generalize e₁ : (a + x0) / 2 ^ 32 = c₁
  have k₁ := Nat.div_add_mod (a + x0) (2 ^ 32)
  have l₁ : (a + x0) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [e₁] at k₁
  have hc₁ : c₁ ≤ 1 := by omega_using [k₁, ha, h0]
  generalize e₂ : (b + x1 + c₁) / 2 ^ 32 = c₂
  have k₂ := Nat.div_add_mod (b + x1 + c₁) (2 ^ 32)
  have l₂ : (b + x1 + c₁) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [e₂] at k₂
  have hc₂ : c₂ ≤ 1 := by omega_using [k₂, hb, h1, hc₁]
  have k₃ := Nat.div_add_mod (c + c₂) (2 ^ 32)
  have l₃ : (c + c₂) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  generalize (c + c₂) % 2 ^ 32 = r₃ at *
  generalize (c + c₂) / 2 ^ 32 = q₃ at *
  generalize (a + x0) % 2 ^ 32 = r₁ at *
  generalize (b + x1 + c₁) % 2 ^ 32 = r₂ at *
  omega_using [k₁, k₂, k₃, h, l₁, l₂, l₃]

/-! ## The steps of a column -/

/-- Reads the registers, memory and regions of a state after writes, for
literal registers. -/
macro "regupd" : tactic => `(tactic| simp (config := {decide := true}) only [acc, v,
  RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
  RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags,
  RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false])


theorem toNat_zero32 : (0 : BitVec 32).toNat = 0 := rfl

theorem readSrc_imm (s : State) (w : BitVec 32) : VG.X86.readSrc s (.imm w) = some w := rfl
theorem readSrc_reg (s : State) (r : Reg) : VG.X86.readSrc s (.reg r) = some (s.gpr r) := rfl


/-- What a column's code leaves: `esi`, `edi`, `esp` and the regions. -/
theorem accAdd_ok {s : State} {src : Src} {x : BitVec 32} (hx : VG.X86.readSrc s src = some x) :
    WP isa (.block (accAdd src)) s fun s' =>
      (VG.Proof.X25519.X86.acc s + x.toNat < 2 ^ 96 → VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s + x.toNat) ∧ VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [accAdd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hx, VG.Proof.X25519.X86.readSrc_imm,
    Option.bind_some, Option.map_some, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun hlt => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> regupd
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt; have hc := (s.gpr .ebp).isLt
  have hx' := x.isLt
  simp only [VG.Proof.X25519.X86.add3_toNat, VG.Proof.X25519.X86.toNat_zero32, Nat.add_zero]
  simp only [BitVec.toNat_add]
  rw [VG.Proof.X25519.X86.carry_toNat (by omega_using [ha, hx']), VG.Proof.X25519.X86.carry_toNat (by omega_using [hb, ha, hx'])]
  have := VG.Proof.X25519.X86.acc3 (c := (s.gpr .ebp).toNat) (x1 := 0) ha hb hx' (by decide) (by omega_using [hlt])
  simp only [Nat.add_zero, Nat.mul_zero] at this
  exact this

theorem toNat_mul_lo (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat * b.toNat)).toNat +
      2 ^ 32 * (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = a.toNat * b.toNat := by
  have := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 32) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])]
  omega_using []

theorem accMul_ok {s : State} {src : Src} {y : BitVec 32} (hy : VG.X86.readSrc s src = some y) :
    WP isa (.block (accMul src)) s fun s' =>
      (VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.v s .eax * y.toNat < 2 ^ 96 → VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.v s .eax * y.toNat) ∧ VG.Proof.X25519.X86.Keep s s' ∧
        s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [accMul, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul, hy,
    VG.Proof.X25519.X86.readSrc_imm, VG.Proof.X25519.X86.readSrc_reg, Option.bind_some, Option.map_some, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨fun hlt => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> regupd
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at hlt
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt
  have e := VG.Proof.X25519.X86.toNat_mul_lo (s.gpr .eax) y
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat)) = lo at *
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat / 2 ^ 32)) = hi at *
  have hl := lo.isLt; have hh := hi.isLt
  simp only [VG.Proof.X25519.X86.add3_toNat, VG.Proof.X25519.X86.toNat_zero32, Nat.add_zero]
  simp only [BitVec.toNat_add]
  rw [VG.Proof.X25519.X86.carry_toNat (by omega_using [ha, hl]), VG.Proof.X25519.X86.carry_toNat (by omega_using [hb, hh, ha, hl])]
  have := VG.Proof.X25519.X86.acc3 (c := (s.gpr .ebp).toNat) ha hb hl hh (by omega_using [hlt, e])
  rw [← e]
  exact this

theorem ofBool_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by
  cases c <;> rfl

theorem accMul2_ok {s : State} {src : Src} {y : BitVec 32} (hy : VG.X86.readSrc s src = some y) :
    WP isa (.block (accMul2 src)) s fun s' =>
      (VG.Proof.X25519.X86.acc s + 2 * (VG.Proof.X25519.X86.v s .eax * y.toNat) < 2 ^ 96 → VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s + 2 * (VG.Proof.X25519.X86.v s .eax * y.toNat)) ∧
        VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [accMul2, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul, hy,
    VG.Proof.X25519.X86.readSrc_imm, VG.Proof.X25519.X86.readSrc_reg, Option.bind_some, Option.map_some, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨fun hlt => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> regupd
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at hlt
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt; have hc := (s.gpr .ebp).isLt
  have e := VG.Proof.X25519.X86.toNat_mul_lo (s.gpr .eax) y
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat)) = lo at *
  generalize (BitVec.ofNat 32 ((s.gpr .eax).toNat * y.toNat / 2 ^ 32)) = hi at *
  have hl := lo.isLt; have hh := hi.isLt
  simp only [BitVec.toNat_add, VG.Proof.X25519.X86.toNat_zero32, Nat.add_zero, VG.Proof.X25519.X86.ofBool_toNat]
  simp (disch := omega) only [VG.Proof.X25519.X86.carry_toNat]
  rw [← e]
  generalize lo.toNat = l at *
  generalize hi.toNat = h at *
  omega

open VG.X86.Wp in
theorem readSrc_sc {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {d : Nat} (hd : d + 4 ≤ 4096) :
    VG.X86.readSrc s (.mem (sc d)) = some (VG.Proof.X25519.X86.wd s.mem x d) :=
  readSrc_mem hc.edi (hc.inRW4 hd (by decide))

theorem updKeep {s s' : State} {d : Reg} {w : BitVec 32} (h : Wp.Upd s s' d w)
    (hd : d ≠ .esi ∧ d ≠ .edi ∧ d ≠ .esp := by decide) : VG.Proof.X25519.X86.Keep s s' :=
  ⟨h.other _ hd.1.symm, h.other _ hd.2.1.symm, h.other _ hd.2.2.symm, h.rd, h.wr⟩

theorem updAcc {s s' : State} {w : BitVec 32} (h : Wp.Upd s s' .eax w) : VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s := by
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, h.other .ebx (by decide), h.other .ecx (by decide), h.other .ebp (by decide)]

theorem xor_ones_toNat (w : BitVec 32) : (w ^^^ 0xffffffff).toNat = 2 ^ 32 - 1 - w.toNat := by
  rw [show (0xffffffff : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes, BitVec.toNat_not]

open VG.X86.Wp in
theorem term_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) (t : Term) (hr : ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ 4096) :
    WP isa (.block (Term.code t)) s fun s' =>
      (VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.tval s.mem x t < 2 ^ 96 → VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.tval s.mem x t) ∧ VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem := by
  cases t with
  | mulM a b =>
    have ha := hr a (by simp [VG.Proof.X25519.X86.treads]); have hb := hr b (by simp [VG.Proof.X25519.X86.treads])
    refine wp_ldm hc.edi (hc.inRW4 ha (by decide)) fun s₁ u₁ => ?_
    have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
    refine WP.mono (VG.Proof.X25519.X86.accMul_ok (VG.Proof.X25519.X86.readSrc_sc c₁ hb)) fun s' ⟨h, k, m⟩ => ⟨fun hlt => ?_, (VG.Proof.X25519.X86.updKeep u₁).trans k,
      m.trans u₁.mem⟩
    rw [h (by rw [VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr, u₁.mem]; exact hlt), VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr, u₁.mem]; rfl
  | mulM2 a b =>
    have ha := hr a (by simp [VG.Proof.X25519.X86.treads]); have hb := hr b (by simp [VG.Proof.X25519.X86.treads])
    refine wp_ldm hc.edi (hc.inRW4 ha (by decide)) fun s₁ u₁ => ?_
    have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
    refine WP.mono (VG.Proof.X25519.X86.accMul2_ok (VG.Proof.X25519.X86.readSrc_sc c₁ hb)) fun s' ⟨h, k, m⟩ => ⟨fun hlt => ?_, (VG.Proof.X25519.X86.updKeep u₁).trans k,
      m.trans u₁.mem⟩
    rw [h (by rw [VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr, u₁.mem]; exact hlt), VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr, u₁.mem]; rfl
  | mulI a c =>
    have ha := hr a (by simp [VG.Proof.X25519.X86.treads])
    refine wp_ldm hc.edi (hc.inRW4 ha (by decide)) fun s₁ u₁ => ?_
    refine WP.mono (VG.Proof.X25519.X86.accMul_ok (VG.Proof.X25519.X86.readSrc_imm s₁ c)) fun s' ⟨h, k, m⟩ => ⟨fun hlt => ?_, (VG.Proof.X25519.X86.updKeep u₁).trans k,
      m.trans u₁.mem⟩
    rw [h (by rw [VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr]; exact hlt), VG.Proof.X25519.X86.updAcc u₁, VG.Proof.X25519.X86.v, u₁.gpr]; rfl
  | addM a =>
    have ha := hr a (by simp [VG.Proof.X25519.X86.treads])
    exact VG.Proof.X25519.X86.accAdd_ok (VG.Proof.X25519.X86.readSrc_sc hc ha)
  | addI c => exact VG.Proof.X25519.X86.accAdd_ok (VG.Proof.X25519.X86.readSrc_imm s c)
  | addNot a =>
    have ha := hr a (by simp [VG.Proof.X25519.X86.treads])
    refine wp_ldm hc.edi (hc.inRW4 ha (by decide)) fun s₁ u₁ => ?_
    refine Wp.cons (s' := (arithFlags s₁ (s₁.gpr .eax ^^^ 0xffffffff) false false).setReg .eax
      (s₁.gpr .eax ^^^ 0xffffffff)) rfl ?_
    have u₂ := Upd.flags s₁ .eax (s₁.gpr .eax ^^^ 0xffffffff) false false (s₁.gpr .eax ^^^ 0xffffffff)
    refine WP.mono (VG.Proof.X25519.X86.accAdd_ok (VG.Proof.X25519.X86.readSrc_reg _ .eax)) fun s' ⟨h, k, m⟩ =>
      ⟨fun hlt => ?_, (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans k), m.trans (u₂.mem.trans u₁.mem)⟩
    have e : (((arithFlags s₁ (s₁.gpr .eax ^^^ 0xffffffff) false false).setReg .eax
        (s₁.gpr .eax ^^^ 0xffffffff)).gpr .eax).toNat = VG.Proof.X25519.X86.tval s.mem x (.addNot a) := by
      rw [u₂.gpr, u₁.gpr, VG.Proof.X25519.X86.xor_ones_toNat]; rfl
    rw [e] at h
    rw [h (by rw [(VG.Proof.X25519.X86.updAcc u₂), (VG.Proof.X25519.X86.updAcc u₁)]; exact hlt), (VG.Proof.X25519.X86.updAcc u₂), (VG.Proof.X25519.X86.updAcc u₁)]

theorem terms_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) (ts : List Term)
    (hr : ∀ t ∈ ts, ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ 4096) :
    WP isa (.block (ts.flatMap Term.code)) s fun s' =>
      (VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.colv s.mem x ts < 2 ^ 96 → VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.colv s.mem x ts) ∧ VG.Proof.X25519.X86.Keep s s' ∧
        s'.mem = s.mem := by
  induction ts generalizing s with
  | nil => exact WP.block_nil ⟨fun _ => by simp [VG.Proof.X25519.X86.colv], Keep.refl _, rfl⟩
  | cons t ts ih =>
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.term_ok hc t (hr t List.mem_cons_self)) fun s₁ ⟨h₁, k₁, m₁⟩ => ?_)
    refine WP.mono (ih (k₁.ctx hc) fun t' ht' => hr t' (List.mem_cons_of_mem _ ht'))
      fun s₂ ⟨h₂, k₂, m₂⟩ => ⟨fun hlt => ?_, k₁.trans k₂, m₂.trans m₁⟩
    simp only [VG.Proof.X25519.X86.colv, List.map_cons, List.sum_cons] at hlt ⊢
    rw [m₁] at h₂
    simp only [VG.Proof.X25519.X86.colv] at h₂
    rw [h₂ (by rw [h₁ (by omega_using [hlt])]; omega_using [hlt]), h₁ (by omega_using [hlt])]
    omega_using []

open VG.X86.Wp in
theorem colEnd_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o : Nat} (ho : o + 4 ≤ 4096) :
    WP isa (.block (colEnd o)) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem.writeW (VG.X86.addr x o) (s.gpr .ebx) ∧ VG.Proof.X25519.X86.acc s' = VG.Proof.X25519.X86.acc s / 2 ^ 32 := by
  refine wp_stm hc.edi (hc.inW4 ho (by decide)) fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have k₁ : VG.Proof.X25519.X86.Keep s s₁ := ⟨by rw [u₁.gpr], by rw [u₁.gpr], by rw [u₁.gpr], u₁.rd, u₁.wr⟩
  refine ⟨k₁.trans ((VG.Proof.X25519.X86.updKeep u₂).trans ((VG.Proof.X25519.X86.updKeep u₃).trans (VG.Proof.X25519.X86.updKeep u₄))), by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₄.gpr, u₄.other .ebx (by decide), u₄.other .ecx (by decide), u₃.gpr,
    u₃.other .ebx (by decide), u₂.gpr, u₂.other .ebp (by decide), u₁.gpr, VG.Proof.X25519.X86.toNat_zero32, Nat.mul_zero,
    Nat.add_zero]
  have := (s.gpr .ebx).isLt
  omega_using [this]

theorem column_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) (ts : List Term) {o : Nat}
    (hr : ∀ t ∈ ts, ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ 4096) (ho : o + 4 ≤ 4096)
    (hlt : VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.colv s.mem x ts < 2 ^ 96) :
    WP isa (.block (column ts o)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 4] s.mem s'.mem ∧
      VG.Proof.X25519.X86.wv s'.mem x o = (VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.colv s.mem x ts) % 2 ^ 32 ∧
      VG.Proof.X25519.X86.acc s' = (VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.colv s.mem x ts) / 2 ^ 32 := by
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.terms_ok hc ts hr) fun s₁ ⟨h₁, k₁, m₁⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.X86.colEnd_ok (k₁.ctx hc) ho) fun s₂ ⟨k₂, m₂, h₂⟩ =>
    ⟨k₁.trans k₂, ?_, ?_, by rw [h₂, h₁ hlt]⟩
  · rw [m₂, m₁]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit4 ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [m₂, VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd_write_self, ← h₁ hlt]
    have := (s₁.gpr .ecx).isLt; have := (s₁.gpr .ebp).isLt
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v]
    omega_using []

theorem cols_zero (o : Nat) (ts : Nat → List Term) : cols o 0 ts = [] := rfl

theorem cols_succ (o n : Nat) (ts : Nat → List Term) :
    cols o (n + 1) ts = cols o n ts ++ column (ts n) (o + 4 * n) := by
  simp only [cols, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- `P r + P 2³² q = P x` for the remainder `r` and quotient `q` of `x` by `2³²`. -/
theorem digit_step (P x : Nat) : P * (x % 2 ^ 32) + P * 2 ^ 32 * (x / 2 ^ 32) = P * x := by
  rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]

/-- `n` columns at `[x + o]`: their words and the carry are the sum of the
columns' values (with the accumulator's value on entry), as long as each
column reads no word an earlier one stored. -/
theorem cols_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o : Nat} (ts : Nat → List Term) :
    ∀ n, o + 4 * n ≤ 4096 →
    (∀ k < n, ∀ t ∈ ts k, ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ 4096 ∧ (d + 4 ≤ o ∨ o + 4 * k ≤ d)) →
    (∀ k < n, VG.Proof.X25519.X86.colv s.mem x (ts k) < 2 ^ 68) → VG.Proof.X25519.X86.acc s < 2 ^ 40 →
    WP isa (.block (cols o n ts)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s.mem s'.mem ∧
      VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s'.mem x (o + 4 * k)) n + (2 ^ 32) ^ n * VG.Proof.X25519.X86.acc s' =
        VG.Proof.X25519.X86.acc s + VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x (ts k)) n ∧ VG.Proof.X25519.X86.acc s' < 2 ^ 40
  | 0, _, _, _, ha => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, by simp [VG.Proof.X25519.X86.num], ha⟩
  | n + 1, ho, hr, hb, ha => by
    rw [VG.Proof.X25519.X86.cols_succ]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cols_ok hc ts n (by omega_using [ho])
      (fun k hk => hr k (by omega_using [hk])) (fun k hk => hb k (by omega_using [hk])) ha)
      fun s₁ ⟨k₁, f₁, e₁, a₁⟩ => ?_)
    have hfit := hc.fit4
    have hV : VG.Proof.X25519.X86.colv s₁.mem x (ts n) = VG.Proof.X25519.X86.colv s.mem x (ts n) := VG.Proof.X25519.X86.colv_congr fun t ht d hd =>
      VG.Proof.X25519.X86.wd_frame1 f₁ hfit (by omega_using [ho]) (hr n (by omega_using []) t ht d hd).1
        (hr n (by omega_using []) t ht d hd).2
    have hb' := hb n (by omega_using [])
    refine WP.mono (VG.Proof.X25519.X86.column_ok (k₁.ctx hc) (ts n) (fun t ht d hd => (hr n (by omega_using []) t ht d hd).1)
      (by omega_using [ho]) (by rw [hV]; omega_using [a₁, hb'])) fun s₂ ⟨k₂, f₂, w₂, a₂⟩ =>
      ⟨k₁.trans k₂, ?_, ?_, ?_⟩
    · exact (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho])).trans
        (VG.Proof.X25519.X86.frameWiden f₂ hfit (by omega_using []) (by omega_using []) (by omega_using [ho]))
    · have hw : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₂.mem x (o + 4 * k)) n = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₁.mem x (o + 4 * k)) n :=
        VG.Proof.X25519.X86.num_congr fun k hk => by
          show (VG.Proof.X25519.X86.wd s₂.mem x (o + 4 * k)).toNat = (VG.Proof.X25519.X86.wd s₁.mem x (o + 4 * k)).toNat
          rw [VG.Proof.X25519.X86.wd_frame1 f₂ hfit (by omega_using [ho]) (by omega_using [ho, hk]) (by omega_using [hk])]
      rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, hw, w₂, a₂, hV, Nat.add_assoc, Nat.pow_succ (2 ^ 32) n,
        VG.Proof.X25519.X86.digit_step, Nat.mul_add, ← Nat.add_assoc, e₁, Nat.add_assoc]
    · rw [a₂, hV]; omega_using [a₁, hb']

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Fold`. -/
section

/-!
# X25519 on x86 (32-bit): folding a carry, and linear combinations

`fold` adds `38 c` for the carry `c` in the accumulator (as `2²⁵⁶ ≡ 38` modulo
`p`), which leaves a carry of at most 1, added as 38 more to the lowest word,
which cannot carry again. `linear_ok`: an element summed by eight columns and
folded is their sum modulo `p`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

variable {W : Nat}

/-- `mul r`: `edx:eax = eax · r`, the other registers, memory and regions kept. -/
structure MulUpd (s s' : State) (r : Reg) : Prop where
  eax : VG.Proof.X25519.X86.v s' .eax = (VG.Proof.X25519.X86.v s .eax * VG.Proof.X25519.X86.v s r) % 2 ^ 32
  edx : VG.Proof.X25519.X86.v s' .edx = (VG.Proof.X25519.X86.v s .eax * VG.Proof.X25519.X86.v s r) / 2 ^ 32
  other : ∀ q, q ≠ .eax → q ≠ .edx → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : ∀ s', VG.Proof.X25519.X86.MulUpd s s' r → WP isa (.block is) s' Q) : WP isa (.block (.mul r :: is)) s Q := by
  refine Wp.cons (s' := execMul r s) rfl (k _ ⟨?_, ?_, fun q h₁ h₂ => ?_, rfl, rfl, rfl⟩)
  · simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, execMul, VG.Proof.X25519.X86.v, RegUpd.gpr_setReg,
      BitVec.toNat_ofNat]
  · simp only [execMul, VG.Proof.X25519.X86.v, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, BitVec.toNat_ofNat, ite_true]
    have := Nat.mul_lt_mul_of_lt_of_lt (s.gpr .eax).isLt (s.gpr r).isLt
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])
  · simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, h₁, h₂, ite_false]

theorem MulUpd.keep {s s' : State} {r : Reg} (h : VG.Proof.X25519.X86.MulUpd s s' r) : VG.Proof.X25519.X86.Keep s s' :=
  ⟨h.other _ (by decide) (by decide), h.other _ (by decide) (by decide), h.other _ (by decide) (by decide),
    h.rd, h.wr⟩

/-- The accumulator's three words, when it is less than `2³²`. -/
theorem acc_small {s : State} {c : Nat} (h : VG.Proof.X25519.X86.acc s = c) (hc : c < 2 ^ 32) :
    VG.Proof.X25519.X86.v s .ebx = c ∧ VG.Proof.X25519.X86.v s .ecx = 0 ∧ VG.Proof.X25519.X86.v s .ebp = 0 := by
  simp only [VG.Proof.X25519.X86.acc] at h
  omega_using [h, hc]

/-- `num` with its lowest digit increased by `d`. -/
theorem num_add0 {f g : Nat → Nat} {n d : Nat} (hn : 1 ≤ n) (h0 : g 0 = f 0 + d)
    (h : ∀ k, 1 ≤ k → k < n → g k = f k) : VG.Proof.X25519.X86.num g n = VG.Proof.X25519.X86.num f n + d := by
  induction n with
  | zero => omega_using [hn]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [VG.Proof.X25519.X86.num, Nat.pow_zero, Nat.one_mul, Nat.zero_add, h0]
    · rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.num_succ, ih hpos fun k h₁ h₂ => h k h₁ (by omega_using [h₂]),
        h n hpos (by omega_using [])]
      omega_using []

theorem le_num {f : Nat → Nat} {n : Nat} (hn : 1 ≤ n) : f 0 ≤ VG.Proof.X25519.X86.num f n := by
  induction n with
  | zero => omega_using [hn]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [VG.Proof.X25519.X86.num, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.le_refl]
    · rw [VG.Proof.X25519.X86.num_succ]; have := ih hpos; omega_using [this]

theorem toNat_38 : (38 : BitVec 32).toNat = 38 := rfl

theorem head_ok {s : State} {c : Nat} (hc : VG.Proof.X25519.X86.acc s = c) (hc' : c < 2 ^ 26) :
    WP isa (.block [.mov .eax (.imm 38), .mul .ebx, .mov .ebx (.reg .eax)]) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem ∧ VG.Proof.X25519.X86.acc s' = 38 * c := by
  obtain ⟨hb, hcx, hbp⟩ := VG.Proof.X25519.X86.acc_small hc (by omega_using [hc'])
  refine Wp.wp_movi fun s₁ u₁ => VG.Proof.X25519.X86.wp_mul fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep u₁).trans (u₂.keep.trans (VG.Proof.X25519.X86.updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  have e₂ : VG.Proof.X25519.X86.v s₂ .eax = 38 * c := by
    rw [u₂.eax, VG.Proof.X25519.X86.v, u₁.gpr, VG.Proof.X25519.X86.v, u₁.other _ (by decide), ← VG.Proof.X25519.X86.v, hb, VG.Proof.X25519.X86.toNat_38]
    exact Nat.mod_eq_of_lt (by omega_using [hc'])
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₃.gpr, u₃.other .ecx (by decide), u₃.other .ebp (by decide),
    u₂.other .ecx (by decide) (by decide), u₂.other .ebp (by decide) (by decide),
    u₁.other .ecx (by decide), u₁.other .ebp (by decide)]
  simp only [VG.Proof.X25519.X86.v] at e₂ hcx hbp
  rw [e₂, hcx, hbp]; omega_using []

theorem tail_ok {x : BitVec 32} {s : State} (hctx : VG.Proof.X25519.X86.Ctx W x s) {o c : Nat} (ho : o + 4 ≤ 4096)
    (hc : VG.Proof.X25519.X86.acc s = c) (hc' : c ≤ 1) (hw : VG.Proof.X25519.X86.wv s.mem x o + 38 * c < 2 ^ 32) :
    WP isa (.block [.mov .eax (.imm 38), .mul .ebx, .alu .add .eax (.mem (sc o)), .store (sc o) .eax]) s
      fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 4] s.mem s'.mem ∧ VG.Proof.X25519.X86.wv s'.mem x o = VG.Proof.X25519.X86.wv s.mem x o + 38 * c := by
  obtain ⟨hb, -, -⟩ := VG.Proof.X25519.X86.acc_small hc (by omega_using [hc'])
  refine Wp.wp_movi fun s₁ u₁ => VG.Proof.X25519.X86.wp_mul fun s₂ u₂ => ?_
  have c₂ := u₂.keep.ctx ((VG.Proof.X25519.X86.updKeep u₁).ctx hctx)
  refine Wp.wp_addm c₂.edi (c₂.inRW4 ho (by decide)) fun s₃ u₃ => ?_
  have c₃ := (VG.Proof.X25519.X86.updKeep u₃).ctx c₂
  refine Wp.wp_stm c₃.edi (c₃.inW4 ho (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨(VG.Proof.X25519.X86.updKeep u₁).trans (u₂.keep.trans ((VG.Proof.X25519.X86.updKeep u₃).trans ⟨by rw [u₄.gpr], by rw [u₄.gpr],
    by rw [u₄.gpr], u₄.rd, u₄.wr⟩)), ?_, ?_⟩
  · rw [u₄.mem, u₃.mem, m₂]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hctx.fit4 ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [u₄.mem, u₃.mem, u₃.gpr, m₂, VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd_write_self, BitVec.toNat_add]
    have e₂ : VG.Proof.X25519.X86.v s₂ .eax = 38 * c := by
      rw [u₂.eax, VG.Proof.X25519.X86.v, u₁.gpr, VG.Proof.X25519.X86.v, u₁.other _ (by decide), ← VG.Proof.X25519.X86.v, hb, VG.Proof.X25519.X86.toNat_38]
      exact Nat.mod_eq_of_lt (by omega_using [hc'])
    simp only [VG.Proof.X25519.X86.v] at e₂
    rw [e₂]
    simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at hw ⊢
    omega_using [hw]

/-- The fold of the carry `c < 2²⁶` in the accumulator into the element at
`[x + o]`. -/
theorem fold_ok {x : BitVec 32} {s : State} (hctx : VG.Proof.X25519.X86.Ctx W x s) {o c : Nat} (ho : o + 32 ≤ 4096)
    (hc : VG.Proof.X25519.X86.acc s = c) (hc' : c < 2 ^ 26) :
    WP isa (.block (fold o)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = (VG.Proof.X25519.X86.fe s.mem x o + 38 * c) % P := by
  have hfit := hctx.fit4
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.X25519.X86.head_ok hc hc') fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))
  have c₁ := k₁.ctx hctx
  refine WP.mono (VG.Proof.X25519.X86.cols_ok c₁ (fun k => [.addM (o + 4 * k)]) 8 ho (fun k hk t ht d hd => ?_)
    (fun k hk => ?_) (by rw [a₁]; omega_using [hc'])) fun s₂ ⟨k₂, f₂, e₂, a₂⟩ => ?_
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [ho, hk], .inr (Nat.le_refl _)⟩
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := BitVec.isLt (VG.Proof.X25519.X86.wd s₁.mem x (o + 4 * k)); simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢; omega_using [this]
  · -- The columns' sum is the element plus `38 c`, and the carry is at most 1.
    have hV : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s₁.mem x [.addM (o + 4 * k)]) 8 = VG.Proof.X25519.X86.fe s.mem x o := by
      rw [m₁]; simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]; rfl
    rw [hV, a₁] at e₂
    have hlt := VG.Proof.X25519.X86.fe_lt s.mem x o
    have hw := VG.Proof.X25519.X86.num_lt (f := fun k => VG.Proof.X25519.X86.wv s₂.mem x (o + 4 * k)) (n := 8) fun _ _ => BitVec.isLt _
    have h0 := VG.Proof.X25519.X86.le_num (f := fun k => VG.Proof.X25519.X86.wv s₂.mem x (o + 4 * k)) (n := 8) (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    generalize hW : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₂.mem x (o + 4 * k)) 8 = W at e₂ hw h0
    have hc2 : VG.Proof.X25519.X86.acc s₂ ≤ 1 := by
      rcases Nat.lt_or_ge (VG.Proof.X25519.X86.acc s₂) 2 with h | h
      · omega_using [h]
      · have : (2 ^ 32) ^ 8 * 2 ≤ (2 ^ 32) ^ 8 * VG.Proof.X25519.X86.acc s₂ := Nat.mul_le_mul_left _ h
        omega_using [this, e₂, hlt, hc']
    have hw0 : VG.Proof.X25519.X86.wv s₂.mem x o + 38 * VG.Proof.X25519.X86.acc s₂ < 2 ^ 32 := by
      rcases Nat.lt_or_ge (VG.Proof.X25519.X86.acc s₂) 1 with h | h
      · have := BitVec.isLt (VG.Proof.X25519.X86.wd s₂.mem x o); simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢; omega_using [h, this]
      · omega_using [h, hc2, e₂, hlt, hc', h0]
    refine WP.mono (VG.Proof.X25519.X86.tail_ok (k₂.ctx c₁) (by omega_using [ho]) rfl hc2 hw0) fun s₃ ⟨k₃, f₃, w₃⟩ =>
      ⟨k₁.trans (k₂.trans k₃), ?_, ?_⟩
    · rw [m₁] at f₂
      exact f₂.trans (VG.Proof.X25519.X86.frameWiden f₃ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho]))
    · have e₃ : VG.Proof.X25519.X86.fe s₃.mem x o = W + 38 * VG.Proof.X25519.X86.acc s₂ := by
        rw [← hW]
        refine VG.Proof.X25519.X86.num_add0 (by decide) (by simp only [Nat.mul_zero, Nat.add_zero]; exact w₃) fun k h₁ h₂ => ?_
        show (VG.Proof.X25519.X86.wd s₃.mem x (o + 4 * k)).toNat = (VG.Proof.X25519.X86.wd s₂.mem x (o + 4 * k)).toNat
        rw [VG.Proof.X25519.X86.wd_frame1 f₃ hfit (by omega_using [ho]) (by omega_using [ho, h₂]) (by omega_using [h₁])]
      rw [e₃, ← fold256 W (VG.Proof.X25519.X86.acc s₂), e₂, Nat.add_comm]

/-- An element summed by eight columns (reading no word an earlier one
stored) and folded: the sum of the columns modulo `p`. -/
theorem linear_ok {x : BitVec 32} {s : State} (hctx : VG.Proof.X25519.X86.Ctx W x s) (o : Nat) (ts : Nat → List Term)
    (ho : o + 32 ≤ 4096)
    (hr : ∀ k < 8, ∀ t ∈ ts k, ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ 4096 ∧ (d + 4 ≤ o ∨ o + 4 * k ≤ d))
    (hb : ∀ k < 8, VG.Proof.X25519.X86.colv s.mem x (ts k) < 2 ^ 68)
    (hV : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x (ts k)) 8 < 2 ^ 256 * 2 ^ 26) :
    WP isa (.block (linear o ts)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x (ts k)) 8 % P := by
  have hfit := hctx.fit4
  refine WP.block_append (WP.block_append ?_)
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  have k₃ : VG.Proof.X25519.X86.Keep s s₃ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans (VG.Proof.X25519.X86.updKeep u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have a₃ : VG.Proof.X25519.X86.acc s₃ = 0 := by
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
      u₂.other .ebx (by decide), u₁.gpr, VG.Proof.X25519.X86.toNat_zero32]
  have c₃ := k₃.ctx hctx
  refine WP.mono (VG.Proof.X25519.X86.cols_ok c₃ ts 8 ho hr (by rw [m₃]; exact hb) (by rw [a₃]; decide))
    fun s₄ ⟨k₄, f₄, e₄, _⟩ => ?_
  rw [a₃, m₃, Nat.zero_add] at e₄
  have hc : VG.Proof.X25519.X86.acc s₄ < 2 ^ 26 := by
    have : (2 ^ 32) ^ 8 * VG.Proof.X25519.X86.acc s₄ < (2 ^ 32) ^ 8 * 2 ^ 26 := by omega_using [e₄, hV]
    exact Nat.lt_of_mul_lt_mul_left this
  refine WP.mono (VG.Proof.X25519.X86.fold_ok (k₄.ctx c₃) ho rfl hc) fun s₅ ⟨k₅, f₅, e₅⟩ =>
    ⟨k₃.trans (k₄.trans k₅), by rw [m₃] at f₄; exact f₄.trans f₅, ?_⟩
  rw [e₅, ← fold256, ← e₄]
  rfl

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Arith`. -/
section

/-!
# X25519 on x86 (32-bit): the field operations

Each operation of `Impl/X25519/X86.lean` on elements at offsets of the working
space, as the operation of `GF(p)` on their values modulo `p`: `mul` (by
product scanning into `T`, then `lo + 38 hi`), `add`, `sub` (as `a + (2²⁵⁶ - 1 -
b) + (2²⁵⁶ - 75)`), `mulSmall` (by 121665). Each leaves the rest of memory
unchanged but for the output and, for `mul`, `T`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

variable {W : Nat}

/-! ## Numbers in any base, for `grind`'s ring normalization -/

/-- `num` in any base. -/
def numB (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X25519.X86.numB B f n + B ^ n * f n

theorem num_eq_numB (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num f n = VG.Proof.X25519.X86.numB (2 ^ 32) f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X25519.X86.num_succ, VG.Proof.X25519.X86.numB, ih]

/-- Product scanning: the columns of `a b` in radix `2³²`. -/
theorem prod_identity (fa fb : Nat → Nat) :
    VG.Proof.X25519.X86.num (fun k => (((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i =>
      fa i * fb (k - i)).sum) 16 = VG.Proof.X25519.X86.num fa 8 * VG.Proof.X25519.X86.num fb 8 := by
  simp only [VG.Proof.X25519.X86.num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [VG.Proof.X25519.X86.numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp (config := {decide := true}) only [ite_true, ite_false, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  grind

theorem num_16 (f : Nat → Nat) : VG.Proof.X25519.X86.num f 16 = VG.Proof.X25519.X86.num f 8 + 2 ^ 256 * VG.Proof.X25519.X86.num (fun k => f (8 + k)) 8 := by
  simp only [VG.Proof.X25519.X86.num_eq_numB]
  rw [show (2 : Nat) ^ 256 = (2 ^ 32) ^ 8 by rw [← Nat.pow_mul]]
  generalize 2 ^ 32 = B
  simp only [VG.Proof.X25519.X86.numB]
  grind

/-- The complements of the words. -/
theorem num_not {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) :
    VG.Proof.X25519.X86.num (fun k => 2 ^ 32 - 1 - f k) 8 = 2 ^ 256 - 1 - VG.Proof.X25519.X86.num f 8 := by
  have hs := VG.Proof.X25519.X86.num_add (fun k => 2 ^ 32 - 1 - f k) f 8
  have hc : VG.Proof.X25519.X86.num (fun k => 2 ^ 32 - 1 - f k + f k) 8 = VG.Proof.X25519.X86.num (fun _ => 2 ^ 32 - 1) 8 :=
    VG.Proof.X25519.X86.num_congr fun k hk => by have := h k hk; omega_using [this]
  have h1 : VG.Proof.X25519.X86.num (fun _ => 2 ^ 32 - 1) 8 = 2 ^ 256 - 1 := rfl
  omega_using [hs, hc, h1]

/-! ## Columns -/

theorem colv_le_len {m : Mem} {x : BitVec 32} {B : Nat} :
    ∀ {ts : List Term}, (∀ t ∈ ts, VG.Proof.X25519.X86.tval m x t ≤ B) → VG.Proof.X25519.X86.colv m x ts ≤ ts.length * B
  | [], _ => by simp [VG.Proof.X25519.X86.colv]
  | t :: ts, h => by
    have h1 := h t List.mem_cons_self
    have h2 := VG.Proof.X25519.X86.colv_le_len (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [VG.Proof.X25519.X86.colv, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    rw [Nat.add_mul, Nat.one_mul]; omega_using [h1, h2]

theorem wv_lt (m : Mem) (x : BitVec 32) (d : Nat) : VG.Proof.X25519.X86.wv m x d < 2 ^ 32 := BitVec.isLt _

theorem wv_mul_le (m : Mem) (x : BitVec 32) (a b : Nat) : VG.Proof.X25519.X86.wv m x a * VG.Proof.X25519.X86.wv m x b ≤ 2 ^ 64 := by
  have h1 := VG.Proof.X25519.X86.wv_lt m x a; have h2 := VG.Proof.X25519.X86.wv_lt m x b
  exact Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt h1) (Nat.le_of_lt h2)) (by decide)

/-- Three offsets of elements, each either equal to or apart from the other. -/
def Apart (o a : Nat) : Prop := a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a

instance (o a : Nat) : Decidable (VG.Proof.X25519.X86.Apart o a) := inferInstanceAs (Decidable (a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a))

/-- The words of `[a]` a column `k` of an output at `o` reads. -/
theorem apart_read {o a k j : Nat} (h : VG.Proof.X25519.X86.Apart o a) (hk : k ≤ j) (hj : j < 8) :
    a + 4 * j + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * j := by
  rcases h with h | h | h <;> omega_using [h, hk, hj]

/-! ## The operations -/

theorem zeroAcc_ok {s : State} :
    WP isa (.block zeroAcc) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem ∧ VG.Proof.X25519.X86.acc s' = 0 := by
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans (VG.Proof.X25519.X86.updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
    u₂.other .ebx (by decide), u₁.gpr, VG.Proof.X25519.X86.toNat_zero32]

/-- The offsets the arithmetic uses: elements below `T`. -/
def Below (o : Nat) : Prop := o + 32 ≤ VG.Impl.X25519.X86.T

instance : DecidablePred VG.Proof.X25519.X86.Below := fun o => inferInstanceAs (Decidable (o + 32 ≤ VG.Impl.X25519.X86.T))

/-- Squaring by columns: the products of distinct words doubled, and the squares. -/
theorem sqr_identity (fa : Nat → Nat) :
    VG.Proof.X25519.X86.num (fun k => ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map fun i =>
      2 * (fa i * fa (k - i))) ++ if k % 2 == 0 && k < 16 then [fa (k / 2) * fa (k / 2)] else []).sum) 16 =
      VG.Proof.X25519.X86.num fa 8 * VG.Proof.X25519.X86.num fa 8 := by
  simp only [VG.Proof.X25519.X86.num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [VG.Proof.X25519.X86.numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp (config := {decide := true}) only [ite_true, ite_false, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.nil_append, List.cons_append]
  grind

/-- 16 columns summed into `T`, then reduced to `[o]`: the value of the columns modulo `p`, when
they read only below `T` and each is below `2⁶⁸`. -/
theorem mulCols_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o : Nat} (ho : VG.Proof.X25519.X86.Below o)
    (ts : Nat → List Term) (hr : ∀ k < 16, ∀ t ∈ ts k, ∀ d ∈ VG.Proof.X25519.X86.treads t, d + 4 ≤ VG.Impl.X25519.X86.T)
    (hb : ∀ k < 16, VG.Proof.X25519.X86.colv s.mem x (ts k) < 2 ^ 68) {V : Nat} (hV : V < 2 ^ 256 * 2 ^ 256)
    (hv : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x (ts k)) 16 = V) :
    WP isa (.block (mulCols o ts)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 64] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = V % P := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho
  have hfit := hc.fit4
  refine WP.block_append (WP.block_append (WP.mono VG.Proof.X25519.X86.zeroAcc_ok fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))
  have c₁ := k₁.ctx hc
  refine WP.mono (VG.Proof.X25519.X86.cols_ok c₁ ts 16 (by simp only [VG.Impl.X25519.X86.T]; decide) (fun k hk t ht d hd => ?_)
    (fun k hk => ?_) (by rw [a₁]; decide)) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_
  · have := hr k hk t ht d hd
    simp only [VG.Impl.X25519.X86.T] at this ⊢
    exact ⟨by omega_using [this], .inl this⟩
  · rw [m₁]; exact hb k hk
  · -- The product, in `T`.
    rw [a₁, Nat.zero_add, m₁, hv] at e₂
    have e₃ : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * k)) 16 = V := by
      have hQ : ((2 : Nat) ^ 32) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
      rw [hQ] at e₂
      have : VG.Proof.X25519.X86.acc s₂ = 0 := by
        rcases Nat.eq_zero_or_pos (VG.Proof.X25519.X86.acc s₂) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ 256 * 2 ^ 256) h
          omega_using [this, e₂, hV]
      rw [this, Nat.mul_zero, Nat.add_zero] at e₂
      exact e₂
    rw [VG.Proof.X25519.X86.num_16] at e₃
    have c₂ := k₂.ctx c₁
    have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s₂.mem x [.mulI (VG.Impl.X25519.X86.T + 32 + 4 * k) 38, .addM (VG.Impl.X25519.X86.T + 4 * k)]) 8 =
        VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * k)) 8 + 38 * VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * (8 + k))) 8 := by
      rw [← VG.Proof.X25519.X86.num_mul, ← VG.Proof.X25519.X86.num_add]
      refine VG.Proof.X25519.X86.num_congr fun k _ => ?_
      show VG.Proof.X25519.X86.colv s₂.mem x _ = VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * k) + 38 * VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * (8 + k))
      rw [show VG.Impl.X25519.X86.T + 4 * (8 + k) = VG.Impl.X25519.X86.T + 32 + 4 * k by omega_using []]
      simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        VG.Proof.X25519.X86.toNat_38]
      omega_using []
    refine WP.mono (VG.Proof.X25519.X86.linear_ok c₂ o (fun k => [.mulI (VG.Impl.X25519.X86.T + 32 + 4 * k) 38, .addM (VG.Impl.X25519.X86.T + 4 * k)])
      (by omega_using [ho]) (fun k hk t ht d hd => ?_) (fun k hk => ?_) ?_) fun s₃ ⟨k₃, f₃, e₄⟩ =>
        ⟨k₁.trans (k₂.trans k₃), ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd <;> subst hd <;>
        simp only [VG.Impl.X25519.X86.T] <;> exact ⟨by omega_using [hk], .inr (by omega_using [ho, hk])⟩
    · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, VG.Proof.X25519.X86.toNat_38]
      have h1 := VG.Proof.X25519.X86.wv_lt s₂.mem x (VG.Impl.X25519.X86.T + 32 + 4 * k); have h2 := VG.Proof.X25519.X86.wv_lt s₂.mem x (VG.Impl.X25519.X86.T + 4 * k)
      omega_using [h1, h2]
    · have hl := VG.Proof.X25519.X86.num_lt (f := fun k => VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * k)) (n := 8) fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _
      have hh := VG.Proof.X25519.X86.num_lt (f := fun k => VG.Proof.X25519.X86.wv s₂.mem x (VG.Impl.X25519.X86.T + 4 * (8 + k))) (n := 8) fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _
      rw [hs]
      omega_using [hl, hh]
    · rw [m₁] at f₂
      exact (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (f₃.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
    · rw [e₄, hs, ← fold256, ← e₃]

theorem mul_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a b : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hb : VG.Proof.X25519.X86.Below b) :
    WP isa (.block (VG.Impl.X25519.X86.mul o a b)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 64] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = VG.Proof.X25519.X86.fe s.mem x a * VG.Proof.X25519.X86.fe s.mem x b % P := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ha hb
  have hA := VG.Proof.X25519.X86.fe_lt s.mem x a; have hB := VG.Proof.X25519.X86.fe_lt s.mem x b
  have hAB : VG.Proof.X25519.X86.fe s.mem x a * VG.Proof.X25519.X86.fe s.mem x b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul_of_lt_of_lt hA hB
  unfold VG.Impl.X25519.X86.mul
  split
  · subst b
    refine VG.Proof.X25519.X86.mulCols_ok hc ho _ (fun k hk t ht d hd => ?_) (fun k hk => ?_) hAB ?_
    · simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
      · simp only [VG.Proof.X25519.X86.treads, List.mem_cons, List.not_mem_nil, or_false] at hd
        simp only [VG.Impl.X25519.X86.T]
        rcases hd with rfl | rfl <;> omega_using [ha, hi, hki]
      · split at ht
        · rename_i hk2
          simp only [beq_iff_eq] at hk2
          simp only [List.mem_singleton] at ht
          subst ht
          simp only [VG.Proof.X25519.X86.treads, List.mem_cons, List.not_mem_nil, or_false] at hd
          simp only [VG.Impl.X25519.X86.T]
          rcases hd with rfl | rfl <;> omega_using [ha, hk2]
        · exact absurd ht List.not_mem_nil
    · have hl : (sqrTerms a k).length ≤ 5 := by
        simp only [sqrTerms, List.length_append, List.length_map]
        have := (by decide : ∀ k < 16, ((List.range 8).filter fun i => 2 * i < k && k - i < 8).length ≤ 4) k hk
        split <;> simp only [List.length_cons, List.length_nil] <;> omega_using [this]
      have h1 := VG.Proof.X25519.X86.colv_le_len (m := s.mem) (x := x) (B := 2 ^ 65) (ts := sqrTerms a k) fun t ht => by
        simp only [sqrTerms, List.mem_append, List.mem_map] at ht
        rcases ht with ⟨i, -, rfl⟩ | ht
        · have := VG.Proof.X25519.X86.wv_mul_le s.mem x (a + 4 * i) (a + 4 * (k - i))
          simp only [VG.Proof.X25519.X86.tval]; omega_using [this]
        · split at ht
          · simp only [List.mem_singleton] at ht
            subst ht
            have := VG.Proof.X25519.X86.wv_mul_le s.mem x (a + 4 * (k / 2)) (a + 4 * (k / 2))
            simp only [VG.Proof.X25519.X86.tval]; omega_using [this]
          · exact absurd ht List.not_mem_nil
      have h2 := Nat.mul_le_mul_right (2 ^ 65) hl
      omega_using [h1, h2]
    · have hcol : ∀ k, VG.Proof.X25519.X86.colv s.mem x (sqrTerms a k) = ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map
          fun i => 2 * (VG.Proof.X25519.X86.wv s.mem x (a + 4 * i) * VG.Proof.X25519.X86.wv s.mem x (a + 4 * (k - i)))) ++
          if k % 2 == 0 && k < 16 then [VG.Proof.X25519.X86.wv s.mem x (a + 4 * (k / 2)) * VG.Proof.X25519.X86.wv s.mem x (a + 4 * (k / 2))]
          else []).sum := fun k => by
        unfold VG.Proof.X25519.X86.colv sqrTerms
        rw [List.map_append, List.map_map]
        split <;> rfl
      simp only [hcol]
      exact VG.Proof.X25519.X86.sqr_identity (fun i => VG.Proof.X25519.X86.wv s.mem x (a + 4 * i))
  · refine VG.Proof.X25519.X86.mulCols_ok hc ho _ (fun k hk t ht d hd => ?_) (fun k hk => ?_) hAB ?_
    · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at ht
      obtain ⟨i, ⟨hi, -, hki⟩, rfl⟩ := ht
      simp only [VG.Proof.X25519.X86.treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      simp only [VG.Impl.X25519.X86.T]
      rcases hd with rfl | rfl <;> omega_using [ha, hb, hi, hki]
    · have hl : (prodTerms a b k).length ≤ 8 := by
        simp only [prodTerms, List.length_map]
        exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have h1 := VG.Proof.X25519.X86.colv_le_len (m := s.mem) (x := x) (B := 2 ^ 64) (ts := prodTerms a b k) fun t ht => by
        simp only [prodTerms, List.mem_map] at ht
        obtain ⟨i, -, rfl⟩ := ht
        exact VG.Proof.X25519.X86.wv_mul_le _ _ _ _
      have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
      omega_using [h1, h2]
    · have hcol : ∀ k, VG.Proof.X25519.X86.colv s.mem x (prodTerms a b k) = (((List.range 8).filter fun i => i ≤ k && k - i < 8).map
          fun i => VG.Proof.X25519.X86.wv s.mem x (a + 4 * i) * VG.Proof.X25519.X86.wv s.mem x (b + 4 * (k - i))).sum := fun k => by
        simp only [VG.Proof.X25519.X86.colv, prodTerms, List.map_map]; rfl
      simp only [hcol]
      exact VG.Proof.X25519.X86.prod_identity (fun i => VG.Proof.X25519.X86.wv s.mem x (a + 4 * i)) (fun j => VG.Proof.X25519.X86.wv s.mem x (b + 4 * j))

/-- The reads of a column `k` of an output at `o` from `[a + 4k]`. -/
theorem read_ok {o a k : Nat} (h : VG.Proof.X25519.X86.Apart o a) (ha : VG.Proof.X25519.X86.Below a) (hk : k < 8) :
    a + 4 * k + 4 ≤ 4096 ∧ (a + 4 * k + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * k) :=
  ⟨by simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ha; omega_using [ha, hk], VG.Proof.X25519.X86.apart_read h (Nat.le_refl _) hk⟩

theorem add_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a b : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hb : VG.Proof.X25519.X86.Below b) (hoa : VG.Proof.X25519.X86.Apart o a) (hob : VG.Proof.X25519.X86.Apart o b) :
    WP isa (.block (add o a b)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = (VG.Proof.X25519.X86.fe s.mem x a + VG.Proof.X25519.X86.fe s.mem x b) % P := by
  have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x [.addM (a + 4 * k), .addM (b + 4 * k)]) 8 =
      VG.Proof.X25519.X86.fe s.mem x a + VG.Proof.X25519.X86.fe s.mem x b := by
    rw [VG.Proof.X25519.X86.fe, VG.Proof.X25519.X86.fe, ← VG.Proof.X25519.X86.num_add]
    refine VG.Proof.X25519.X86.num_congr fun k _ => ?_
    simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  refine WP.mono (VG.Proof.X25519.X86.linear_ok hc o _ (by simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', by rw [e', hs]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd <;> subst hd
    exacts [VG.Proof.X25519.X86.read_ok hoa ha hk, VG.Proof.X25519.X86.read_ok hob hb hk]
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := VG.Proof.X25519.X86.wv_lt s.mem x (a + 4 * k); have h2 := VG.Proof.X25519.X86.wv_lt s.mem x (b + 4 * k)
    omega_using [h1, h2]
  · rw [hs]; have h1 := VG.Proof.X25519.X86.fe_lt s.mem x a; have h2 := VG.Proof.X25519.X86.fe_lt s.mem x b; omega_using [h1, h2]

theorem num_subK : VG.Proof.X25519.X86.num (fun k => (subK k).toNat) 8 = 2 ^ 256 - 75 := by decide

theorem sub_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a b : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hb : VG.Proof.X25519.X86.Below b) (hoa : VG.Proof.X25519.X86.Apart o a) (hob : VG.Proof.X25519.X86.Apart o b) :
    WP isa (.block (Impl.X25519.X86.sub o a b)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      (VG.Proof.X25519.X86.fe s'.mem x o + VG.Proof.X25519.X86.fe s.mem x b) % P = VG.Proof.X25519.X86.fe s.mem x a % P := by
  have hB := VG.Proof.X25519.X86.fe_lt s.mem x b
  have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x [.addM (a + 4 * k), .addNot (b + 4 * k), .addI (subK k)]) 8 =
      VG.Proof.X25519.X86.fe s.mem x a + (2 ^ 256 - 1 - VG.Proof.X25519.X86.fe s.mem x b) + (2 ^ 256 - 75) := by
    rw [VG.Proof.X25519.X86.fe, VG.Proof.X25519.X86.fe, ← VG.Proof.X25519.X86.num_subK, ← VG.Proof.X25519.X86.num_not fun k _ => VG.Proof.X25519.X86.wv_lt s.mem x (b + 4 * k), ← VG.Proof.X25519.X86.num_add, ← VG.Proof.X25519.X86.num_add]
    refine VG.Proof.X25519.X86.num_congr fun k _ => ?_
    simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_assoc]
  refine WP.mono (VG.Proof.X25519.X86.linear_ok hc o _ (by simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only [VG.Proof.X25519.X86.treads, List.mem_singleton, List.not_mem_nil] at hd
    · subst hd; exact VG.Proof.X25519.X86.read_ok hoa ha hk
    · subst hd; exact VG.Proof.X25519.X86.read_ok hob hb hk
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := VG.Proof.X25519.X86.wv_lt s.mem x (a + 4 * k); have h3 := (subK k).isLt
    omega_using [h1, h3]
  · rw [hs]; have h1 := VG.Proof.X25519.X86.fe_lt s.mem x a; omega_using [h1, hB]
  · rw [Nat.add_mod, e', hs, ← Nat.add_mod]
    have e : VG.Proof.X25519.X86.fe s.mem x a + (2 ^ 256 - 1 - VG.Proof.X25519.X86.fe s.mem x b) + (2 ^ 256 - 75) + VG.Proof.X25519.X86.fe s.mem x b =
        VG.Proof.X25519.X86.fe s.mem x a + P * 4 := by simp only [P]; omega_using [hB]
    rw [e, Nat.add_mul_mod_self_left]

theorem mulSmall_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hoa : VG.Proof.X25519.X86.Apart o a) :
    WP isa (.block (mulSmall o a)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o % P = 121665 * VG.Proof.X25519.X86.fe s.mem x a % P := by
  have hs : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s.mem x [.mulI (a + 4 * k) 121665]) 8 = 121665 * VG.Proof.X25519.X86.fe s.mem x a := by
    rw [VG.Proof.X25519.X86.fe, ← VG.Proof.X25519.X86.num_mul]
    refine VG.Proof.X25519.X86.num_congr fun k _ => ?_
    simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.mul_comm (VG.Proof.X25519.X86.wv _ _ _)]
    rfl
  refine WP.mono (VG.Proof.X25519.X86.linear_ok hc o _ (by simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', by rw [e', hs]⟩
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact VG.Proof.X25519.X86.read_ok hoa ha hk
  · simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := VG.Proof.X25519.X86.wv_lt s.mem x (a + 4 * k)
    have : VG.Proof.X25519.X86.wv s.mem x (a + 4 * k) * (121665 : BitVec 32).toNat ≤ 2 ^ 32 * 121665 :=
      Nat.mul_le_mul (Nat.le_of_lt h1) (by decide)
    omega_using [this]
  · rw [hs]; have h1 := VG.Proof.X25519.X86.fe_lt s.mem x a; omega_using [h1]

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Contract`. -/
section

/-!
# X25519 on x86 (32-bit): the contract the proof is written against

The facts of the shared contract (`Spec.X25519.x25519Contract`) the proof
uses, stated for x86; the shared contract implies it (`sig_implies`, in
`Main.lean`).
-/

namespace VG.Proof.X25519

open VG VG.X86 in
/-- `vg_x25519(out, scalar, point, scratch)`, whose arguments are on the
stack (cdecl). -/
def x25519X86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let point : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [scalar, point, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.X25519.bytesAt s'.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.X25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.X25519

namespace VG.Proof.X25519.X86

open VG VG.X86

section
variable (s₀ : State)
/-- The arguments and the regions, on entry. -/
abbrev outR : Region := ⟨(arg s₀ 0).setWidth 64, 32⟩
abbrev scalarR : Region := ⟨(arg s₀ 1).setWidth 64, 32⟩
abbrev pointR : Region := ⟨(arg s₀ 2).setWidth 64, 32⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X25519.X86.scalarR s₀, VG.Proof.X25519.X86.pointR s₀, VG.Proof.X25519.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.X25519.X86.outR s₀, VG.Proof.X25519.X86.scR 4096 (arg s₀ 3)]
  out_sc : (VG.Proof.X25519.X86.outR s₀).Disjoint (VG.Proof.X25519.X86.scR 4096 (arg s₀ 3))
  scalar_sc : (VG.Proof.X25519.X86.scalarR s₀).Disjoint (VG.Proof.X25519.X86.scR 4096 (arg s₀ 3))
  point_sc : (VG.Proof.X25519.X86.pointR s₀).Disjoint (VG.Proof.X25519.X86.scR 4096 (arg s₀ 3))
  args_out : (VG.Proof.X25519.X86.argsR s₀).Disjoint (VG.Proof.X25519.X86.outR s₀)
  args_sc : (VG.Proof.X25519.X86.argsR s₀).Disjoint (VG.Proof.X25519.X86.scR 4096 (arg s₀ 3))
  ret_out : (VG.Proof.X25519.X86.retR s₀).Disjoint (VG.Proof.X25519.X86.outR s₀)
  ret_sc : (VG.Proof.X25519.X86.retR s₀).Disjoint (VG.Proof.X25519.X86.scR 4096 (arg s₀ 3))
  out_fit : (arg s₀ 0).toNat + 32 ≤ 2 ^ 32
  scalar_fit : (arg s₀ 1).toNat + 32 ≤ 2 ^ 32
  point_fit : (arg s₀ 2).toNat + 32 ≤ 2 ^ 32
  sc_fit : (arg s₀ 3).toNat + 4096 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519X86.pre s₀) : VG.Proof.X25519.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 4) : (⟨argAddr s 0, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 16) (by omega_using [hfit]) (by omega_using [])
    (by omega_using [hi]) (by decide)

namespace Pre
variable {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨VG.Proof.X25519.X86.argsR s₀, by rw [hp.rd]; simp, VG.Proof.X25519.X86.arg_contains hp.sp_fit hi⟩

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [VG.Proof.X25519.X86.scR 4096 (arg s₀ 3)] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (VG.Proof.X25519.X86.arg_contains hp.sp_fit hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem sc_in : VG.Proof.X25519.X86.scR 4096 (arg s₀ 3) ∈ s₀.wr := by rw [hp.wr]; simp

theorem out_in : VG.Proof.X25519.X86.outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end Pre

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Ops`. -/
section

/-!
# X25519 on x86 (32-bit): sequences of field operations

The elements the field arithmetic computes with are at the *slots* of the
working space (offsets `lo + 32 i` below `T`: X25519's ladder and inversion
use `lo = 288`, Ed25519 `lo = 64`), and their values `F m x q` in `GF(p)`. A
sequence of operations (`ops`) leaves in each slot the value of an evaluation
of the operations on the values of the slots (`run`), and changes no memory
outside the slots and `T` (`[lo, T + 64)`). Also: `copy`, and `cswap` by a
mask.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

variable {W lo : Nat}

/-- The value in `GF(p)` of the element at `[x + q]`. -/
def F (m : Mem) (x : BitVec 32) (q : Nat) : Fe := toFe (VG.Proof.X25519.X86.fe m x q)

/-- The slots: elements at offsets `lo + 32 i` below `T`. -/
def isSlot (lo q : Nat) : Bool := lo ≤ q && q + 32 ≤ VG.Impl.X25519.X86.T && (q - lo) % 32 == 0

theorem slot_below {q : Nat} (h : VG.Proof.X25519.X86.isSlot lo q = true) : VG.Proof.X25519.X86.Below q := by
  simp only [VG.Proof.X25519.X86.isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at h ⊢; omega_using [h]

theorem slot_ge {q : Nat} (h : VG.Proof.X25519.X86.isSlot lo q = true) : lo ≤ q := by
  simp only [VG.Proof.X25519.X86.isSlot, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem slot_apart {o q : Nat} (ho : VG.Proof.X25519.X86.isSlot lo o = true) (hq : VG.Proof.X25519.X86.isSlot lo q = true) : VG.Proof.X25519.X86.Apart o q := by
  simp only [VG.Proof.X25519.X86.isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho hq
  simp only [VG.Proof.X25519.X86.Apart, VG.Impl.X25519.X86.T] at ho hq ⊢; omega_using [ho, hq]

theorem slot_ne {o q : Nat} (ho : VG.Proof.X25519.X86.isSlot lo o = true) (hq : VG.Proof.X25519.X86.isSlot lo q = true) (h : q ≠ o) :
    q + 32 ≤ o ∨ o + 32 ≤ q := by
  simp only [VG.Proof.X25519.X86.isSlot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho hq
  simp only [VG.Impl.X25519.X86.T] at ho hq; omega_using [ho, hq, h]

/-! ## Copies -/

theorem copy_step {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a n : Nat} (ho : VG.Proof.X25519.X86.Below o)
    (ha : VG.Proof.X25519.X86.Below a) (hoa : VG.Proof.X25519.X86.Apart o a) (hn : n < 8) (hk : VG.Proof.X25519.X86.Keep s₀ s) (hf : Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (o + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (a + 4 * j)) :
    WP isa (.block [.mov .eax (.mem (sc (a + 4 * n))), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      VG.Proof.X25519.X86.Keep s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (a + 4 * j) := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho ha
  have hfit := hc.fit4
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by omega_using [ha, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW4 (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have hr : VG.Proof.X25519.X86.wd s.mem x (a + 4 * n) = VG.Proof.X25519.X86.wd s₀.mem x (a + 4 * n) :=
    VG.Proof.X25519.X86.wd_frame1 hf hfit (by omega_using [ho, hn]) (by omega_using [ha, hn])
      (VG.Proof.X25519.X86.apart_read hoa (Nat.le_refl _) hn)
  refine ⟨hk.trans ((VG.Proof.X25519.X86.updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self]; exact hr
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem copies_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hoa : VG.Proof.X25519.X86.Apart o a) : ∀ n ≤ 8,
    WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (sc (a + 4 * k))),
      .store (sc (o + 4 * k)) .eax])) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s.mem s'.mem ∧
        ∀ j < n, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = VG.Proof.X25519.X86.wd s.mem x (a + 4 * j)
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.copies_ok hc ho ha hoa n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      VG.Proof.X25519.X86.copy_step (k₁.ctx hc) ho ha hoa (by omega_using [hn]) k₁ f₁ w₁)

theorem copy_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o a : Nat} (ho : VG.Proof.X25519.X86.Below o) (ha : VG.Proof.X25519.X86.Below a)
    (hoa : VG.Proof.X25519.X86.Apart o a) :
    WP isa (.block (copy o a)) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧ VG.Proof.X25519.X86.fe s'.mem x o = VG.Proof.X25519.X86.fe s.mem x a :=
  WP.mono (VG.Proof.X25519.X86.copies_ok hc ho ha hoa 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ =>
    ⟨k, f, VG.Proof.X25519.X86.num_congr fun j hj => by
      show (VG.Proof.X25519.X86.wd _ x (o + 4 * j)).toNat = (VG.Proof.X25519.X86.wd _ x (a + 4 * j)).toNat; rw [w j hj]⟩

/-! ## Conditional swaps -/

/-- The mask of `sw ∈ {0, 1}`. -/
def mask (sw : Nat) : BitVec 32 := 0 - BitVec.ofNat 32 sw

theorem sel_mask (X Y : BitVec 32) {sw : Nat} (h : sw ≤ 1) :
    X ^^^ ((X ^^^ Y) &&& VG.Proof.X25519.X86.mask sw) = (if sw = 1 then Y else X) ∧
      Y ^^^ ((X ^^^ Y) &&& VG.Proof.X25519.X86.mask sw) = (if sw = 1 then X else Y) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
  · simp only [VG.Proof.X25519.X86.mask, BitVec.ofNat_eq_ofNat, BitVec.sub_zero, BitVec.and_zero, BitVec.xor_zero]
    exact ⟨rfl, rfl⟩
  · have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
    simp only [VG.Proof.X25519.X86.mask, this, BitVec.and_allOnes, ite_true]
    refine ⟨?_, ?_⟩
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm X Y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The words below `n` of the elements at `[x + X]` and `[x + Y]` swapped if
`sw = 1`, the others as on entry. -/
structure SwapInv (x : BitVec 32) (s₀ : State) (X Y sw n : Nat) (s : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s₀ s
  ecx : s.gpr .ecx = s₀.gpr .ecx
  frame : Frame [VG.Proof.X25519.X86.sub x X 32, VG.Proof.X25519.X86.sub x Y 32] s₀.mem s.mem
  done : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (X + 4 * j) = (if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * j) else VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * j)) ∧
    VG.Proof.X25519.X86.wd s.mem x (Y + 4 * j) = (if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * j) else VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * j))
  todo : ∀ j < 8, n ≤ j → VG.Proof.X25519.X86.wd s.mem x (X + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * j) ∧
    VG.Proof.X25519.X86.wd s.mem x (Y + 4 * j) = VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * j)

theorem cswap_step {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {X Y sw n : Nat} (hX : VG.Proof.X25519.X86.Below X)
    (hY : VG.Proof.X25519.X86.Below Y) (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s₀.gpr .ecx = VG.Proof.X25519.X86.mask sw)
    (hn : n < 8) (h : VG.Proof.X25519.X86.SwapInv x s₀ X Y sw n s) :
    WP isa (.block [.mov .eax (.mem (sc (X + 4 * n))), .mov .edx (.mem (sc (Y + 4 * n))), .mov .ebx (.reg .eax),
      .alu .xor .ebx (.reg .edx), .alu .and .ebx (.reg .ecx), .alu .xor .eax (.reg .ebx),
      .alu .xor .edx (.reg .ebx), .store (sc (X + 4 * n)) .eax, .store (sc (Y + 4 * n)) .edx]) s
      (VG.Proof.X25519.X86.SwapInv x s₀ X Y sw (n + 1)) := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hX hY
  have hfit := hc.fit4
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by omega_using [hX, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
  refine Wp.wp_ldm c₁.edi (c₁.inRW4 (by omega_using [hY, hn]) (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_mov fun s₃ u₃ => Wp.wp_xor fun s₄ u₄ => Wp.wp_and fun s₅ u₅ => Wp.wp_xor fun s₆ u₆ =>
    Wp.wp_xor fun s₇ u₇ => ?_
  have k₇ : VG.Proof.X25519.X86.Keep s s₇ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans ((VG.Proof.X25519.X86.updKeep u₃).trans ((VG.Proof.X25519.X86.updKeep u₄).trans
    ((VG.Proof.X25519.X86.updKeep u₅).trans ((VG.Proof.X25519.X86.updKeep u₆).trans (VG.Proof.X25519.X86.updKeep u₇))))))
  have c₇ := k₇.ctx hc
  refine Wp.wp_stm c₇.edi (c₇.inW4 (by omega_using [hX, hn]) (by decide)) fun s₈ u₈ => ?_
  have c₈ : VG.Proof.X25519.X86.Ctx W x s₈ := c₇.keep (by rw [u₈.gpr]) u₈.wr
  refine Wp.wp_stm c₈.edi (c₈.inW4 (by omega_using [hY, hn]) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  -- The values.
  have m₇ : s₇.mem = s.mem := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₇ : s₇.gpr .ecx = s.gpr .ecx := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ⟨tX, tY⟩ := h.todo n hn (Nat.le_refl _)
  have eX : s₁.gpr .eax = VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n) := by rw [u₁.gpr]; exact tX
  have eY : s₂.gpr .edx = VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n) := by rw [u₂.gpr, u₁.mem]; exact tY
  have ed : s₅.gpr .ebx = (VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n) ^^^ VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n)) &&& VG.Proof.X25519.X86.mask sw := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide),
      u₃.other .edx (by decide), u₂.other .eax (by decide), eX, eY, u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), h.ecx, hm]
  have v₆ : s₆.gpr .eax = if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n) else VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n) := by
    rw [u₆.gpr, ed, u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), eX]
    exact (VG.Proof.X25519.X86.sel_mask _ _ hsw).1
  have v₇ : s₇.gpr .edx = if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n) else VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n) := by
    rw [u₇.gpr, u₆.other .ebx (by decide), ed, u₆.other .edx (by decide),
      u₅.other .edx (by decide), u₄.other .edx (by decide), u₃.other .edx (by decide), eY]
    exact (VG.Proof.X25519.X86.sel_mask _ _ hsw).2
  have eax₈ : s₇.gpr .eax = s₆.gpr .eax := u₇.other _ (by decide)
  have hsep : ∀ j < 8, ∀ k < 8, X + 4 * j + 4 ≤ Y + 4 * k ∨ Y + 4 * k + 4 ≤ X + 4 * j := fun j hj k hk => by
    omega_using [hXY, hj, hk]
  have wX : ∀ j < 8, VG.Proof.X25519.X86.wd s₉.mem x (X + 4 * j) =
      if j = n then (if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n) else VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n))
      else VG.Proof.X25519.X86.wd s.mem x (X + 4 * j) := fun j hj => by
    rw [u₉.mem, u₈.mem, u₈.gpr, v₇, VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, hX, hj])
      (by omega_using [hfit, hY, hn]) (hsep j hj n hn), eax₈, v₆, m₇]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self]; simp only [↓reduceIte]
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, hX, hj]) (by omega_using [hfit, hX, hn])
        (by omega_using [e]), ite_eq_right e]
  have wY : ∀ j < 8, VG.Proof.X25519.X86.wd s₉.mem x (Y + 4 * j) =
      if j = n then (if sw = 1 then VG.Proof.X25519.X86.wd s₀.mem x (X + 4 * n) else VG.Proof.X25519.X86.wd s₀.mem x (Y + 4 * n))
      else VG.Proof.X25519.X86.wd s.mem x (Y + 4 * j) := fun j hj => by
    rw [u₉.mem, u₈.mem, u₈.gpr, v₇]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self]; simp only [↓reduceIte]
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, hY, hj]) (by omega_using [hfit, hY, hn])
        (by omega_using [e]), ite_eq_right e, VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, hY, hj])
        (by omega_using [hfit, hX, hn]) ((hsep n hn j hj).symm), m₇]
  refine ⟨h.keep.trans (k₇.trans ⟨by rw [u₉.gpr, u₈.gpr], by rw [u₉.gpr, u₈.gpr], by rw [u₉.gpr, u₈.gpr],
    by rw [u₉.rd, u₈.rd], by rw [u₉.wr, u₈.wr]⟩), by rw [u₉.gpr, u₈.gpr, ecx₇, h.ecx], ?_, fun j hj => ?_,
    fun j hj hnj => ?_⟩
  · rw [u₉.mem, u₈.mem, m₇]
    refine (h.frame.writeW List.mem_cons_self _ ?_).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_
    · exact VG.Proof.X25519.X86.sub_contains (by omega_using [hfit, hX]) (by omega_using []) (by omega_using [hn]) (by decide)
    · exact VG.Proof.X25519.X86.sub_contains (by omega_using [hfit, hY]) (by omega_using []) (by omega_using [hn]) (by decide)
  · rw [wX j (by omega_using [hj, hn]), wY j (by omega_using [hj, hn])]
    by_cases e : j = n
    · subst e; simp only [↓reduceIte, and_self]
    · simp only [ite_eq_right e]; exact h.done j (by omega_using [hj, e])
  · rw [wX j hj, wY j hj, ite_eq_right (by omega_using [hnj]), ite_eq_right (by omega_using [hnj])]
    exact h.todo j hj (by omega_using [hnj])

theorem cswaps_ok {x : BitVec 32} {s₀ : State} {X Y sw : Nat} (hX : VG.Proof.X25519.X86.Below X) (hY : VG.Proof.X25519.X86.Below Y)
    (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s₀.gpr .ecx = VG.Proof.X25519.X86.mask sw) (hc₀ : VG.Proof.X25519.X86.Ctx W x s₀) :
    ∀ n ≤ 8, ∀ s, VG.Proof.X25519.X86.SwapInv x s₀ X Y sw 0 s →
    WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.mem (sc (X + 4 * k))), .mov .edx (.mem (sc (Y + 4 * k))), .mov .ebx (.reg .eax),
        .alu .xor .ebx (.reg .edx), .alu .and .ebx (.reg .ecx), .alu .xor .eax (.reg .ebx),
        .alu .xor .edx (.reg .ebx), .store (sc (X + 4 * k)) .eax, .store (sc (Y + 4 * k)) .edx])) s
      (VG.Proof.X25519.X86.SwapInv x s₀ X Y sw n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.cswaps_ok hX hY hXY hsw hm hc₀ n (by omega_using [hn]) s h)
      fun s₁ h₁ => VG.Proof.X25519.X86.cswap_step (h₁.keep.ctx hc₀) hX hY hXY hsw hm (by omega_using [hn]) h₁)

/-- `cswap X Y` with the mask of `sw` in `ecx`. -/
theorem cswap_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {X Y sw : Nat} (hX : VG.Proof.X25519.X86.Below X) (hY : VG.Proof.X25519.X86.Below Y)
    (hXY : X + 32 ≤ Y ∨ Y + 32 ≤ X) (hsw : sw ≤ 1) (hm : s.gpr .ecx = VG.Proof.X25519.X86.mask sw) :
    WP isa (.block (cswap X Y)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [VG.Proof.X25519.X86.sub x X 32, VG.Proof.X25519.X86.sub x Y 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x X = (if sw = 1 then VG.Proof.X25519.X86.fe s.mem x Y else VG.Proof.X25519.X86.fe s.mem x X) ∧
      VG.Proof.X25519.X86.fe s'.mem x Y = (if sw = 1 then VG.Proof.X25519.X86.fe s.mem x X else VG.Proof.X25519.X86.fe s.mem x Y) := by
  refine WP.mono (VG.Proof.X25519.X86.cswaps_ok hX hY hXY hsw hm hc 8 (Nat.le_refl _) s ⟨Keep.refl _, rfl, Frame.refl _ _,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => ⟨rfl, rfl⟩⟩) fun s' h =>
    ⟨h.keep, h.ecx, h.frame, ?_, ?_⟩
  · by_cases e : sw = 1
    · rw [ite_eq_left e]
      exact VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd _ x (X + 4 * j)).toNat = (VG.Proof.X25519.X86.wd _ x (Y + 4 * j)).toNat; rw [(h.done j hj).1, ite_eq_left e]
    · rw [ite_eq_right e]
      exact VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd _ x (X + 4 * j)).toNat = (VG.Proof.X25519.X86.wd _ x (X + 4 * j)).toNat; rw [(h.done j hj).1, ite_eq_right e]
  · by_cases e : sw = 1
    · rw [ite_eq_left e]
      exact VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd _ x (Y + 4 * j)).toNat = (VG.Proof.X25519.X86.wd _ x (X + 4 * j)).toNat; rw [(h.done j hj).2, ite_eq_left e]
    · rw [ite_eq_right e]
      exact VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd _ x (Y + 4 * j)).toNat = (VG.Proof.X25519.X86.wd _ x (Y + 4 * j)).toNat; rw [(h.done j hj).2, ite_eq_right e]

/-! ## Sequences of operations -/

/-- An operation's output. -/
def opOut : Op → Nat
  | .mul o _ _ | .mulSmall o _ | .add o _ _ | .sub o _ _ | .copy o _ => o

/-- An operation's inputs. -/
def opIns : Op → List Nat
  | .mul _ a b | .add _ a b | .sub _ a b => [a, b]
  | .mulSmall _ a | .copy _ a => [a]

/-- An operation on slots. -/
def opValid (lo : Nat) (op : Op) : Bool := VG.Proof.X25519.X86.isSlot lo (VG.Proof.X25519.X86.opOut op) && (VG.Proof.X25519.X86.opIns op).all (VG.Proof.X25519.X86.isSlot lo)

/-- An operation's result, for the values `E` of the slots. -/
def opVal (op : Op) (E : Nat → Fe) : Fe :=
  match op with
  | .mul _ a b => E a * E b
  | .mulSmall _ a => a24 * E a
  | .add _ a b => E a + E b
  | .sub _ a b => E a - E b
  | .copy _ a => E a

/-- The values of the slots after a sequence of operations. -/
def run : List Op → (Nat → Fe) → Nat → Fe
  | [], E => E
  | op :: l, E => VG.Proof.X25519.X86.run l (Function.update E (VG.Proof.X25519.X86.opOut op) (VG.Proof.X25519.X86.opVal op E))

theorem opVal_congr {E E' : Nat → Fe} (op : Op) (h : ∀ q ∈ VG.Proof.X25519.X86.opIns op, E q = E' q) : VG.Proof.X25519.X86.opVal op E = VG.Proof.X25519.X86.opVal op E' := by
  cases op <;> simp only [VG.Proof.X25519.X86.opIns, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [VG.Proof.X25519.X86.opVal, h]

theorem run_congr (l : List Op) (hv : ∀ op ∈ l, VG.Proof.X25519.X86.opValid lo op = true) :
    ∀ {E E' : Nat → Fe}, (∀ q, VG.Proof.X25519.X86.isSlot lo q = true → E q = E' q) → ∀ q, VG.Proof.X25519.X86.isSlot lo q = true → VG.Proof.X25519.X86.run l E q = VG.Proof.X25519.X86.run l E' q := by
  induction l with
  | nil => exact fun h q hq => h q hq
  | cons op l ih =>
    intro E E' h q hq
    have hvo := hv op List.mem_cons_self
    simp only [VG.Proof.X25519.X86.opValid, Bool.and_eq_true, List.all_eq_true] at hvo
    refine ih (fun o ho => hv o (List.mem_cons_of_mem _ ho)) (fun r hr => ?_) q hq
    by_cases e : r = VG.Proof.X25519.X86.opOut op
    · subst e; simp only [Function.update_self]
      exact VG.Proof.X25519.X86.opVal_congr op fun q hq => h q (hvo.2 q hq)
    · simp only [Function.update_of_ne e]; exact h r hr

/-- A frame of a slot and of words at `T` is one of the slots and `T`. -/
theorem frame_wide {m m' : Mem} {x : BitVec 32} {o n : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (ho : VG.Proof.X25519.X86.isSlot lo o = true) (hn : n ≤ 64) (hf : Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T n] m m') :
    Frame [VG.Proof.X25519.X86.sub x lo (VG.Impl.X25519.X86.T + 64 - lo)] m m' := by
  have hob := VG.Proof.X25519.X86.slot_below ho; have ho' := VG.Proof.X25519.X86.slot_ge ho
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hob
  exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_sub hx ho' (by simp only [VG.Impl.X25519.X86.T]; omega_using [ho', hob]) (by omega_using [hob])
    · exact VG.Proof.X25519.X86.sub_sub hx (by simp only [VG.Impl.X25519.X86.T]; omega_using [ho', hob]) (by simp only [VG.Impl.X25519.X86.T]; omega_using [ho', hob, hn])
        (by simp only [VG.Impl.X25519.X86.T]; decide)⟩

theorem op_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) (op : Op) (hv : VG.Proof.X25519.X86.opValid lo op = true) :
    WP isa (.block op.code) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x lo (VG.Impl.X25519.X86.T + 64 - lo)] s.mem s'.mem ∧
      ∀ q, VG.Proof.X25519.X86.isSlot lo q = true → VG.Proof.X25519.X86.F s'.mem x q = Function.update (VG.Proof.X25519.X86.F s.mem x) (VG.Proof.X25519.X86.opOut op) (VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x)) q := by
  have hfit := hc.fit4
  simp only [VG.Proof.X25519.X86.opValid, Bool.and_eq_true, List.all_eq_true] at hv
  obtain ⟨ho, hi⟩ := hv
  have hob := VG.Proof.X25519.X86.slot_below ho
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hob
  -- An element outside the output's region (and `T`'s).
  have other : ∀ {m m' : Mem}, Frame [VG.Proof.X25519.X86.sub x (VG.Proof.X25519.X86.opOut op) 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 64] m m' → ∀ q, VG.Proof.X25519.X86.isSlot lo q = true →
      q ≠ (VG.Proof.X25519.X86.opOut op) → VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q := fun {m m'} hf q hq hne => by
    have hqb := VG.Proof.X25519.X86.slot_below hq; simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hqb
    have hs := VG.Proof.X25519.X86.slot_ne ho hq hne
    simp only [VG.Proof.X25519.X86.F]
    refine congrArg toFe (VG.Proof.X25519.X86.fe_frame fun k hk => VG.Proof.X25519.X86.wd_frame hf fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hfit, hqb, hk]) (by omega_using [hfit, hob]) (by omega_using [hs, hk])
    · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hfit, hqb, hk]) (by simp only [VG.Impl.X25519.X86.T]; omega_using [hfit])
        (by simp only [VG.Impl.X25519.X86.T]; omega_using [hqb, hk])
  have frame1 : ∀ {m m' : Mem}, Frame [VG.Proof.X25519.X86.sub x (VG.Proof.X25519.X86.opOut op) 32] m m' → Frame [VG.Proof.X25519.X86.sub x (VG.Proof.X25519.X86.opOut op) 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 64] m m' :=
    fun hf => hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have fin : ∀ s', VG.Proof.X25519.X86.Keep s s' → Frame [VG.Proof.X25519.X86.sub x (VG.Proof.X25519.X86.opOut op) 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 64] s.mem s'.mem →
      VG.Proof.X25519.X86.F s'.mem x (VG.Proof.X25519.X86.opOut op) = VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x) →
      VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x lo (VG.Impl.X25519.X86.T + 64 - lo)] s.mem s'.mem ∧
        ∀ q, VG.Proof.X25519.X86.isSlot lo q = true → VG.Proof.X25519.X86.F s'.mem x q = Function.update (VG.Proof.X25519.X86.F s.mem x) (VG.Proof.X25519.X86.opOut op) (VG.Proof.X25519.X86.opVal op (VG.Proof.X25519.X86.F s.mem x)) q :=
    fun s' k f e => ⟨k, VG.Proof.X25519.X86.frame_wide hfit ho (Nat.le_refl _) f, fun q hq => by
      by_cases hq' : q = (VG.Proof.X25519.X86.opOut op)
      · subst hq'; rw [Function.update_self]; exact e
      · rw [Function.update_of_ne hq']; exact other f q hq hq'⟩
  cases op with
  | mul o a b =>
    simp only [VG.Proof.X25519.X86.opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (VG.Proof.X25519.X86.mul_ok hc (VG.Proof.X25519.X86.slot_below ho) (VG.Proof.X25519.X86.slot_below hi.1) (VG.Proof.X25519.X86.slot_below hi.2)) fun s' ⟨k, f, e⟩ =>
      fin s' k f (toFe_mul e)
  | mulSmall o a =>
    simp only [VG.Proof.X25519.X86.opIns, List.mem_singleton, forall_eq] at hi
    exact WP.mono (VG.Proof.X25519.X86.mulSmall_ok hc (VG.Proof.X25519.X86.slot_below ho) (VG.Proof.X25519.X86.slot_below hi) (VG.Proof.X25519.X86.slot_apart ho hi)) fun s' ⟨k, f, e⟩ =>
      fin s' k (frame1 f) (toFe_a24 e)
  | add o a b =>
    simp only [VG.Proof.X25519.X86.opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (VG.Proof.X25519.X86.add_ok hc (VG.Proof.X25519.X86.slot_below ho) (VG.Proof.X25519.X86.slot_below hi.1) (VG.Proof.X25519.X86.slot_below hi.2) (VG.Proof.X25519.X86.slot_apart ho hi.1)
      (VG.Proof.X25519.X86.slot_apart ho hi.2)) fun s' ⟨k, f, e⟩ => fin s' k (frame1 f) (toFe_add e)
  | sub o a b =>
    simp only [VG.Proof.X25519.X86.opIns, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hi
    exact WP.mono (VG.Proof.X25519.X86.sub_ok hc (VG.Proof.X25519.X86.slot_below ho) (VG.Proof.X25519.X86.slot_below hi.1) (VG.Proof.X25519.X86.slot_below hi.2) (VG.Proof.X25519.X86.slot_apart ho hi.1)
      (VG.Proof.X25519.X86.slot_apart ho hi.2)) fun s' ⟨k, f, e⟩ => fin s' k (frame1 f) (toFe_sub e)
  | copy o a =>
    simp only [VG.Proof.X25519.X86.opIns, List.mem_singleton, forall_eq] at hi
    exact WP.mono (VG.Proof.X25519.X86.copy_ok hc (VG.Proof.X25519.X86.slot_below ho) (VG.Proof.X25519.X86.slot_below hi) (VG.Proof.X25519.X86.slot_apart ho hi)) fun s' ⟨k, f, e⟩ =>
      fin s' k (frame1 f) (by simp only [VG.Proof.X25519.X86.F, VG.Proof.X25519.X86.opVal, VG.Proof.X25519.X86.opOut]; rw [e])

theorem ops_ok {x : BitVec 32} : ∀ {s : State} (l : List Op), VG.Proof.X25519.X86.Ctx W x s → (∀ op ∈ l, VG.Proof.X25519.X86.opValid lo op = true) →
    WP isa (.block (VG.Impl.X25519.X86.ops l)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x lo (VG.Impl.X25519.X86.T + 64 - lo)] s.mem s'.mem ∧
      ∀ q, VG.Proof.X25519.X86.isSlot lo q = true → VG.Proof.X25519.X86.F s'.mem x q = VG.Proof.X25519.X86.run l (VG.Proof.X25519.X86.F s.mem x) q
  | _, [], _, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ _ => rfl⟩
  | s, op :: l, hc, hv => by
    rw [VG.Impl.X25519.X86.ops, List.flatMap_cons]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.op_ok hc op (hv op List.mem_cons_self)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
    refine WP.mono (VG.Proof.X25519.X86.ops_ok l (k₁.ctx hc) fun o ho => hv o (List.mem_cons_of_mem _ ho))
      fun s₂ ⟨k₂, f₂, e₂⟩ => ⟨k₁.trans k₂, f₁.trans f₂, fun q hq => ?_⟩
    rw [e₂ q hq, VG.Proof.X25519.X86.run]
    exact VG.Proof.X25519.X86.run_congr l (fun o ho => hv o (List.mem_cons_of_mem _ ho)) e₁ q hq

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Step`. -/
section

/-!
# X25519 on x86 (32-bit): the ladder

What holds from the end of the setup on (`Base`: the working space, the saved
registers, the scalar's bits, and that nothing outside the working space
changes), and the ladder: each iteration takes the ladder's state after the
bits `254, …, n + 1` in the slots `X2, Z2, X3, Z3` and the word `SWAP` (`LInv
(n + 1)`) to that after the bit `n` (`LInv n`).
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The callee-saved registers and their slots in the working space, in the
order `save` stores them. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ VG.Proof.X25519.X86.savedSlots, p.2 + 4 ≤ 16 := by decide

/-- What holds from the end of the setup on: the working space at `x` (in
`edi`), the saved registers (of the state on entry `s₀`), the bits of the
scalar `k`, and memory outside the working space as on entry. -/
structure Base (x : BitVec 32) (k : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.X25519.X86.Ctx 4096 x s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.X25519.X86.scR 4096 x] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr VG.Proof.X25519.X86.savedSlots
  bits : ∀ t < 255, s.mem (addr x (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)

/-- A byte of the working space outside a frame's region. -/
theorem byte_frame1 {m m' : Mem} {x : BitVec 32} {o n d : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) (hd : d < 4096) (h : d + 1 ≤ o ∨ o + n ≤ d) :
    m' (addr x d) = m (addr x d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.X25519.X86.sub_disj (x := x) (n := 1) (by omega_using [hx, hd]) (by omega_using [hx, ho]) h _
      (Region.contains_self _ _)

theorem Base.of_frame {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : VG.Proof.X25519.X86.Base x k s₀ s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {o n : Nat} (hf : Frame [VG.Proof.X25519.X86.sub x o n] s.mem s'.mem) (ho : o + n ≤ 4096)
    (hlo : 16 ≤ o) (hgap : o + n ≤ 32 ∨ 288 ≤ o) (hon : o < 4096) : VG.Proof.X25519.X86.Base x k s₀ s' := by
  have hfit := h.ctx.fit
  refine ⟨h.ctx.keep hedi hwr, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_, fun t ht => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, VG.Proof.X25519.X86.scR_eq]
      exact VG.Proof.X25519.X86.sub_sub hfit (Nat.zero_le _) (by omega_using [ho]) hon⟩)
  · have := VG.Proof.X25519.X86.savedSlots_bound p hp
    exact VG.Proof.X25519.X86.wd_frame1 hf hfit ho (by omega_using [this]) (by omega_using [this, hlo])
  · rw [VG.Proof.X25519.X86.byte_frame1 hf hfit ho (by simp only [BITS]; omega_using [ht]) (by simp only [BITS]; omega_using [ht, hgap])]
    exact h.bits t ht

/-- The operations keep `Base`. -/
theorem Base.ops {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : VG.Proof.X25519.X86.Base x k s₀ s) (hk : VG.Proof.X25519.X86.Keep s s')
    (hf : Frame [VG.Proof.X25519.X86.sub x 288 640] s.mem s'.mem) : VG.Proof.X25519.X86.Base x k s₀ s' :=
  h.of_frame hk.edi hk.esp hk.rd hk.wr hf (by decide) (by decide) (.inr (Nat.le_refl _)) (by decide)

/-- The ladder's state after the bits `254` down to `n`, in the slots. -/
structure LInv (x : BitVec 32) (k : Nat) (x1 : Fe) (s₀ : State) (n : Nat) (s : State) : Prop
    extends VG.Proof.X25519.X86.Base x k s₀ s where
  esi : s.gpr .esi = BitVec.ofNat 32 n
  vx1 : VG.Proof.X25519.X86.F s.mem x X1 = x1
  vx2 : VG.Proof.X25519.X86.F s.mem x X2 = (ladderAfter k x1 n).x2
  vz2 : VG.Proof.X25519.X86.F s.mem x Z2 = (ladderAfter k x1 n).z2
  vx3 : VG.Proof.X25519.X86.F s.mem x X3 = (ladderAfter k x1 n).x3
  vz3 : VG.Proof.X25519.X86.F s.mem x Z3 = (ladderAfter k x1 n).z3
  swap : VG.Proof.X25519.X86.wd s.mem x SWAP = BitVec.ofNat 32 (ladderAfter k x1 n).swap

theorem run_step (V : Nat → Fe) :
    let A := V X2 + V Z2
    let AA := A * A
    let B := V X2 - V Z2
    let BB := B * B
    let Ee := AA - BB
    let C := V X3 + V Z3
    let D := V X3 - V Z3
    let DA := D * A
    let CB := C * B
    VG.Proof.X25519.X86.run stepOps V X2 = AA * BB ∧ VG.Proof.X25519.X86.run stepOps V Z2 = Ee * (AA + a24 * Ee) ∧
      VG.Proof.X25519.X86.run stepOps V X3 = (DA + CB) * (DA + CB) ∧ VG.Proof.X25519.X86.run stepOps V Z3 = V X1 * ((DA - CB) * (DA - CB)) ∧
      VG.Proof.X25519.X86.run stepOps V X1 = V X1 := by
  simp only [VG.Proof.X25519.X86.run, stepOps, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opVal, Function.update_apply, X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB,
    Impl.X25519.X86.E, DA, CB]
  simp only [↓reduceIte, Nat.reduceEqDiff, and_self]

theorem stepOps_valid : ∀ op ∈ stepOps, VG.Proof.X25519.X86.opValid 288 op = true := by decide

theorem cswap_fst (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).1 = if sw = 1 then b else a := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).2 = if sw = 1 then a else b := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem F_ite {m m' : Mem} {x : BitVec 32} {q a b : Nat} (sw : Nat)
    (h : VG.Proof.X25519.X86.fe m' x q = if sw = 1 then VG.Proof.X25519.X86.fe m x a else VG.Proof.X25519.X86.fe m x b) :
    VG.Proof.X25519.X86.F m' x q = if sw = 1 then VG.Proof.X25519.X86.F m x a else VG.Proof.X25519.X86.F m x b := by
  simp only [VG.Proof.X25519.X86.F, h]; split <;> rfl

theorem ofNat_xor {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = BitVec.ofNat 32 (a ^^^ b) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem byte_ofNat {b : Nat} (h : b ≤ 1) : (BitVec.ofNat 8 b).setWidth 32 = BitVec.ofNat 32 b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> decide

theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem addr_add_ofNat (x : BitVec 32) (n d : Nat) : addr (x + BitVec.ofNat 32 n) d = addr x (d + n) := by
  simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n d]

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_movzx8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Wp.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  simp only [exec, State.load8, ea_mk, ha, hin, ↓reduceIte, Option.map_some]

/-- The start of an iteration: the counter decremented to `n`, `swap` updated
and the mask of the swap in `ecx`. -/
theorem stepHead_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : VG.Proof.X25519.X86.LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block stepHead) s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 n ∧
      s'.gpr .ecx = VG.Proof.X25519.X86.mask ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n) ∧
      (∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s'.mem x q = VG.Proof.X25519.X86.F s.mem x q) ∧
      VG.Proof.X25519.X86.wd s'.mem x SWAP = BitVec.ofNat 32 (VG.Proof.X25519.bit k n) := by
  have hc := h.ctx
  have hfit := hc.fit
  have hsw := ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])
  have hb := bit_le k n
  refine Wp.wp_subi fun s₁ u₁ _ _ => Wp.wp_mov fun s₂ u₂ => Wp.wp_add fun s₃ u₃ _ => ?_
  have esi₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₁.gpr, h.esi]; exact Wp.ofNat_pred (by omega_using [])
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), esi₁]
  have eax₃ : s₃.gpr .eax = x + BitVec.ofNat 32 n := by
    rw [u₃.gpr, u₂.gpr, u₂.other .esi (by decide), esi₁, u₁.other _ (by decide), hc.edi]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have edi₃ : s₃.gpr .edi = x := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  have c₃ : VG.Proof.X25519.X86.Ctx 4096 x s₃ := hc.keep (by rw [edi₃, hc.edi]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  refine VG.Proof.X25519.X86.wp_movzx8 (a := addr x (BITS + n)) (by rw [eax₃, VG.Proof.X25519.X86.addr_add_ofNat])
    (c₃.inRW (by simp only [BITS]; omega_using [hn]) (by decide)) fun s₄ u₄ => ?_
  have eax₄ : s₄.gpr .eax = BitVec.ofNat 32 (VG.Proof.X25519.bit k n) := by
    rw [u₄.gpr, m₃, h.bits n (by omega_using [hn]), VG.Proof.X25519.X86.byte_ofNat hb]
  have c₄ := (VG.Proof.X25519.X86.updKeep u₄).ctx c₃
  refine Wp.wp_ldm c₄.edi (c₄.inRW (by simp only [SWAP]; decide) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_xor fun s₆ u₆ => ?_
  have edx₆ : s₆.gpr .edx = BitVec.ofNat 32 ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n) := by
    rw [u₆.gpr, u₅.gpr, u₄.mem, m₃, u₅.other .eax (by decide), eax₄]
    exact (congrArg (· ^^^ _) h.swap).trans (VG.Proof.X25519.X86.ofNat_xor hsw hb)
  have c₆ := (VG.Proof.X25519.X86.updKeep u₆).ctx ((VG.Proof.X25519.X86.updKeep u₅).ctx c₄)
  refine Wp.wp_stm c₆.edi (c₆.inW (by simp only [SWAP]; decide) (by decide)) fun s₇ u₇ => ?_
  refine Wp.wp_movi fun s₈ u₈ => Wp.wp_sub fun s₉ u₉ _ => WP.block_nil ?_
  have m₇ : s₉.mem = s.mem.writeW (addr x SWAP) (BitVec.ofNat 32 (VG.Proof.X25519.bit k n)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.other .eax (by decide), u₅.other .eax (by decide), eax₄, u₆.mem,
      u₅.mem, u₄.mem, m₃]
  have hf : Frame [VG.Proof.X25519.X86.sub x SWAP 4] s.mem s₉.mem := by
    rw [m₇]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  have g : ∀ r, r ≠ .ecx → r ≠ .eax → r ≠ .edx → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₉.other _ h1, u₈.other _ h1, u₇.gpr, u₆.other _ h3, u₅.other _ h3, u₄.other _ h2, u₃.other _ h2,
      u₂.other _ h2, u₁.other _ h4]
  refine ⟨h.toBase.of_frame (g _ (by decide) (by decide) (by decide) (by decide))
    (g _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) hf (by decide) (by decide)
    (.inl (by decide)) (by decide), ?_, ?_, fun q hq => ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
  · rw [u₉.gpr, u₈.gpr, u₈.other .edx (by decide), u₇.gpr, edx₆]; rfl
  · have hq' := VG.Proof.X25519.X86.slot_ge hq; have hqb := VG.Proof.X25519.X86.slot_below hq; simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hqb
    simp only [VG.Proof.X25519.X86.F]
    exact congrArg toFe (VG.Proof.X25519.X86.fe_frame fun j hj => VG.Proof.X25519.X86.wd_frame1 hf hfit (by decide) (by omega_using [hqb, hj])
      (by simp only [SWAP]; omega_using [hq']))
  · rw [m₇, VG.Proof.X25519.X86.wd_write_self]

/-- A frame of two slots is one of the slots and `T`. -/
theorem frame2_wide {m m' : Mem} {x : BitVec 32} {a b : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [VG.Proof.X25519.X86.sub x a 32, VG.Proof.X25519.X86.sub x b 32] m m') (ha : VG.Proof.X25519.X86.isSlot 288 a = true) (hb : VG.Proof.X25519.X86.isSlot 288 b = true) :
    Frame [VG.Proof.X25519.X86.sub x 288 640] m m' := by
  have ha1 := VG.Proof.X25519.X86.slot_ge ha; have ha2 := VG.Proof.X25519.X86.slot_below ha; have hb1 := VG.Proof.X25519.X86.slot_ge hb; have hb2 := VG.Proof.X25519.X86.slot_below hb
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ha2 hb2
  exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.X86.sub_sub hx ha1 (by omega_using [ha2]) (by omega_using [ha2])
    · exact VG.Proof.X25519.X86.sub_sub hx hb1 (by omega_using [hb2]) (by omega_using [hb2])⟩

/-- A slot other than the two a frame's regions are. -/
theorem F_frame2 {m m' : Mem} {x : BitVec 32} {a b q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [VG.Proof.X25519.X86.sub x a 32, VG.Proof.X25519.X86.sub x b 32] m m') (ha : VG.Proof.X25519.X86.isSlot 288 a = true) (hb : VG.Proof.X25519.X86.isSlot 288 b = true)
    (hq : VG.Proof.X25519.X86.isSlot 288 q = true) (hqa : q ≠ a) (hqb : q ≠ b) : VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q := by
  have ha2 := VG.Proof.X25519.X86.slot_below ha; have hb2 := VG.Proof.X25519.X86.slot_below hb; have hq2 := VG.Proof.X25519.X86.slot_below hq
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ha2 hb2 hq2
  have sa := VG.Proof.X25519.X86.slot_ne ha hq hqa; have sb := VG.Proof.X25519.X86.slot_ne hb hq hqb
  simp only [VG.Proof.X25519.X86.F]
  refine congrArg toFe (VG.Proof.X25519.X86.fe_frame fun j hj => VG.Proof.X25519.X86.wd_frame hf fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, ha2]) (by omega_using [sa, hj])
  · exact VG.Proof.X25519.X86.sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, hb2]) (by omega_using [sb, hj])

/-- One iteration of the ladder, for the bit `n`. -/
theorem step_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : VG.Proof.X25519.X86.LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block VG.Impl.X25519.X86.step) s fun s' => VG.Proof.X25519.X86.LInv x k x1 s₀ n s' ∧ s'.zf = some (decide (n = 0)) := by
  have hfit := h.ctx.fit
  have hsw := VG.Proof.X25519.X86.xor_le_one (ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])) (bit_le k n)
  simp only [VG.Impl.X25519.X86.step, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.stepHead_ok hn h) fun s₁ ⟨b₁, esi₁, ecx₁, F₁, sw₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cswap_ok b₁.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₁) fun s₂ ⟨k₂, ecx₂, f₂, x₂, y₂⟩ => ?_)
  have b₂ := b₁.ops k₂ (VG.Proof.X25519.X86.frame2_wide hfit f₂ (by decide) (by decide))
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cswap_ok b₂.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₂.trans ecx₁)) fun s₃ ⟨k₃, _, f₃, x₃, y₃⟩ => ?_)
  have b₃ := b₂.ops k₃ (VG.Proof.X25519.X86.frame2_wide hfit f₃ (by decide) (by decide))
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.ops_ok stepOps b₃.ctx VG.Proof.X25519.X86.stepOps_valid) fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  have b₄ := b₃.ops k₄ f₄
  refine Wp.wp_test fun s₅ u₅ z₅ => WP.block_nil ?_
  -- The values after the swaps.
  have hstep := ladderAfter_step k x1 hn
  have v₁ : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s₁.mem x q = VG.Proof.X25519.X86.F s.mem x q := F₁
  have eX2 : VG.Proof.X25519.X86.F s₃.mem x X2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).1 := by
    rw [VG.Proof.X25519.X86.F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_ite _ x₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, VG.Proof.X25519.X86.cswap_fst]
  have eX3 : VG.Proof.X25519.X86.F s₃.mem x X3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).2 := by
    rw [VG.Proof.X25519.X86.F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_ite _ y₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, VG.Proof.X25519.X86.cswap_snd]
  have eZ2 : VG.Proof.X25519.X86.F s₃.mem x Z2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).1 := by
    rw [VG.Proof.X25519.X86.F_ite _ x₃, VG.Proof.X25519.X86.F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, VG.Proof.X25519.X86.cswap_fst]
  have eZ3 : VG.Proof.X25519.X86.F s₃.mem x Z3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ VG.Proof.X25519.bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).2 := by
    rw [VG.Proof.X25519.X86.F_ite _ y₃, VG.Proof.X25519.X86.F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, VG.Proof.X25519.X86.cswap_snd]
  have eX1 : VG.Proof.X25519.X86.F s₃.mem x X1 = x1 := by
    rw [VG.Proof.X25519.X86.F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide), v₁ _ (by decide), h.vx1]
  obtain ⟨r2, rz2, r3, rz3, r1⟩ := VG.Proof.X25519.X86.run_step (VG.Proof.X25519.X86.F s₃.mem x)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  refine ⟨⟨b₄.of_frame (o := 288) (n := 640) (by rw [u₅.gpr]) (by rw [u₅.gpr]) u₅.rd u₅.wr
    (by rw [m₅]; exact Frame.refl _ _) (by decide) (by decide) (.inr (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, k₄.esi, k₃.esi, k₂.esi, esi₁]
  · rw [m₅, e₄ _ (by decide), r1, eX1]
  · rw [m₅, e₄ _ (by decide), r2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), r3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2, eX1]
  · have hs : ∀ {m m' : Mem}, Frame [VG.Proof.X25519.X86.sub x 288 640] m m' → VG.Proof.X25519.X86.wd m' x SWAP = VG.Proof.X25519.X86.wd m x SWAP := fun hf =>
      VG.Proof.X25519.X86.wd_frame1 hf hfit (by decide) (by decide) (.inl (by decide))
    rw [m₅, hs f₄, hs (VG.Proof.X25519.X86.frame2_wide hfit f₃ (by decide) (by decide)),
      hs (VG.Proof.X25519.X86.frame2_wide hfit f₂ (by decide) (by decide)), sw₁, hstep, ladderStep_eq]
  · rw [z₅, k₄.esi, k₃.esi, k₂.esi, esi₁, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The 255 iterations. -/
theorem ladderLoop_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : VG.Proof.X25519.X86.LInv x k x1 s₀ 255 s) :
    WP isa (.loop (.block VG.Impl.X25519.X86.step) .ne) s (VG.Proof.X25519.X86.LInv x k x1 s₀ 0) := by
  refine WP.loop (M := isa) (Q := VG.Proof.X25519.X86.LInv x k x1 s₀ 0) (fun m s => 1 ≤ m ∧ m ≤ 255 ∧ VG.Proof.X25519.X86.LInv x k x1 s₀ m s)
    (fun m s hm => ?_) 255 s ⟨by decide, Nat.le_refl _, h⟩
  obtain ⟨h1, h2, hL⟩ := hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (VG.Proof.X25519.X86.step_ok (by omega_using [h2]) hL) fun s' ⟨hL', hz⟩ => ?_
  by_cases e : n = 0
  · subst e
    exact .inl ⟨by simp only [eval, hz]; rfl, hL'⟩
  · exact .inr ⟨by simp only [eval, hz, e, decide_false]; rfl, n, by omega_using [],
      by omega_using [e], by omega_using [h2], hL'⟩

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Freeze`. -/
section

/-!
# X25519 on x86 (32-bit): the full reduction

`freeze o` leaves at `o` the element's value modulo `p`: bit 255 is folded in
as 19 (`V' < 2²⁵⁵ + 19 < 2p`), then `V' + 19 - 2²⁵⁵ = V' - p` is selected if it
is not negative, that is if bit 255 of `W = V' + 19` is set.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

variable {W lo : Nat}

theorem shr31_toNat (w : BitVec 32) : (w >>> 31).toNat = w.toNat / 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem low31_toNat (w : BitVec 32) : (w &&& low31).toNat = w.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_and, show low31.toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- Bit 255 of the element at `o` into the accumulator as `19 b`, and cleared. -/
theorem top_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o : Nat} (ho : o + 32 ≤ 4096) :
    WP isa (.block [.mov .eax (.mem (sc (o + 28))), .shift .shr .eax 31, .mov .edx (.imm 19), .mul .edx,
      .mov .ebx (.reg .eax), .mov .ecx (.imm 0), .mov .ebp (.imm 0),
      .mov .eax (.mem (sc (o + 28))), .alu .and .eax (.imm low31), .store (sc (o + 28)) .eax]) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x (o + 28) 4] s.mem s'.mem ∧ VG.Proof.X25519.X86.acc s' = 19 * (VG.Proof.X25519.X86.wv s.mem x (o + 28) / 2 ^ 31) ∧
        VG.Proof.X25519.X86.wv s'.mem x (o + 28) = VG.Proof.X25519.X86.wv s.mem x (o + 28) % 2 ^ 31 := by
  have hfit := hc.fit4
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by omega_using [ho]) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_shr (by decide) fun s₂ u₂ _ => Wp.wp_movi fun s₃ u₃ => VG.Proof.X25519.X86.wp_mul fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => Wp.wp_movi fun s₆ u₆ => Wp.wp_movi fun s₇ u₇ => ?_
  have k₇ : VG.Proof.X25519.X86.Keep s s₇ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans ((VG.Proof.X25519.X86.updKeep u₃).trans (u₄.keep.trans
    ((VG.Proof.X25519.X86.updKeep u₅).trans ((VG.Proof.X25519.X86.updKeep u₆).trans (VG.Proof.X25519.X86.updKeep u₇))))))
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₇ := k₇.ctx hc
  refine Wp.wp_ldm c₇.edi (c₇.inRW4 (by omega_using [ho]) (by decide)) fun s₈ u₈ => ?_
  refine Wp.wp_andi fun s₉ u₉ => ?_
  have c₉ := (VG.Proof.X25519.X86.updKeep u₉).ctx ((VG.Proof.X25519.X86.updKeep u₈).ctx c₇)
  refine Wp.wp_stm c₉.edi (c₉.inW4 (by omega_using [ho]) (by decide)) fun s₁₀ u₁₀ => WP.block_nil ?_
  have hb : VG.Proof.X25519.X86.v s₄ .eax = VG.Proof.X25519.X86.wv s.mem x (o + 28) / 2 ^ 31 * 19 := by
    rw [u₄.eax, VG.Proof.X25519.X86.v, u₃.other _ (by decide), u₂.gpr, VG.Proof.X25519.X86.v, u₃.gpr, VG.Proof.X25519.X86.shr31_toNat, u₁.gpr]
    have := VG.Proof.X25519.X86.wv_lt s.mem x (o + 28)
    exact Nat.mod_eq_of_lt (by simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢; show _ * 19 < _; omega_using [this])
  refine ⟨k₇.trans ((VG.Proof.X25519.X86.updKeep u₈).trans ((VG.Proof.X25519.X86.updKeep u₉).trans ⟨by rw [u₁₀.gpr], by rw [u₁₀.gpr],
    by rw [u₁₀.gpr], u₁₀.rd, u₁₀.wr⟩)), ?_, ?_, ?_⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, m₇]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by omega_using [ho]) (Nat.le_refl _) (Nat.le_refl _) _
  · simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₁₀.gpr, u₉.other .ebx (by decide), u₉.other .ecx (by decide),
      u₉.other .ebp (by decide), u₈.other .ebx (by decide), u₈.other .ecx (by decide),
      u₈.other .ebp (by decide), u₇.gpr, u₇.other .ebx (by decide), u₇.other .ecx (by decide), u₆.gpr,
      u₆.other .ebx (by decide), u₅.gpr, VG.Proof.X25519.X86.toNat_zero32, Nat.mul_zero, Nat.add_zero]
    simp only [VG.Proof.X25519.X86.v] at hb; rw [hb, Nat.mul_comm]
  · rw [u₁₀.mem, VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd_write_self, u₉.gpr, u₈.gpr, VG.Proof.X25519.X86.low31_toNat, m₇]

/-- The accumulator set to `c`. -/
theorem setAcc_ok {s : State} (c : BitVec 32) :
    WP isa (.block [.mov .ebx (.imm c), .mov .ecx (.imm 0), .mov .ebp (.imm 0)]) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ s'.mem = s.mem ∧ VG.Proof.X25519.X86.acc s' = c.toNat := by
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans (VG.Proof.X25519.X86.updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
    u₂.other .ebx (by decide), u₁.gpr, VG.Proof.X25519.X86.toNat_zero32, Nat.mul_zero, Nat.add_zero]

/-- The mask of bit 255 of `W` in `T` into `ecx`, and the bit cleared. -/
theorem mask_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) :
    WP isa (.block [.mov .eax (.mem (sc (VG.Impl.X25519.X86.T + 28))), .shift .shr .eax 31, .mov .ecx (.imm 0),
      .alu .sub .ecx (.reg .eax), .mov .eax (.mem (sc (VG.Impl.X25519.X86.T + 28))), .alu .and .eax (.imm low31),
      .store (sc (VG.Impl.X25519.X86.T + 28)) .eax]) s fun s' =>
      VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x (VG.Impl.X25519.X86.T + 28) 4] s.mem s'.mem ∧
        s'.gpr .ecx = VG.Proof.X25519.X86.mask (VG.Proof.X25519.X86.wv s.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31) ∧
        VG.Proof.X25519.X86.wv s'.mem x (VG.Impl.X25519.X86.T + 28) = VG.Proof.X25519.X86.wv s.mem x (VG.Impl.X25519.X86.T + 28) % 2 ^ 31 := by
  have hfit := hc.fit4
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by simp only [VG.Impl.X25519.X86.T]; decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_shr (by decide) fun s₂ u₂ _ => Wp.wp_movi fun s₃ u₃ => Wp.wp_sub fun s₄ u₄ _ => ?_
  have k₄ : VG.Proof.X25519.X86.Keep s s₄ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans ((VG.Proof.X25519.X86.updKeep u₃).trans (VG.Proof.X25519.X86.updKeep u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ := k₄.ctx hc
  refine Wp.wp_ldm c₄.edi (c₄.inRW4 (by simp only [VG.Impl.X25519.X86.T]; decide) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_andi fun s₆ u₆ => ?_
  have c₆ := (VG.Proof.X25519.X86.updKeep u₆).ctx ((VG.Proof.X25519.X86.updKeep u₅).ctx c₄)
  refine Wp.wp_stm c₆.edi (c₆.inW4 (by simp only [VG.Impl.X25519.X86.T]; decide) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  refine ⟨k₄.trans ((VG.Proof.X25519.X86.updKeep u₅).trans ((VG.Proof.X25519.X86.updKeep u₆).trans ⟨by rw [u₇.gpr], by rw [u₇.gpr],
    by rw [u₇.gpr], u₇.rd, u₇.wr⟩)), ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, m₄]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by simp only [VG.Impl.X25519.X86.T]; decide) (Nat.le_refl _) (Nat.le_refl _) _
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .eax (by decide),
      VG.Proof.X25519.X86.mask]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [u₂.gpr, VG.Proof.X25519.X86.shr31_toNat, u₁.gpr, BitVec.toNat_ofNat]
    have := VG.Proof.X25519.X86.wv_lt s.mem x (VG.Impl.X25519.X86.T + 28)
    simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢
    omega_using [this]
  · rw [u₇.mem, VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd_write_self, u₆.gpr, u₅.gpr, VG.Proof.X25519.X86.low31_toNat, m₄]

/-- The words below `n` of the element at `o` selected from `T` if `g = 1`. -/
structure SelInv (x : BitVec 32) (s₀ : State) (o g n : Nat) (s : State) : Prop where
  keep : VG.Proof.X25519.X86.Keep s₀ s
  ecx : s.gpr .ecx = s₀.gpr .ecx
  frame : Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s.mem
  done : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (o + 4 * j) = if g = 1 then VG.Proof.X25519.X86.wd s₀.mem x (VG.Impl.X25519.X86.T + 4 * j) else VG.Proof.X25519.X86.wd s₀.mem x (o + 4 * j)

theorem select_step {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o g n : Nat} (ho : VG.Proof.X25519.X86.Below o)
    (hg : g ≤ 1) (hm : s₀.gpr .ecx = VG.Proof.X25519.X86.mask g) (hn : n < 8) (h : VG.Proof.X25519.X86.SelInv x s₀ o g n s) :
    WP isa (.block [.mov .eax (.mem (sc (o + 4 * n))), .mov .edx (.mem (sc (VG.Impl.X25519.X86.T + 4 * n))),
      .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx),
      .store (sc (o + 4 * n)) .eax]) s (VG.Proof.X25519.X86.SelInv x s₀ o g (n + 1)) := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho
  have hfit := hc.fit4
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by omega_using [ho, hn]) (by decide)) fun s₁ u₁ => ?_
  have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
  refine Wp.wp_ldm c₁.edi (c₁.inRW4 (by simp only [VG.Impl.X25519.X86.T]; omega_using [hn]) (by decide)) fun s₂ u₂ => ?_
  refine Wp.wp_xor fun s₃ u₃ => Wp.wp_and fun s₄ u₄ => Wp.wp_xor fun s₅ u₅ => ?_
  have k₅ : VG.Proof.X25519.X86.Keep s s₅ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans ((VG.Proof.X25519.X86.updKeep u₃).trans ((VG.Proof.X25519.X86.updKeep u₄).trans
    (VG.Proof.X25519.X86.updKeep u₅))))
  have c₅ := k₅.ctx hc
  refine Wp.wp_stm c₅.edi (c₅.inW4 (by omega_using [ho, hn]) (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have eo : s₁.gpr .eax = VG.Proof.X25519.X86.wd s₀.mem x (o + 4 * n) := by
    rw [u₁.gpr]; exact VG.Proof.X25519.X86.wd_frame1 h.frame hfit (by omega_using [ho, hn]) (by omega_using [ho, hn])
      (.inr (Nat.le_refl _))
  have eT : s₂.gpr .edx = VG.Proof.X25519.X86.wd s₀.mem x (VG.Impl.X25519.X86.T + 4 * n) := by
    rw [u₂.gpr, u₁.mem]; exact VG.Proof.X25519.X86.wd_frame1 h.frame hfit (by omega_using [ho, hn])
      (by simp only [VG.Impl.X25519.X86.T]; omega_using [hn]) (.inr (by simp only [VG.Impl.X25519.X86.T]; omega_using [ho]))
  have v₅ : s₅.gpr .eax = if g = 1 then VG.Proof.X25519.X86.wd s₀.mem x (VG.Impl.X25519.X86.T + 4 * n) else VG.Proof.X25519.X86.wd s₀.mem x (o + 4 * n) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.other .eax (by decide),
      eo, eT, u₃.other .ecx (by decide), u₂.other .ecx (by decide), u₁.other .ecx (by decide), h.ecx, hm,
      BitVec.xor_comm (VG.Proof.X25519.X86.wd s₀.mem x (VG.Impl.X25519.X86.T + 4 * n))]
    exact (VG.Proof.X25519.X86.sel_mask _ _ hg).1
  refine ⟨h.keep.trans (k₅.trans ⟨by rw [u₆.gpr], by rw [u₆.gpr], by rw [u₆.gpr], u₆.rd, u₆.wr⟩),
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx], ?_, fun j hj => ?_⟩
  · rw [u₆.mem, m₅]
    exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden h.frame hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₆.mem, m₅]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self, v₅]
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact h.done j (by omega_using [hj, e])

theorem selects_ok {x : BitVec 32} {s₀ : State} (hc₀ : VG.Proof.X25519.X86.Ctx W x s₀) {o g : Nat} (ho : VG.Proof.X25519.X86.Below o)
    (hg : g ≤ 1) (hm : s₀.gpr .ecx = VG.Proof.X25519.X86.mask g) : ∀ n ≤ 8, ∀ s, VG.Proof.X25519.X86.SelInv x s₀ o g 0 s →
    WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.mem (sc (o + 4 * k))), .mov .edx (.mem (sc (VG.Impl.X25519.X86.T + 4 * k))), .alu .xor .edx (.reg .eax),
        .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc (o + 4 * k)) .eax])) s
      (VG.Proof.X25519.X86.SelInv x s₀ o g n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.selects_ok hc₀ ho hg hm n (by omega_using [hn]) s h)
      fun s₁ h₁ => VG.Proof.X25519.X86.select_step (h₁.keep.ctx hc₀) ho hg hm (by omega_using [hn]) h₁)

/-- The top word of an element. -/
theorem num_top (f : Nat → Nat) : VG.Proof.X25519.X86.num f 8 = VG.Proof.X25519.X86.num f 7 + 2 ^ 224 * f 7 := rfl

theorem num7_lt {f : Nat → Nat} (h : ∀ k < 7, f k < 2 ^ 32) : VG.Proof.X25519.X86.num f 7 < 2 ^ 224 := VG.Proof.X25519.X86.num_lt h

/-- The element with bit 255 folded in as 19. -/
theorem fold_top {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) :
    VG.Proof.X25519.X86.num f 8 % 2 ^ 255 = VG.Proof.X25519.X86.num f 7 + 2 ^ 224 * (f 7 % 2 ^ 31) ∧ VG.Proof.X25519.X86.num f 8 / 2 ^ 255 = f 7 / 2 ^ 31 := by
  have h7 := VG.Proof.X25519.X86.num7_lt fun k hk => h k (by omega_using [hk])
  have hf := h 7 (by decide)
  rw [VG.Proof.X25519.X86.num_top]
  have e := Nat.div_add_mod (f 7) (2 ^ 31)
  generalize f 7 / 2 ^ 31 = q at e ⊢
  generalize hr : f 7 % 2 ^ 31 = r at e ⊢
  have hr' : r < 2 ^ 31 := hr ▸ Nat.mod_lt _ (by decide)
  generalize VG.Proof.X25519.X86.num f 7 = N at h7 ⊢
  rw [← e]
  omega_using [h7, hr']

theorem freeze_eq (o : Nat) : freeze o =
    ([.mov .eax (.mem (sc (o + 28))), .shift .shr .eax 31, .mov .edx (.imm 19), .mul .edx,
      .mov .ebx (.reg .eax), .mov .ecx (.imm 0), .mov .ebp (.imm 0),
      .mov .eax (.mem (sc (o + 28))), .alu .and .eax (.imm low31), .store (sc (o + 28)) .eax] : List Instr) ++
    (cols o 8 (fun k => [.addM (o + 4 * k)]) ++
    (([.mov .ebx (.imm 19), .mov .ecx (.imm 0), .mov .ebp (.imm 0)] : List Instr) ++
    (cols VG.Impl.X25519.X86.T 8 (fun k => [.addM (o + 4 * k)]) ++
    (([.mov .eax (.mem (sc (VG.Impl.X25519.X86.T + 28))), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
      .mov .eax (.mem (sc (VG.Impl.X25519.X86.T + 28))), .alu .and .eax (.imm low31), .store (sc (VG.Impl.X25519.X86.T + 28)) .eax] : List Instr) ++
    (List.range 8).flatMap fun k =>
      [.mov .eax (.mem (sc (o + 4 * k))), .mov .edx (.mem (sc (VG.Impl.X25519.X86.T + 4 * k))), .alu .xor .edx (.reg .eax),
        .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), .store (sc (o + 4 * k)) .eax])))) := by
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]

theorem colv_addM (m : Mem) (x : BitVec 32) (d : Nat) : VG.Proof.X25519.X86.colv m x [.addM d] = VG.Proof.X25519.X86.wv m x d := by
  simp only [VG.Proof.X25519.X86.colv, VG.Proof.X25519.X86.tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The element at `o` reduced fully, in place. -/
theorem freeze_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx W x s) {o : Nat} (ho : VG.Proof.X25519.X86.isSlot lo o = true) :
    WP isa (.block (freeze o)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o = VG.Proof.X25519.X86.fe s.mem x o % P := by
  have hfit := hc.fit4
  have hob := VG.Proof.X25519.X86.slot_below ho
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hob
  rw [VG.Proof.X25519.X86.freeze_eq]
  -- The words of the element on entry.
  have hV := VG.Proof.X25519.X86.fold_top (f := fun k => VG.Proof.X25519.X86.wv s.mem x (o + 4 * k)) fun k _ => VG.Proof.X25519.X86.wv_lt _ _ _
  have hVa : VG.Proof.X25519.X86.fe s.mem x o % 2 ^ 255 = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s.mem x (o + 4 * k)) 7 +
      2 ^ 224 * (VG.Proof.X25519.X86.wv s.mem x (o + 28) % 2 ^ 31) := hV.1
  have hVb : VG.Proof.X25519.X86.fe s.mem x o / 2 ^ 255 = VG.Proof.X25519.X86.wv s.mem x (o + 28) / 2 ^ 31 := hV.2
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.top_ok hc (by omega_using [hob])) fun s₁ ⟨k₁, f₁, a₁, w₁⟩ => ?_)
  have c₁ := k₁.ctx hc
  -- `V1`: the element without bit 255.
  have e₁ : VG.Proof.X25519.X86.fe s₁.mem x o = VG.Proof.X25519.X86.fe s.mem x o % 2 ^ 255 := by
    have n7 : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₁.mem x (o + 4 * k)) 7 = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s.mem x (o + 4 * k)) 7 :=
      VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd s₁.mem x (o + 4 * j)).toNat = (VG.Proof.X25519.X86.wd s.mem x (o + 4 * j)).toNat
        rw [VG.Proof.X25519.X86.wd_frame1 f₁ hfit (by omega_using [hob]) (by omega_using [hob, hj]) (.inl (by omega_using [hj]))]
    rw [hVa, ← w₁, ← n7]
    rfl
  have hb : VG.Proof.X25519.X86.wv s.mem x (o + 28) / 2 ^ 31 ≤ 1 := by
    have := VG.Proof.X25519.X86.wv_lt s.mem x (o + 28); simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢; omega_using [this]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cols_ok c₁ (fun k => [.addM (o + 4 * k)]) 8 (by omega_using [hob])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [a₁]; omega_using [hb])) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_)
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hob, hk], .inr (Nat.le_refl _)⟩
  · rw [VG.Proof.X25519.X86.colv_addM]; have := VG.Proof.X25519.X86.wv_lt s₁.mem x (o + 4 * k); omega_using [this]
  have c₂ := k₂.ctx c₁
  -- `V' = V1 + 19 b`.
  have hs₂ : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s₁.mem x [.addM (o + 4 * k)]) 8 = VG.Proof.X25519.X86.fe s₁.mem x o :=
    VG.Proof.X25519.X86.num_congr fun k _ => VG.Proof.X25519.X86.colv_addM _ _ _
  rw [hs₂, a₁, e₁] at e₂
  have hV1 : VG.Proof.X25519.X86.fe s.mem x o % 2 ^ 255 < 2 ^ 255 := Nat.mod_lt _ (by decide)
  have eV' : VG.Proof.X25519.X86.fe s₂.mem x o = 19 * (VG.Proof.X25519.X86.fe s.mem x o / 2 ^ 255) + VG.Proof.X25519.X86.fe s.mem x o % 2 ^ 255 := by
    rw [hVb]
    change VG.Proof.X25519.X86.num _ 8 + (2 ^ 32) ^ 8 * VG.Proof.X25519.X86.acc s₂ = _ at e₂
    have : VG.Proof.X25519.X86.acc s₂ = 0 := by
      rcases Nat.eq_zero_or_pos (VG.Proof.X25519.X86.acc s₂) with h | h
      · exact h
      · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h; omega_using [this, e₂, hV1, hb]
    rw [this, Nat.mul_zero, Nat.add_zero] at e₂
    exact e₂
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.setAcc_ok (s := s₂) 19) fun s₃ ⟨k₃, m₃, a₃⟩ => ?_)
  have c₃ := k₃.ctx c₂
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cols_ok c₃ (fun k => [.addM (o + 4 * k)]) 8 (by simp only [VG.Impl.X25519.X86.T]; decide)
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) (by rw [a₃]; decide)) fun s₄ ⟨k₄, f₄, e₄, _⟩ => ?_)
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [VG.Proof.X25519.X86.treads, List.mem_singleton] at hd; subst hd
    exact ⟨by omega_using [hob, hk], .inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hob, hk])⟩
  · rw [VG.Proof.X25519.X86.colv_addM]; have := VG.Proof.X25519.X86.wv_lt s₃.mem x (o + 4 * k); omega_using [this]
  have c₄ := k₄.ctx c₃
  -- `W = V' + 19`.
  have hs₄ : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.colv s₃.mem x [.addM (o + 4 * k)]) 8 = VG.Proof.X25519.X86.fe s₂.mem x o := by
    rw [m₃]; exact VG.Proof.X25519.X86.num_congr fun k _ => VG.Proof.X25519.X86.colv_addM _ _ _
  rw [hs₄, a₃, show (19 : BitVec 32).toNat = 19 from rfl] at e₄
  have eW : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) 8 = VG.Proof.X25519.X86.fe s₂.mem x o + 19 := by
    change VG.Proof.X25519.X86.num _ 8 + (2 ^ 32) ^ 8 * VG.Proof.X25519.X86.acc s₄ = _ at e₄
    have : VG.Proof.X25519.X86.acc s₄ = 0 := by
      rcases Nat.eq_zero_or_pos (VG.Proof.X25519.X86.acc s₄) with h | h
      · exact h
      · have := Nat.mul_le_mul_left ((2 ^ 32) ^ 8) h
        rw [eV'] at e₄; omega_using [this, e₄, hV1, hb, hVb]
    rw [this, Nat.mul_zero, Nat.add_zero] at e₄
    rw [e₄]; omega_using []
  have hW := VG.Proof.X25519.X86.fold_top (f := fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) fun k _ => VG.Proof.X25519.X86.wv_lt _ _ _
  have hWa : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) 8 % 2 ^ 255 = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) 7 +
      2 ^ 224 * (VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) % 2 ^ 31) := hW.1
  have hWb : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) 8 / 2 ^ 255 = VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31 := hW.2
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.mask_ok c₄) fun s₅ ⟨k₅, f₅, m₅, w₅⟩ => ?_)
  have c₅ := k₅.ctx c₄
  have hg : VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31 ≤ 1 := by
    have := VG.Proof.X25519.X86.wv_lt s₄.mem x (VG.Impl.X25519.X86.T + 28); simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd] at this ⊢; omega_using [this]
  have hoT : ∀ j < 8, VG.Proof.X25519.X86.wd s₅.mem x (o + 4 * j) = VG.Proof.X25519.X86.wd s₂.mem x (o + 4 * j) := fun j hj => by
    rw [VG.Proof.X25519.X86.wd_frame1 f₅ hfit (by simp only [VG.Impl.X25519.X86.T]; decide) (by omega_using [hob, hj])
      (.inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hob, hj])), VG.Proof.X25519.X86.wd_frame1 f₄ hfit (by simp only [VG.Impl.X25519.X86.T]; decide)
      (by omega_using [hob, hj]) (.inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hob, hj])), m₃]
  -- `T` now holds `W mod 2²⁵⁵`.
  have eT : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₅.mem x (VG.Impl.X25519.X86.T + 4 * k)) 8 = (VG.Proof.X25519.X86.fe s₂.mem x o + 19) % 2 ^ 255 := by
    have n7 : VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₅.mem x (VG.Impl.X25519.X86.T + 4 * k)) 7 = VG.Proof.X25519.X86.num (fun k => VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 4 * k)) 7 :=
      VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.wd s₅.mem x (VG.Impl.X25519.X86.T + 4 * j)).toNat = (VG.Proof.X25519.X86.wd s₄.mem x (VG.Impl.X25519.X86.T + 4 * j)).toNat
        rw [VG.Proof.X25519.X86.wd_frame1 f₅ hfit (by simp only [VG.Impl.X25519.X86.T]; decide) (by simp only [VG.Impl.X25519.X86.T]; omega_using [hj])
          (.inl (by simp only [VG.Impl.X25519.X86.T]; omega_using [hj]))]
    rw [← eW, hWa, ← w₅, ← n7]
    rfl
  refine WP.mono (VG.Proof.X25519.X86.selects_ok c₅ (o := o) (g := VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31) (by simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T]; omega_using [hob]) hg m₅ 8
    (Nat.le_refl _) s₅ ⟨Keep.refl _, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun s₆ h₆ => ⟨k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans h₆.keep)))), ?_, ?_⟩
  · -- Everything written is in the element and `T`.
    have w1 : ∀ {m m' : Mem} {a n : Nat}, Frame [VG.Proof.X25519.X86.sub x a n] m m' →
        o ≤ a → a + n ≤ o + 32 → a < 4096 → Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] m m' := fun hf h1 h2 h3 =>
      (VG.Proof.X25519.X86.frameWiden hf hfit h1 h2 h3).mono (fun r hr => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
    have w2 : ∀ {m m' : Mem} {a n : Nat}, Frame [VG.Proof.X25519.X86.sub x a n] m m' →
        VG.Impl.X25519.X86.T ≤ a → a + n ≤ VG.Impl.X25519.X86.T + 32 → a < 4096 → Frame [VG.Proof.X25519.X86.sub x o 32, VG.Proof.X25519.X86.sub x VG.Impl.X25519.X86.T 32] m m' := fun hf h1 h2 h3 =>
      (VG.Proof.X25519.X86.frameWiden hf hfit h1 h2 h3).mono (fun r hr => List.mem_cons_of_mem _ hr)
    rw [m₃] at f₄
    exact (w1 f₁ (by omega_using []) (by omega_using []) (by omega_using [hob])).trans
      ((w1 f₂ (by omega_using []) (by omega_using []) (by omega_using [hob])).trans
      ((w2 f₄ (by decide) (by decide) (by decide)).trans
      ((w2 f₅ (by simp only [VG.Impl.X25519.X86.T]; decide) (by simp only [VG.Impl.X25519.X86.T]; decide) (by simp only [VG.Impl.X25519.X86.T]; decide)).trans
      (w1 h₆.frame (by omega_using []) (by omega_using []) (by omega_using [hob])))))
  · -- The selection is the value modulo `p`.
    have e₆ : VG.Proof.X25519.X86.fe s₆.mem x o = if VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31 = 1 then (VG.Proof.X25519.X86.fe s₂.mem x o + 19) % 2 ^ 255
        else VG.Proof.X25519.X86.fe s₂.mem x o := by
      rw [← eT]
      split
      · exact VG.Proof.X25519.X86.num_congr fun j hj => by
          show (VG.Proof.X25519.X86.wd s₆.mem x (o + 4 * j)).toNat = (VG.Proof.X25519.X86.wd s₅.mem x (VG.Impl.X25519.X86.T + 4 * j)).toNat
          rw [h₆.done j hj, ite_eq_left ‹_›]
      · exact VG.Proof.X25519.X86.num_congr fun j hj => by
          show (VG.Proof.X25519.X86.wd s₆.mem x (o + 4 * j)).toNat = (VG.Proof.X25519.X86.wd s₂.mem x (o + 4 * j)).toNat
          rw [h₆.done j hj, ite_eq_right ‹_›, hoT j hj]
    have hWb' : VG.Proof.X25519.X86.wv s₄.mem x (VG.Impl.X25519.X86.T + 28) / 2 ^ 31 = (VG.Proof.X25519.X86.fe s₂.mem x o + 19) / 2 ^ 255 := by
      rw [← eW, hWb]
    rw [e₆, hWb']
    have hmod : VG.Proof.X25519.X86.fe s₂.mem x o % P = VG.Proof.X25519.X86.fe s.mem x o % P := by
      rw [eV', Nat.add_comm, ← fold255, Nat.mul_comm, Nat.mod_add_div']
    rw [← hmod]
    have hlt : VG.Proof.X25519.X86.fe s₂.mem x o < P + 38 := by rw [eV']; simp only [P]; omega_using [hV1, hb, hVb]
    simp only [P] at hlt ⊢
    split <;> rename_i hsplit <;> omega_using [hlt, hsplit]

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Setup`. -/
section

/-!
# X25519 on x86 (32-bit): reading the arguments

`save` stores the callee-saved registers in the working space, `loadPoint` the
u-coordinate (its top bit masked) in `X1`, `loadScalar` the bits of the scalar
in `BITS` (clamped), and `initLadder` the ladder's initial state; so the
ladder starts with `LInv 255`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem save_eq : save = .mov .eax (.mem (at_ .esp 16)) :: (Spill.saveCode .eax VG.Proof.X25519.X86.savedSlots ++
    ([.mov .edi (.reg .eax)] : List Instr)) := rfl

/-- What `save` leaves. -/
structure Saved (s₀ s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.X25519.X86.scR 4096 (arg s₀ 3)] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr (arg s₀ 3)) s₀.gpr VG.Proof.X25519.X86.savedSlots

theorem save_ok {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) : WP isa (.block save) s₀ (VG.Proof.X25519.X86.Saved s₀) := by
  have hfit := hp.sc_fit
  rw [VG.Proof.X25519.X86.save_eq]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 16) rfl (hp.argIn (i := 3) (by decide)) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ 3 := u₁.gpr
  have inW : ∀ {s : State} {d : Nat}, s.wr = s₀.wr → d + 4 ≤ 4096 → InRegions s.wr (addr (arg s₀ 3) d) 4 :=
    fun hw hd => ⟨_, hw ▸ hp.sc_in, VG.Proof.X25519.X86.scR_contains hfit hd (by decide)⟩
  refine Spill.save_ok VG.Proof.X25519.X86.savedSlots (fun p h => by
    rw [ea]; exact inW u₁.wr (by have := VG.Proof.X25519.X86.savedSlots_bound p h; omega_using [this])) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hr : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have hm : s₆.mem = Spill.saveMem s₀.mem (addr (arg s₀ 3)) s₀.gpr VG.Proof.X25519.X86.savedSlots := by
    rw [u₆.mem, u₅.mem, ea, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => hr _ (by revert p h; decide)
  refine ⟨by rw [u₆.gpr, u₅.gpr, ea], by rw [u₆.other _ (by decide), u₅.gpr, hr _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₁.wr], ?_, ?_⟩
  · rw [hm]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      VG.Proof.X25519.X86.scR_contains hfit (by have := VG.Proof.X25519.X86.savedSlots_bound p h; omega_using [this]) (by decide)
  · rw [hm]; exact Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by omega_using [hfit])

/-- A store to the working space above the saved registers keeps `Saved`. -/
theorem Saved.write {s₀ s s' : State} (hp : VG.Proof.X25519.X86.Pre s₀) (h : VG.Proof.X25519.X86.Saved s₀ s) {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 4096) (hg : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {v : BitVec 32} (hm : s'.mem = s.mem.writeW (addr (arg s₀ 3) d) v) : VG.Proof.X25519.X86.Saved s₀ s' := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.X25519.X86.scR_contains hfit hd' (by decide))
  · have := VG.Proof.X25519.X86.savedSlots_bound p hp
    rw [hm]
    exact VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, this]) (by omega_using [hfit, hd']) (.inl (by omega_using [this, hd]))

/-- The words of the u-coordinate, on entry. -/
abbrev pw (s₀ : State) (k : Nat) : BitVec 32 := VG.Proof.X25519.X86.wd s₀.mem (arg s₀ 2) (4 * k)

/-- The words `X1` receives: those of the u-coordinate, the top bit masked. -/
def pv (s₀ : State) (k : Nat) : BitVec 32 := if k = 7 then VG.Proof.X25519.X86.pw s₀ 7 &&& low31 else VG.Proof.X25519.X86.pw s₀ k

/-- A word of the u-coordinate, unchanged. -/
theorem point_contains {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) {k : Nat} (hk : k < 8) :
    (VG.Proof.X25519.X86.pointR s₀).Contains (addr (arg s₀ 2) (4 * k)) 4 := by
  have := VG.Proof.X25519.X86.sub_contains (x := arg s₀ 2) (a := 0) (k := 32) (d := 4 * k) (n := 4)
    (by have := hp.point_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)
  rwa [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero] at this

/-- A word of the u-coordinate, unchanged. -/
theorem Saved.pw {s₀ s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (h : VG.Proof.X25519.X86.Saved s₀ s) {k : Nat} (hk : k < 8) :
    VG.Proof.X25519.X86.wd s.mem (arg s₀ 2) (4 * k) = VG.Proof.X25519.X86.pw s₀ k :=
  h.frame.readW (VG.Proof.X25519.X86.point_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.point_sc) (by decide)

theorem loadWord_ok {s₀ s : State} (hp : VG.Proof.X25519.X86.Pre s₀) {n : Nat} (hn : n < 8)
    (h : VG.Proof.X25519.X86.Saved s₀ s) (hesi : s.gpr .esi = arg s₀ 2) (hw : ∀ j < n, VG.Proof.X25519.X86.wd s.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j) :
    WP isa (.block (([.mov .eax (.mem (at_ .esi (4 * n)))] : List Instr) ++
      (if n = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * n)) .eax] : List Instr))) s fun s' =>
      VG.Proof.X25519.X86.Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, VG.Proof.X25519.X86.wd s'.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j := by
  have hfit := hp.sc_fit
  have hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 2) (4 * n)) 4 :=
    ⟨VG.Proof.X25519.X86.pointR s₀, by rw [h.rd, hp.rd]; simp, VG.Proof.X25519.X86.point_contains hp hn⟩
  simp only [List.cons_append, List.nil_append]
  refine Wp.wp_ldm hesi hin fun s₁ u₁ => ?_
  -- The rest, from the value `w` in `eax`.
  have fin : ∀ (s₂ : State) (w : BitVec 32), s₂.gpr .eax = w → w = VG.Proof.X25519.X86.pv s₀ n → s₂.gpr .edi = s.gpr .edi →
      s₂.gpr .esp = s.gpr .esp → s₂.gpr .esi = s.gpr .esi → s₂.rd = s.rd → s₂.wr = s.wr → s₂.mem = s.mem →
      WP isa (.block [.store (sc (X1 + 4 * n)) .eax]) s₂ fun s' =>
        VG.Proof.X25519.X86.Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, VG.Proof.X25519.X86.wd s'.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j := by
    intro s₂ w ew hw' g1 g2 g3 g4 g5 g6
    refine Wp.wp_stm (by rw [g1]; exact h.edi) ⟨_, by rw [g5, h.wr]; exact hp.sc_in,
      VG.Proof.X25519.X86.scR_contains hfit (by simp only [X1]; omega_using [hn]) (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    refine ⟨h.write hp (d := X1 + 4 * n) (by simp only [X1]; omega_using []) (by simp only [X1]; omega_using [hn])
      (by rw [u₃.gpr, g1]) (by rw [u₃.gpr, g2]) (by rw [u₃.rd, g4]) (by rw [u₃.wr, g5]) (by rw [u₃.mem, g6]),
      by rw [u₃.gpr, g3, hesi], fun j hj => ?_⟩
    rw [u₃.mem, g6]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self, ew, hw']
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by simp only [X1]; omega_using [hfit, hj, hn]) (by simp only [X1]; omega_using [hfit, hn])
        (by omega_using [e])]
      exact hw j (by omega_using [hj, e])
  have e₁ : s₁.gpr .eax = VG.Proof.X25519.X86.pw s₀ n := by rw [u₁.gpr]; exact h.pw hp hn
  by_cases h7 : n = 7
  · subst h7
    simp only [ite_true, List.cons_append, List.nil_append]
    refine Wp.wp_andi fun s₂ u₂ => fin s₂ _ u₂.gpr ?_ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])
    rw [e₁]; rfl
  · simp only [h7, ite_false, List.nil_append]
    exact fin s₁ _ rfl (by rw [e₁, VG.Proof.X25519.X86.pv, ite_eq_right h7]) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.mem

theorem loadWords_ok {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) : ∀ n ≤ 8, ∀ s, VG.Proof.X25519.X86.Saved s₀ s → s.gpr .esi = arg s₀ 2 →
    WP isa (.block ((List.range n).flatMap fun k => ([.mov .eax (.mem (at_ .esi (4 * k)))] : List Instr) ++
      (if k = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * k)) .eax] : List Instr))) s fun s' =>
      VG.Proof.X25519.X86.Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n, VG.Proof.X25519.X86.wd s'.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j
  | 0, _, _, h, he => WP.block_nil ⟨h, he, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.loadWords_ok hp n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁, w₁⟩ =>
      VG.Proof.X25519.X86.loadWord_ok hp (by omega_using [hn]) h₁ e₁ w₁)

theorem loadPoint_ok {s₀ s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (h : VG.Proof.X25519.X86.Saved s₀ s) :
    WP isa (.block loadPoint) s fun s' => VG.Proof.X25519.X86.Saved s₀ s' ∧ ∀ j < 8, VG.Proof.X25519.X86.wd s'.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j := by
  refine Wp.wp_ldm (B := s.gpr .esp) (o := 12) rfl (by rw [h.esp, h.rd, h.wr]; exact hp.argIn (i := 2) (by decide))
    fun s₁ u₁ => ?_
  have h₁ : VG.Proof.X25519.X86.Saved s₀ s₁ := ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
    by rw [u₁.rd]; exact h.rd, by rw [u₁.wr]; exact h.wr, by rw [u₁.mem]; exact h.frame,
    by rw [u₁.mem]; exact h.saved⟩
  have e₁ : s₁.gpr .esi = arg s₀ 2 := by
    rw [u₁.gpr, h.esp]; exact hp.arg_same h.frame (i := 2) (by decide)
  exact WP.mono (VG.Proof.X25519.X86.loadWords_ok hp 8 (Nat.le_refl _) s₁ h₁ e₁) fun s' ⟨h', _, w'⟩ => ⟨h', w'⟩

/-! ## The scalar's bits -/

theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Wp.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store8, ea_mk, ha, hout, ↓reduceIte]

theorem byte_write_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem byte_write_ne (m : Mem) {x : BitVec 32} (v : BitVec 8) {d e : Nat} (hd : x.toNat + d + 1 ≤ 2 ^ 32)
    (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) : (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := VG.Proof.X25519.X86.sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])

theorem Saved.of_frame {s₀ sA s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (h : VG.Proof.X25519.X86.Saved s₀ sA) {o n : Nat}
    (hf : Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) o n] sA.mem s.mem) (ho : 16 ≤ o) (hon : o + n ≤ 4096) (hn : o < 4096)
    (hg : s.gpr .edi = sA.gpr .edi) (hesp : s.gpr .esp = sA.gpr .esp) (hrd : s.rd = sA.rd) (hwr : s.wr = sA.wr) :
    VG.Proof.X25519.X86.Saved s₀ s := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hfit (Nat.zero_le _) (by omega_using [hon]) hn⟩)
  · have := VG.Proof.X25519.X86.savedSlots_bound p hp
    exact VG.Proof.X25519.X86.wd_frame1 hf hfit hon (by omega_using [this]) (.inl (by omega_using [this, ho]))

/-- Byte `i` of the scalar, on entry. -/
abbrev sb (s₀ : State) (i : Nat) : Nat := (s₀.mem (addr (arg s₀ 1) i)).toNat

/-- The bits stored so far. -/
structure BInv (s₀ sA : State) (t : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esi : s.gpr .esi = arg s₀ 1
  esp : s.gpr .esp = sA.gpr .esp
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  frame : Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) BITS 256] sA.mem s.mem
  bits : ∀ u < t, s.mem (addr (arg s₀ 3) (BITS + u)) = BitVec.ofNat 8 ((VG.Proof.X25519.X86.sb s₀ (u / 8) >>> (u % 8)) &&& 1)

theorem bit_toNat {b : Nat} (hb : b < 256) (j : Nat) :
    ((BitVec.ofNat 32 b >>> j) &&& 1).toNat = (b >>> j) &&& 1 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
  rfl

theorem setWidth8_bit (w : BitVec 32) {b : Nat} (h : w.toNat = b) :
    w.setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

theorem and_one_le (n : Nat) : n &&& 1 ≤ 1 := Nat.le_of_lt_succ (Nat.and_lt_two_pow n (by decide : 1 < 2 ^ 1))

theorem bitOf_ok {s₀ sA s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hsA : sA.wr = s₀.wr) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h : VG.Proof.X25519.X86.BInv s₀ sA (8 * i + j) s) (heax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.X25519.X86.sb s₀ i)) :
    WP isa (.block (bitOf i j)) s fun s' => VG.Proof.X25519.X86.BInv s₀ sA (8 * i + j + 1) s' ∧ s'.gpr .eax = s.gpr .eax := by
  have hfit := hp.sc_fit
  have hbl : VG.Proof.X25519.X86.sb s₀ i < 256 := BitVec.isLt _
  -- The last two instructions, from `edx = eax >>> j`.
  have fin : ∀ s₁, s₁.gpr .edx = s.gpr .eax >>> j → s₁.gpr .eax = s.gpr .eax → s₁.gpr .edi = s.gpr .edi →
      s₁.gpr .esi = s.gpr .esi → s₁.gpr .esp = s.gpr .esp → s₁.rd = s.rd → s₁.wr = s.wr → s₁.mem = s.mem →
      WP isa (.block [.alu .and .edx (.imm 1), .store8 (sc (BITS + 8 * i + j)) .dl]) s₁ fun s' =>
        VG.Proof.X25519.X86.BInv s₀ sA (8 * i + j + 1) s' ∧ s'.gpr .eax = s.gpr .eax := by
    intro s₁ e1 a1 g1 g2 g3 g4 g5 g6
    refine Wp.wp_andi fun s₂ u₂ => ?_
    refine VG.Proof.X25519.X86.wp_store8 (a := addr (arg s₀ 3) (BITS + 8 * i + j)) (by rw [u₂.other _ (by decide), g1, h.edi])
      ⟨_, by rw [u₂.wr, g5, h.wr, hsA]; exact hp.sc_in, VG.Proof.X25519.X86.scR_contains hfit (by simp only [BITS]; omega_using [hi, hj])
        (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    have ev : ((s₂.gpr (Reg8.dl).reg).setWidth 8) = BitVec.ofNat 8 ((VG.Proof.X25519.X86.sb s₀ i >>> j) &&& 1) := by
      refine VG.Proof.X25519.X86.setWidth8_bit _ ?_
      show (s₂.gpr .edx).toNat = _
      rw [u₂.gpr, e1, heax, VG.Proof.X25519.X86.bit_toNat hbl]
    have m₃ : s₃.mem = s.mem.writeW (addr (arg s₀ 3) (BITS + 8 * i + j)) (BitVec.ofNat 8 ((VG.Proof.X25519.X86.sb s₀ i >>> j) &&& 1)) := by
      rw [u₃.mem, ev, u₂.mem, g6]
    refine ⟨⟨by rw [u₃.gpr, u₂.other _ (by decide), g1, h.edi], by rw [u₃.gpr, u₂.other _ (by decide), g2, h.esi],
      by rw [u₃.gpr, u₂.other _ (by decide), g3, h.esp], by rw [u₃.rd, u₂.rd, g4, h.rd],
      by rw [u₃.wr, u₂.wr, g5, h.wr], ?_, fun u hu => ?_⟩, by rw [u₃.gpr, u₂.other _ (by decide), a1]⟩
    · rw [m₃]
      exact h.frame.writeW (List.mem_singleton_self _) _
        (VG.Proof.X25519.X86.sub_contains (by simp only [BITS]; omega_using [hfit]) (by simp only [BITS]; omega_using [])
          (by simp only [BITS]; omega_using [hi, hj])
          (by decide))
    · rw [m₃]
      by_cases e : u = 8 * i + j
      · subst e
        rw [show BITS + (8 * i + j) = BITS + 8 * i + j by omega_using [], VG.Proof.X25519.X86.byte_write_self,
          show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]
      · rw [VG.Proof.X25519.X86.byte_write_ne _ _ (by simp only [BITS]; omega_using [hfit, hu, hi, hj])
          (by simp only [BITS]; omega_using [hfit, hi, hj]) (by omega_using [e])]
        exact h.bits u (by omega_using [hu, e])
  simp only [bitOf]
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.nil_append, List.cons_append]
    refine Wp.wp_mov fun s₁ u₁ => fin s₁ (by rw [u₁.gpr]; exact (BitVec.ushiftRight_zero _).symm)
      (u₁.other _ (by decide)) (u₁.other _ (by decide)) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      u₁.rd u₁.wr u₁.mem
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine Wp.wp_mov fun s₁ u₁ => Wp.wp_shr ⟨by omega_using [h0], by omega_using [hj]⟩ fun s₂ u₂ _ =>
      fin s₂ (by rw [u₂.gpr, u₁.gpr]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])

theorem bitsOf_ok {s₀ sA : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hsA : sA.wr = s₀.wr) {i : Nat} (hi : i < 32) :
    ∀ n ≤ 8, ∀ s, VG.Proof.X25519.X86.BInv s₀ sA (8 * i) s → s.gpr .eax = BitVec.ofNat 32 (VG.Proof.X25519.X86.sb s₀ i) →
    WP isa (.block ((List.range n).flatMap fun j => bitOf i j)) s fun s' =>
      VG.Proof.X25519.X86.BInv s₀ sA (8 * i + n) s' ∧ s'.gpr .eax = s.gpr .eax
  | 0, _, _, h, _ => WP.block_nil ⟨h, rfl⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.bitsOf_ok hp hsA hi n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁⟩ => ?_)
    exact WP.mono (VG.Proof.X25519.X86.bitOf_ok hp hsA hi (by omega_using [hn]) h₁ (by rw [e₁, he])) fun s₂ ⟨h₂, e₂⟩ =>
      ⟨h₂, e₂.trans e₁⟩

theorem scalar_contains {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) {i : Nat} (hi : i < 32) :
    (VG.Proof.X25519.X86.scalarR s₀).Contains (addr (arg s₀ 1) i) 1 := by
  have := VG.Proof.X25519.X86.sub_contains (x := arg s₀ 1) (a := 0) (k := 32) (d := i) (n := 1)
    (by have := hp.scalar_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hi]) (by decide)
  rwa [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero] at this

theorem bytes_ok {s₀ sA : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hA : VG.Proof.X25519.X86.Saved s₀ sA) : ∀ n ≤ 32, ∀ s, VG.Proof.X25519.X86.BInv s₀ sA 0 s →
    WP isa (.block ((List.range n).flatMap fun i => .movzx8 .eax (at_ .esi i) ::
      (List.range 8).flatMap fun j => bitOf i j)) s (VG.Proof.X25519.X86.BInv s₀ sA (8 * n))
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ (n := n), List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.bytes_ok hp hA n (by omega_using [hn]) s h) fun s₁ h₁ => ?_)
    have hfit := hp.sc_fit
    -- The byte of the scalar, unchanged.
    have hsame : s₁.mem (addr (arg s₀ 1) n) = s₀.mem (addr (arg s₀ 1) n) := by
      have f : Frame [VG.Proof.X25519.X86.scR 4096 (arg s₀ 3)] s₀.mem s₁.mem := hA.frame.trans (h₁.frame.sub fun _ hr =>
        ⟨_, List.mem_singleton_self _, by
          rw [List.mem_singleton.mp hr, VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hfit (Nat.zero_le _) (by simp only [BITS]; decide)
            (by simp only [BITS]; decide)⟩)
      exact f _ fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hp.scalar_sc _ (VG.Proof.X25519.X86.scalar_contains hp (by omega_using [hn]))
    refine VG.Proof.X25519.X86.wp_movzx8 (a := addr (arg s₀ 1) n) (by rw [h₁.esi])
      ⟨VG.Proof.X25519.X86.scalarR s₀, by rw [h₁.rd, hA.rd, hp.rd]; simp, VG.Proof.X25519.X86.scalar_contains hp (by omega_using [hn])⟩ fun s₂ u₂ => ?_
    have h₂ : VG.Proof.X25519.X86.BInv s₀ sA (8 * n) s₂ := ⟨by rw [u₂.other _ (by decide)]; exact h₁.edi,
      by rw [u₂.other _ (by decide)]; exact h₁.esi, by rw [u₂.other _ (by decide)]; exact h₁.esp,
      by rw [u₂.rd]; exact h₁.rd, by rw [u₂.wr]; exact h₁.wr, by rw [u₂.mem]; exact h₁.frame,
      by rw [u₂.mem]; exact h₁.bits⟩
    have e₂ : s₂.gpr .eax = BitVec.ofNat 32 (VG.Proof.X25519.X86.sb s₀ n) := by
      rw [u₂.gpr, hsame]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact WP.mono (VG.Proof.X25519.X86.bitsOf_ok hp (by rw [hA.wr]) (by omega_using [hn]) 8 (Nat.le_refl _) s₂ h₂ e₂)
      fun s₃ ⟨h₃, _⟩ => by rw [show 8 * (n + 1) = 8 * n + 8 by omega_using []]; exact h₃

theorem kb_getD {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) {i : Nat} (hi : i < 32) :
    (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).getD i 0 = s₀.mem (addr (arg s₀ 1) i) := by
  simp only [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  rw [addr_eq (by have := hp.scalar_fit; omega_using [this, hi])]

theorem length_kb (s₀ : State) : (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).length = 32 := by
  simp [Spec.X25519.bytesAt]

theorem loadScalar_eq : loadScalar = .mov .esi (.mem (at_ .esp 8)) ::
    (((List.range 32).flatMap fun i => .movzx8 .eax (at_ .esi i) :: (List.range 8).flatMap fun j => bitOf i j) ++
    ([.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl, .store8 (sc (BITS + 2)) .dl,
      .mov .edx (.imm 1), .store8 (sc (BITS + 254)) .dl] : List Instr)) := rfl

/-- The scalar's bits, clamped: bit `t` of the decoded scalar at `BITS + t`. -/
theorem loadScalar_ok {s₀ sA : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hA : VG.Proof.X25519.X86.Saved s₀ sA) :
    WP isa (.block loadScalar) sA fun s' => VG.Proof.X25519.X86.Saved s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) BITS 256] sA.mem s'.mem ∧
      ∀ t < 255, s'.mem (addr (arg s₀ 3) (BITS + t)) = BitVec.ofNat 8
        (VG.Proof.X25519.bit (decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) t) := by
  have hfit := hp.sc_fit
  rw [VG.Proof.X25519.X86.loadScalar_eq]
  refine Wp.wp_ldm (B := sA.gpr .esp) (o := 8) rfl (by rw [hA.esp, hA.rd, hA.wr]; exact hp.argIn (i := 1) (by decide))
    fun s₁ u₁ => ?_
  have h₁ : VG.Proof.X25519.X86.BInv s₀ sA 0 s₁ := ⟨by rw [u₁.other _ (by decide)]; exact hA.edi,
    by rw [u₁.gpr, hA.esp]; exact hp.arg_same hA.frame (i := 1) (by decide), u₁.other _ (by decide), u₁.rd,
    u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.bytes_ok hp hA 32 (Nat.le_refl _) s₁ h₁) fun s₂ h₂ => ?_)
  have inb : ∀ {s : State} {d : Nat}, s.wr = sA.wr → d < 256 →
      InRegions s.wr (addr (arg s₀ 3) (BITS + d)) 1 := fun hw hd =>
    ⟨_, by rw [hw, hA.wr]; exact hp.sc_in, VG.Proof.X25519.X86.scR_contains hfit (by simp only [BITS]; omega_using [hd]) (by decide)⟩
  refine Wp.wp_movi fun s₃ u₃ => ?_
  have edi₃ : s₃.gpr .edi = arg s₀ 3 := by rw [u₃.other _ (by decide)]; exact h₂.edi
  refine VG.Proof.X25519.X86.wp_store8 (a := addr (arg s₀ 3) (BITS + 0)) (by rw [edi₃]; rfl) (inb (by rw [u₃.wr, h₂.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine VG.Proof.X25519.X86.wp_store8 (a := addr (arg s₀ 3) (BITS + 1)) (by rw [u₄.gpr, edi₃])
    (inb (by rw [u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.X25519.X86.wp_store8 (a := addr (arg s₀ 3) (BITS + 2)) (by rw [u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  refine VG.Proof.X25519.X86.wp_store8 (a := addr (arg s₀ 3) (BITS + 254)) (by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have z3 : ((s₃.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by simp only [Reg8.reg, u₃.gpr]; decide
  have z4 : ((s₄.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₄.gpr]; exact z3
  have z5 : ((s₅.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₅.gpr]; exact z4
  have o : ((s₇.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 1 := by simp only [Reg8.reg, u₇.gpr]; decide
  have m₈ : s₈.mem = ((((s₂.mem.writeW (addr (arg s₀ 3) (BITS + 0)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 1)) (0 : BitVec 8)).writeW (addr (arg s₀ 3) (BITS + 2)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 254)) (1 : BitVec 8)) := by
    rw [u₈.mem, o, u₇.mem, u₆.mem, z5, u₅.mem, z4, u₄.mem, z3, u₃.mem]
  have g : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r hr => by
    rw [u₈.gpr, u₇.other _ hr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ hr]
  have hb : ∀ {m : Mem} {d : Nat} (v : BitVec 8), d < 256 → Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) BITS 256] sA.mem m →
      Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) BITS 256] sA.mem (m.writeW (addr (arg s₀ 3) (BITS + d)) v) := fun v hd hf =>
    hf.writeW (List.mem_singleton_self _) _ (VG.Proof.X25519.X86.sub_contains (by simp only [BITS]; omega_using [hfit])
      (by omega_using []) (by omega_using [hd]) (by decide))
  have f₈ : Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) BITS 256] sA.mem s₈.mem := by
    rw [m₈]; exact hb _ (by decide) (hb _ (by decide) (hb _ (by decide) (hb _ (by decide) h₂.frame)))
  refine ⟨hA.of_frame hp f₈ (by decide) (by decide) (by decide) (by rw [g _ (by decide), h₂.edi, hA.edi])
    (by rw [g _ (by decide), h₂.esp]) (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]), f₈, fun t ht => ?_⟩
  rw [scalar_bit (VG.Proof.X25519.X86.length_kb s₀) ht, m₈]
  have ne : ∀ (m : Mem) (v : BitVec 8) (e : Nat), e < 256 → t ≠ e →
      (m.writeW (addr (arg s₀ 3) (BITS + e)) v) (addr (arg s₀ 3) (BITS + t)) = m (addr (arg s₀ 3) (BITS + t)) :=
    fun m v e he h => VG.Proof.X25519.X86.byte_write_ne m v (by simp only [BITS]; omega_using [hfit, ht])
      (by simp only [BITS]; omega_using [hfit, he]) (by omega_using [h])
  by_cases h3 : t < 3
  · rw [ite_eq_left h3, ne _ _ 254 (by decide) (by omega_using [h3])]
    rcases (by omega_using [h3] : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    · rw [ne _ _ 2 (by decide) (by decide), ne _ _ 1 (by decide) (by decide), VG.Proof.X25519.X86.byte_write_self]; rfl
    · rw [ne _ _ 2 (by decide) (by decide), VG.Proof.X25519.X86.byte_write_self]; rfl
    · rw [VG.Proof.X25519.X86.byte_write_self]; rfl
  · rw [ite_eq_right h3]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, VG.Proof.X25519.X86.byte_write_self]; rfl
    · rw [ite_eq_right h254, ne _ _ 254 (by decide) h254, ne _ _ 2 (by decide) (by omega_using [h3]),
        ne _ _ 1 (by decide) (by omega_using [h3]), ne _ _ 0 (by decide) (by omega_using [h3]),
        h₂.bits t (by omega_using [ht]), VG.Proof.X25519.X86.kb_getD hp (by omega_using [ht])]

/-! ## The ladder's initial state -/

theorem setSmall_step {x : BitVec 32} {s₀ s : State} (hc : VG.Proof.X25519.X86.Ctx 4096 x s) {o n : Nat} (ho : VG.Proof.X25519.X86.Below o) (hn : n < 8)
    (c : BitVec 32) (hk : VG.Proof.X25519.X86.Keep s₀ s) (hf : Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, VG.Proof.X25519.X86.wd s.mem x (o + 4 * j) = if j = 0 then c else 0) :
    WP isa (.block [.mov .eax (.imm (if n = 0 then c else 0)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      VG.Proof.X25519.X86.Keep s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = if j = 0 then c else 0 := by
  simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  have c₁ := (VG.Proof.X25519.X86.updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((VG.Proof.X25519.X86.updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact VG.Proof.X25519.X86.frame_write1 (VG.Proof.X25519.X86.frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self, u₁.gpr]
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem setSmalls_ok {x : BitVec 32} {s₀ : State} (hc₀ : VG.Proof.X25519.X86.Ctx 4096 x s₀) {o : Nat} (ho : VG.Proof.X25519.X86.Below o) (c : BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (if k = 0 then c else 0)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      VG.Proof.X25519.X86.Keep s₀ s' ∧ Frame [VG.Proof.X25519.X86.sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, VG.Proof.X25519.X86.wd s'.mem x (o + 4 * j) = if j = 0 then c else 0
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.setSmalls_ok hc₀ ho c n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      VG.Proof.X25519.X86.setSmall_step (k₁.ctx hc₀) ho (by omega_using [hn]) c k₁ f₁ w₁)

/-- `[o] = c`. -/
theorem setSmall_ok {x : BitVec 32} {s : State} (hc : VG.Proof.X25519.X86.Ctx 4096 x s) {o : Nat} (ho : VG.Proof.X25519.X86.Below o) (c : BitVec 32) :
    WP isa (.block (setSmall o c)) s fun s' => VG.Proof.X25519.X86.Keep s s' ∧ Frame [VG.Proof.X25519.X86.sub x o 32] s.mem s'.mem ∧
      VG.Proof.X25519.X86.fe s'.mem x o = c.toNat :=
  WP.mono (VG.Proof.X25519.X86.setSmalls_ok hc ho c 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ => ⟨k, f, by
    rw [VG.Proof.X25519.X86.fe]
    rw [VG.Proof.X25519.X86.num_congr (g := fun j => if j = 0 then c.toNat else 0) fun j hj => by
      show (VG.Proof.X25519.X86.wd _ x (o + 4 * j)).toNat = _; rw [w j hj]; split <;> rfl]
    simp only [VG.Proof.X25519.X86.num, Nat.reduceEqDiff, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add]⟩

theorem F_setSmall {x : BitVec 32} {s' : State} {o : Nat} (c : BitVec 32) (h : VG.Proof.X25519.X86.fe s'.mem x o = c.toNat) :
    VG.Proof.X25519.X86.F s'.mem x o = toFe c.toNat := by simp only [VG.Proof.X25519.X86.F, h]

/-- The slots, other than `o`, after a frame of `o`'s. -/
theorem F_frame1 {m m' : Mem} {x : BitVec 32} {o q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [VG.Proof.X25519.X86.sub x o 32] m m') (ho : VG.Proof.X25519.X86.isSlot 288 o = true) (hq : VG.Proof.X25519.X86.isSlot 288 q = true) (hne : q ≠ o) :
    VG.Proof.X25519.X86.F m' x q = VG.Proof.X25519.X86.F m x q := by
  have hob := VG.Proof.X25519.X86.slot_below ho; have hqb := VG.Proof.X25519.X86.slot_below hq; simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hob hqb
  simp only [VG.Proof.X25519.X86.F]
  exact congrArg toFe (VG.Proof.X25519.X86.fe_frame1 hf hx (by omega_using [hob]) (by omega_using [hqb]) (VG.Proof.X25519.X86.slot_ne ho hq hne))

theorem frame_slot {m m' : Mem} {x : BitVec 32} {o : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [VG.Proof.X25519.X86.sub x o 32] m m') (ho : VG.Proof.X25519.X86.isSlot 288 o = true) : Frame [VG.Proof.X25519.X86.sub x 288 640] m m' := by
  have hob := VG.Proof.X25519.X86.slot_below ho; have ho' := VG.Proof.X25519.X86.slot_ge ho; simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hob
  exact VG.Proof.X25519.X86.frameWiden hf hx ho' (by omega_using [hob]) (by omega_using [hob])

/-- The u-coordinate as `X1` holds it: decoded (RFC 7748 §5). -/
theorem fe_X1 {s₀ s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hw : ∀ j < 8, VG.Proof.X25519.X86.wd s.mem (arg s₀ 3) (X1 + 4 * j) = VG.Proof.X25519.X86.pv s₀ j) :
    VG.Proof.X25519.X86.fe s.mem (arg s₀ 3) X1 = decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
  have hpf := hp.point_fit
  have e1 : VG.Proof.X25519.X86.fe s.mem (arg s₀ 3) X1 = VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pv s₀ k).toNat) 8 :=
    VG.Proof.X25519.X86.num_congr fun j hj => by show (VG.Proof.X25519.X86.wd _ _ _).toNat = _; rw [hw j hj]
  have e2 : VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pv s₀ k).toNat) 8 = VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pw s₀ k).toNat) 8 % 2 ^ 255 := by
    rw [(VG.Proof.X25519.X86.fold_top (f := fun k => (VG.Proof.X25519.X86.pw s₀ k).toNat) fun _ _ => BitVec.isLt _).1, VG.Proof.X25519.X86.num_top]
    have n7 : VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pv s₀ k).toNat) 7 = VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pw s₀ k).toNat) 7 :=
      VG.Proof.X25519.X86.num_congr fun j hj => by
        show (VG.Proof.X25519.X86.pv s₀ j).toNat = (VG.Proof.X25519.X86.pw s₀ j).toNat
        rw [VG.Proof.X25519.X86.pv, ite_eq_right (show j ≠ 7 by omega_using [hj])]
    rw [n7]
    simp only [VG.Proof.X25519.X86.pv, ite_true, VG.Proof.X25519.X86.low31_toNat]
  have e3 : VG.Proof.X25519.X86.num (fun k => (VG.Proof.X25519.X86.pw s₀ k).toNat) 8 = leNum (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
    rw [leNum_bytesAt_words32]
    have r : ∀ k < 8, (VG.Proof.X25519.X86.pw s₀ k).toNat =
        (s₀.mem.readW ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32).toNat := fun k hk => by
      simp only [VG.Proof.X25519.X86.pw, VG.Proof.X25519.X86.wd]; rw [addr_eq (by omega_using [hpf, hk])]
    simp only [VG.Proof.X25519.X86.num, r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide), r 4 (by decide),
      r 5 (by decide), r 6 (by decide), r 7 (by decide), Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Nat.reduceMul, Nat.reducePow, Nat.one_mul, Nat.zero_add]
  rw [e1, e2, e3, decodeUCoordinate_eq (length_bytesAt _ _ _)]

/-- The scalar, decoded. -/
abbrev kOf (s₀ : State) : Nat := decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)

/-- The u-coordinate, decoded. -/
abbrev uOf (s₀ : State) : Fe := toFe (decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32))

theorem setup_eq : setup = save ++ (loadPoint ++ (loadScalar ++ (copy X3 X1 ++ (setSmall X2 1 ++
    (setSmall Z2 0 ++ (setSmall Z3 1 ++ ([.mov .eax (.imm 0), .store (sc SWAP) .eax] : List Instr))))))) := by
  simp only [setup, initLadder, List.append_assoc]

/-- The arguments read: the ladder's initial state, in `LInv 255` but for the counter. -/
theorem setup_ok {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) :
    WP isa (.block setup) s₀ fun s => VG.Proof.X25519.X86.Base (arg s₀ 3) (VG.Proof.X25519.X86.kOf s₀) s₀ s ∧ VG.Proof.X25519.X86.F s.mem (arg s₀ 3) X1 = VG.Proof.X25519.X86.uOf s₀ ∧
      VG.Proof.X25519.X86.F s.mem (arg s₀ 3) X2 = 1 ∧ VG.Proof.X25519.X86.F s.mem (arg s₀ 3) Z2 = 0 ∧ VG.Proof.X25519.X86.F s.mem (arg s₀ 3) X3 = VG.Proof.X25519.X86.uOf s₀ ∧
      VG.Proof.X25519.X86.F s.mem (arg s₀ 3) Z3 = 1 ∧ VG.Proof.X25519.X86.wd s.mem (arg s₀ 3) SWAP = 0 := by
  have hfit := hp.sc_fit
  rw [VG.Proof.X25519.X86.setup_eq]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.save_ok hp) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.loadPoint_ok hp h₁) fun s₂ ⟨h₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.loadScalar_ok hp h₂) fun s₃ ⟨h₃, f₃, b₃⟩ => ?_)
  have B₃ : VG.Proof.X25519.X86.Base (arg s₀ 3) (VG.Proof.X25519.X86.kOf s₀) s₀ s₃ :=
    ⟨⟨h₃.edi, hfit, by rw [h₃.wr]; exact hp.sc_in, by decide⟩, h₃.esp, h₃.rd, h₃.wr, h₃.frame, h₃.saved, b₃⟩
  have x1₃ : VG.Proof.X25519.X86.F s₃.mem (arg s₀ 3) X1 = VG.Proof.X25519.X86.uOf s₀ := by
    simp only [VG.Proof.X25519.X86.F, VG.Proof.X25519.X86.uOf]
    rw [← VG.Proof.X25519.X86.fe_X1 hp w₂]
    exact congrArg toFe (VG.Proof.X25519.X86.fe_frame1 f₃ hfit (by decide) (by decide) (.inr (by decide)))
  have sl : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.Below q := fun q hq => VG.Proof.X25519.X86.slot_below hq
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.copy_ok B₃.ctx (o := X3) (a := X1) (by decide) (by decide) (by decide))
    fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  have B₄ := B₃.ops k₄ (VG.Proof.X25519.X86.frame_slot hfit f₄ (by decide))
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.setSmall_ok B₄.ctx (o := X2) (by decide) 1) fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  have B₅ := B₄.ops k₅ (VG.Proof.X25519.X86.frame_slot hfit f₅ (by decide))
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.setSmall_ok B₅.ctx (o := Z2) (by decide) 0) fun s₆ ⟨k₆, f₆, e₆⟩ => ?_)
  have B₆ := B₅.ops k₆ (VG.Proof.X25519.X86.frame_slot hfit f₆ (by decide))
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.setSmall_ok B₆.ctx (o := Z3) (by decide) 1) fun s₇ ⟨k₇, f₇, e₇⟩ => ?_)
  have B₇ := B₆.ops k₇ (VG.Proof.X25519.X86.frame_slot hfit f₇ (by decide))
  refine Wp.wp_movi fun s₈ u₈ => ?_
  have c₈ := (VG.Proof.X25519.X86.updKeep u₈).ctx B₇.ctx
  refine Wp.wp_stm c₈.edi (c₈.inW (by decide) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₇.mem.writeW (addr (arg s₀ 3) SWAP) (0 : BitVec 32) := by rw [u₉.mem, u₈.gpr, u₈.mem]
  have f₉ : Frame [VG.Proof.X25519.X86.sub (arg s₀ 3) SWAP 4] s₇.mem s₉.mem := by
    rw [m₉]; exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  have F₉ : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s₉.mem (arg s₀ 3) q = VG.Proof.X25519.X86.F s₇.mem (arg s₀ 3) q := fun q hq => by
    have hq' := VG.Proof.X25519.X86.slot_ge hq; have hqb := VG.Proof.X25519.X86.slot_below hq; simp only [VG.Proof.X25519.X86.Below, VG.Impl.X25519.X86.T] at hqb
    simp only [VG.Proof.X25519.X86.F]
    exact congrArg toFe (VG.Proof.X25519.X86.fe_frame1 f₉ hfit (by decide) (by omega_using [hqb]) (.inr (by simp only [SWAP]; omega_using [hq'])))
  refine ⟨B₇.of_frame (by rw [u₉.gpr, u₈.other _ (by decide)]) (by rw [u₉.gpr, u₈.other _ (by decide)])
    (by rw [u₉.rd, u₈.rd]) (by rw [u₉.wr, u₈.wr]) f₉ (by decide) (by decide) (.inl (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, by rw [m₉, VG.Proof.X25519.X86.wd_write_self]⟩
  · rw [F₉ _ (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame1 hfit f₆ (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₅ (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame1 hfit f₄ (by decide) (by decide) (by decide), x1₃]
  · rw [F₉ _ (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame1 hfit f₆ (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_setSmall _ e₅]; rfl
  · rw [F₉ _ (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₇ (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_setSmall _ e₆]; rfl
  · rw [F₉ _ (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame1 hfit f₆ (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_frame1 hfit f₅ (by decide) (by decide) (by decide)]
    simp only [VG.Proof.X25519.X86.F] at x1₃ ⊢
    rw [e₄]; exact x1₃
  · rw [F₉ _ (by decide), VG.Proof.X25519.X86.F_setSmall _ e₇]; rfl

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Invert`. -/
section

/-!
# X25519 on x86 (32-bit): the inversion

The inversion is a sequence of blocks of operations and runs of squarings
(`sqn`, a loop counted by `esi`); each leaves the slots with the values of an
evaluation of it (`runI`), which for the inversion's steps is `invert` of `Z2`
in `T1`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- `n` squarings in place. -/
theorem sqn_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (hb : VG.Proof.X25519.X86.Base x k s₀ s) {o n : Nat}
    (ho : VG.Proof.X25519.X86.isSlot 288 o = true) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) :
    WP isa (Impl.X25519.X86.sqn o n) s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧
      ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s'.mem x q = Function.update (VG.Proof.X25519.X86.F s.mem x) o
        (Proof.X25519.sqn (VG.Proof.X25519.X86.F s.mem x o) n) q := by
  have hv : VG.Proof.X25519.X86.opValid 288 (.mul o o o) = true := by
    simp only [VG.Proof.X25519.X86.opValid, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opIns, ho, List.all_cons, List.all_nil, Bool.and_self]
  refine WP.seq (Wp.wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : VG.Proof.X25519.X86.Base x k s₀ s₁ := hb.of_frame (o := 288) (n := 640) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  refine WP.loop (M := isa) (fun c s' => 1 ≤ c ∧ c ≤ n ∧ VG.Proof.X25519.X86.Base x k s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 c ∧
      ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s'.mem x q = Function.update (VG.Proof.X25519.X86.F s.mem x) o
        (Proof.X25519.sqn (VG.Proof.X25519.X86.F s.mem x o) (n - c)) q) (fun c s' hc => ?_) n s₁
    ⟨hn, Nat.le_refl _, b₁, u₁.gpr, fun q hq => by
      rw [Nat.sub_self, u₁.mem]
      by_cases e : q = o
      · subst e; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne e]⟩
  obtain ⟨c1, cn, b, esi, hv'⟩ := hc
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.op_ok b.ctx (.mul o o o) hv) fun s₂ ⟨k₂, f₂, e₂⟩ => ?_)
  refine Wp.wp_subi fun s₃ u₃ _ z₃ => WP.block_nil ?_
  have b₃ : VG.Proof.X25519.X86.Base x k s₀ s₃ := (b.ops k₂ f₂).of_frame (o := 288) (n := 640) (u₃.other _ (by decide))
    (u₃.other _ (by decide)) u₃.rd u₃.wr (by rw [u₃.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 (c - 1) := by
    rw [u₃.gpr, k₂.esi, esi]; exact Wp.ofNat_pred c1
  have val₃ : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s₃.mem x q = Function.update (VG.Proof.X25519.X86.F s.mem x) o
      (Proof.X25519.sqn (VG.Proof.X25519.X86.F s.mem x o) (n - (c - 1))) q := fun q hq => by
    rw [u₃.mem, e₂ q hq]
    simp only [VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opVal]
    by_cases e : q = o
    · subst e
      rw [Function.update_self, Function.update_self, hv' q hq, Function.update_self,
        show n - (c - 1) = n - c + 1 by omega_using [c1, cn]]
      rfl
    · rw [Function.update_of_ne e, Function.update_of_ne e, hv' q hq, Function.update_of_ne e]
  have ev : isa.eval .ne s₃ = some (!decide (c - 1 = 0)) := by
    show s₃.zf.map (!·) = _
    rw [z₃, k₂.esi, esi, Wp.ofNat_pred c1, Wp.ofNat_beq_zero (by omega_using [cn, hn'])]; rfl
  by_cases e : c = 1
  · subst e
    refine .inl ⟨by rw [ev]; rfl, b₃, fun q hq => ?_⟩
    rw [val₃ q hq]; rfl
  · exact .inr ⟨by rw [ev]; simp only [show c - 1 ≠ 0 by omega_using [c1, e], decide_false]; rfl, c - 1,
      by omega_using [c1], by omega_using [c1, e], by omega_using [cn], b₃, esi₃, val₃⟩

/-- A step of the inversion: a block of operations, or a run of squarings. -/
inductive IStep
  | ops (l : List Op)
  | sqn (o n : Nat)

def IStep.prog : VG.Proof.X25519.X86.IStep → Prog isa
  | .ops l => .block (Impl.X25519.X86.ops l)
  | .sqn o n => Impl.X25519.X86.sqn o n

/-- Steps in sequence. -/
def progOf : List VG.Proof.X25519.X86.IStep → Prog isa
  | [] => .block []
  | [st] => st.prog
  | st :: l => .seq st.prog (VG.Proof.X25519.X86.progOf l)

def IStep.valid : VG.Proof.X25519.X86.IStep → Bool
  | .ops l => l.all (VG.Proof.X25519.X86.opValid 288)
  | .sqn o n => VG.Proof.X25519.X86.isSlot 288 o && 1 ≤ n && n < 2 ^ 32

/-- The values of the slots after a step. -/
def IStep.run (V : Nat → Fe) : VG.Proof.X25519.X86.IStep → Nat → Fe
  | .ops l => X86.run l V
  | .sqn o n => Function.update V o (Proof.X25519.sqn (V o) n)

def runI : List VG.Proof.X25519.X86.IStep → (Nat → Fe) → Nat → Fe
  | [], V => V
  | st :: l, V => VG.Proof.X25519.X86.runI l (st.run V)

theorem IStep.run_congr {V V' : Nat → Fe} (st : VG.Proof.X25519.X86.IStep) (hv : st.valid = true)
    (h : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → V q = V' q) : ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → st.run V q = st.run V' q := by
  cases st with
  | ops l =>
    simp only [IStep.valid, List.all_eq_true] at hv
    exact X86.run_congr l hv h
  | sqn o n =>
    simp only [IStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro q hq
    by_cases e : q = o
    · subst e; simp only [IStep.run, Function.update_self, h q hq]
    · simp only [IStep.run, Function.update_of_ne e, h q hq]

theorem runI_congr (l : List VG.Proof.X25519.X86.IStep) (hv : ∀ st ∈ l, st.valid = true) :
    ∀ {V V' : Nat → Fe}, (∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → V q = V' q) → ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.runI l V q = VG.Proof.X25519.X86.runI l V' q := by
  induction l with
  | nil => exact fun h q hq => h q hq
  | cons st l ih =>
    intro V V' h q hq
    exact ih (fun o ho => hv o (List.mem_cons_of_mem _ ho))
      (IStep.run_congr st (hv st List.mem_cons_self) h) q hq

theorem IStep.ok {x : BitVec 32} {k : Nat} {s₀ s : State} (hb : VG.Proof.X25519.X86.Base x k s₀ s) (st : VG.Proof.X25519.X86.IStep)
    (hv : st.valid = true) :
    WP isa st.prog s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧ ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s'.mem x q = st.run (VG.Proof.X25519.X86.F s.mem x) q := by
  cases st with
  | ops l =>
    simp only [IStep.valid, List.all_eq_true] at hv
    exact WP.mono (VG.Proof.X25519.X86.ops_ok l hb.ctx hv) fun s' ⟨k', f', e'⟩ => ⟨hb.ops k' f', e'⟩
  | sqn o n =>
    simp only [IStep.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact VG.Proof.X25519.X86.sqn_ok hb hv.1.1 hv.1.2 hv.2

theorem progOf_ok {x : BitVec 32} {k : Nat} {s₀ : State} :
    ∀ (l : List VG.Proof.X25519.X86.IStep) {s : State}, VG.Proof.X25519.X86.Base x k s₀ s → (∀ st ∈ l, st.valid = true) →
    WP isa (VG.Proof.X25519.X86.progOf l) s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧ ∀ q, VG.Proof.X25519.X86.isSlot 288 q = true → VG.Proof.X25519.X86.F s'.mem x q = VG.Proof.X25519.X86.runI l (VG.Proof.X25519.X86.F s.mem x) q
  | [], _, hb, _ => WP.block_nil ⟨hb, fun _ _ => rfl⟩
  | [st], _, hb, hv => WP.mono (IStep.ok hb st (hv st List.mem_cons_self)) fun _ ⟨b, e⟩ => ⟨b, e⟩
  | st :: st' :: l, s, hb, hv => by
    refine WP.seq (WP.mono (IStep.ok hb st (hv st List.mem_cons_self)) fun s₁ ⟨b₁, e₁⟩ => ?_)
    refine WP.mono (VG.Proof.X25519.X86.progOf_ok (st' :: l) b₁ fun o ho => hv o (List.mem_cons_of_mem _ ho))
      fun s₂ ⟨b₂, e₂⟩ => ⟨b₂, fun q hq => ?_⟩
    rw [e₂ q hq]
    exact VG.Proof.X25519.X86.runI_congr (st' :: l) (fun o ho => hv o (List.mem_cons_of_mem _ ho)) e₁ q hq

/-- The inversion's steps. -/
def invSteps : List VG.Proof.X25519.X86.IStep :=
  [.ops [.mul T0 Z2 Z2, .copy T1 T0], .sqn T1 2,
    .ops [.mul T1 Z2 T1, .mul T0 T0 T1, .mul T2 T0 T0, .mul T1 T1 T2, .copy T2 T1], .sqn T2 5,
    .ops [.mul T1 T2 T1, .copy T2 T1], .sqn T2 10,
    .ops [.mul T2 T2 T1, .copy T3 T2], .sqn T3 20,
    .ops [.mul T2 T3 T2], .sqn T2 10,
    .ops [.mul T1 T2 T1, .copy T2 T1], .sqn T2 50,
    .ops [.mul T2 T2 T1, .copy T3 T2], .sqn T3 100,
    .ops [.mul T2 T3 T2], .sqn T2 50,
    .ops [.mul T1 T2 T1], .sqn T1 5,
    .ops [.mul T1 T1 T0]]

theorem invert_eq : Impl.X25519.X86.invert = VG.Proof.X25519.X86.progOf VG.Proof.X25519.X86.invSteps := rfl

theorem invSteps_valid : ∀ st ∈ VG.Proof.X25519.X86.invSteps, st.valid = true := by decide

theorem runI_invert (V : Nat → Fe) : VG.Proof.X25519.X86.runI VG.Proof.X25519.X86.invSteps V T1 = VG.Proof.X25519.invert (V Z2) := by
  simp only [VG.Proof.X25519.X86.runI, VG.Proof.X25519.X86.invSteps, IStep.run, X86.run, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opVal, Function.update_apply, T0, T1, T2, T3, Z2]
  simp only [↓reduceIte, Nat.reduceEqDiff]
  rfl

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Finish`. -/
section

/-!
# X25519 on x86 (32-bit): the end of the ladder, and the result

The swap after the loop, and `finish`: `x2 · z2^(p-2)` (with `z2^(p-2)` in
`T1`), reduced fully, stored to `out`, and the saved registers restored.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The swap after the loop. -/
theorem lastSwap_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : VG.Proof.X25519.X86.LInv x k x1 s₀ 0 s) :
    WP isa (.block lastSwap) s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧
      VG.Proof.X25519.X86.F s'.mem x X2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).x2
        (ladderAfter k x1 0).x3).1 ∧
      VG.Proof.X25519.X86.F s'.mem x Z2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).z2
        (ladderAfter k x1 0).z3).1 := by
  have hfit := h.ctx.fit
  have hsw := ladderAfter_swap_le k x1 (n := 0) (by decide)
  simp only [lastSwap, List.cons_append, List.nil_append]
  refine Wp.wp_ldm h.ctx.edi (h.ctx.inRW (by decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_movi fun s₂ u₂ => Wp.wp_sub fun s₃ u₃ _ => ?_
  have k₃ : VG.Proof.X25519.X86.Keep s s₃ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans (VG.Proof.X25519.X86.updKeep u₃))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have b₃ : VG.Proof.X25519.X86.Base x k s₀ s₃ := h.toBase.ops k₃ (by rw [m₃]; exact Frame.refl _ _)
  have ecx₃ : s₃.gpr .ecx = VG.Proof.X25519.X86.mask (ladderAfter k x1 0).swap := by
    rw [u₃.gpr, u₂.gpr, u₂.other .edx (by decide), u₁.gpr]
    show 0 - VG.Proof.X25519.X86.wd s.mem x SWAP = _
    rw [h.swap]; rfl
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.cswap_ok b₃.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₃) fun s₄ ⟨k₄, ecx₄, f₄, x₄, _⟩ => ?_)
  have b₄ := b₃.ops k₄ (VG.Proof.X25519.X86.frame2_wide hfit f₄ (by decide) (by decide))
  refine WP.mono (VG.Proof.X25519.X86.cswap_ok b₄.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₄.trans ecx₃)) fun s₅ ⟨k₅, _, f₅, x₅, _⟩ => ⟨b₄.ops k₅ (VG.Proof.X25519.X86.frame2_wide hfit f₅ (by decide) (by decide)), ?_, ?_⟩
  · rw [VG.Proof.X25519.X86.F_frame2 hfit f₅ (by decide) (by decide) (by decide) (by decide) (by decide), VG.Proof.X25519.X86.F_ite _ x₄, m₃, h.vx2, h.vx3,
      VG.Proof.X25519.X86.cswap_fst]
  · rw [VG.Proof.X25519.X86.F_ite _ x₅, VG.Proof.X25519.X86.F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide),
      VG.Proof.X25519.X86.F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide), m₃, h.vz2, h.vz3, VG.Proof.X25519.X86.cswap_fst]

theorem runI_X2 (V : Nat → Fe) : VG.Proof.X25519.X86.runI VG.Proof.X25519.X86.invSteps V X2 = V X2 := by
  simp only [VG.Proof.X25519.X86.runI, VG.Proof.X25519.X86.invSteps, IStep.run, X86.run, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opVal, Function.update_apply, T0, T1, T2, T3, X2]
  simp only [↓reduceIte, Nat.reduceEqDiff]

/-- The inversion. -/
theorem invert_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (h : VG.Proof.X25519.X86.Base x k s₀ s) :
    WP isa Impl.X25519.X86.invert s fun s' => VG.Proof.X25519.X86.Base x k s₀ s' ∧
      VG.Proof.X25519.X86.F s'.mem x T1 = VG.Proof.X25519.invert (VG.Proof.X25519.X86.F s.mem x Z2) ∧ VG.Proof.X25519.X86.F s'.mem x X2 = VG.Proof.X25519.X86.F s.mem x X2 := by
  rw [VG.Proof.X25519.X86.invert_eq]
  exact WP.mono (VG.Proof.X25519.X86.progOf_ok VG.Proof.X25519.X86.invSteps h VG.Proof.X25519.X86.invSteps_valid) fun s' ⟨b, e⟩ =>
    ⟨b, by rw [e _ (by decide), VG.Proof.X25519.X86.runI_invert], by rw [e _ (by decide), VG.Proof.X25519.X86.runI_X2]⟩

/-! ## The result -/

theorem num_shift (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.X86.num f (n + 1) = f 0 + 2 ^ 32 * VG.Proof.X25519.X86.num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [VG.Proof.X25519.X86.num]
  | succ n ih =>
    rw [VG.Proof.X25519.X86.num_succ, ih, VG.Proof.X25519.X86.num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

/-- The digits of a number of words. -/
theorem num_digit : ∀ (j : Nat) {f : Nat → Nat} {n : Nat}, (∀ k < n, f k < 2 ^ 32) → j < n →
    VG.Proof.X25519.X86.num f n / (2 ^ 32) ^ j % 2 ^ 32 = f j
  | 0, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [VG.Proof.X25519.X86.num_shift, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 hj)]
  | j + 1, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [VG.Proof.X25519.X86.num_shift, Nat.pow_succ (2 ^ 32) j, Nat.mul_comm ((2 ^ 32) ^ j) (2 ^ 32), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (h 0 (by omega_using [])), Nat.zero_add]
    exact VG.Proof.X25519.X86.num_digit j (fun k hk => h (k + 1) (by omega_using [hk])) (by omega_using [hj])

/-- The words stored to `out` so far: those of `X2`. -/
structure OInv (s₀ sF : State) (n : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esi : s.gpr .esi = arg s₀ 0
  esp : s.gpr .esp = sF.gpr .esp
  rd : s.rd = sF.rd
  wr : s.wr = sF.wr
  frame : Frame [VG.Proof.X25519.X86.outR s₀] sF.mem s.mem
  words : ∀ j < n, VG.Proof.X25519.X86.wd s.mem (arg s₀ 0) (4 * j) = VG.Proof.X25519.X86.wd sF.mem (arg s₀ 3) (X2 + 4 * j)

theorem out_contains {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) {j : Nat} (hj : j < 8) :
    (VG.Proof.X25519.X86.outR s₀).Contains (addr (arg s₀ 0) (4 * j)) 4 := by
  have := VG.Proof.X25519.X86.sub_contains (x := arg s₀ 0) (a := 0) (k := 32) (d := 4 * j) (n := 4)
    (by have := hp.out_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hj]) (by decide)
  rwa [VG.Proof.X25519.X86.sub, VG.Proof.X25519.X86.addr_zero] at this

theorem outWord_ok {s₀ sF s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hsF : sF.wr = s₀.wr) {n : Nat} (hn : n < 8)
    (h : VG.Proof.X25519.X86.OInv s₀ sF n s) :
    WP isa (.block [.mov .eax (.mem (sc (X2 + 4 * n))), .store (at_ .esi (4 * n)) .eax]) s (VG.Proof.X25519.X86.OInv s₀ sF (n + 1)) := by
  have hfit := hp.sc_fit
  refine Wp.wp_ldm h.edi ⟨_, by rw [h.wr, hsF]; exact List.mem_append_right _ hp.sc_in,
    VG.Proof.X25519.X86.scR_contains hfit (by simp only [X2]; omega_using [hn]) (by decide)⟩ fun s₁ u₁ => ?_
  refine Wp.wp_stm (by rw [u₁.other _ (by decide), h.esi]) ⟨_, by rw [u₁.wr, h.wr, hsF]; exact hp.out_in,
    VG.Proof.X25519.X86.out_contains hp hn⟩ fun s₂ u₂ => WP.block_nil ?_
  have hsame : VG.Proof.X25519.X86.wd s.mem (arg s₀ 3) (X2 + 4 * n) = VG.Proof.X25519.X86.wd sF.mem (arg s₀ 3) (X2 + 4 * n) :=
    VG.Proof.X25519.X86.wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
      rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hfit (Nat.zero_le _) (by simp only [X2]; omega_using [hn])
        (by simp only [X2]; omega_using [hn])
  refine ⟨by rw [u₂.gpr, u₁.other _ (by decide), h.edi], by rw [u₂.gpr, u₁.other _ (by decide), h.esi],
    by rw [u₂.gpr, u₁.other _ (by decide), h.esp], by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], ?_,
    fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.X25519.X86.out_contains hp hn)
  · rw [u₂.mem, u₁.mem, u₁.gpr]
    have hof := hp.out_fit
    by_cases e : j = n
    · subst e; rw [VG.Proof.X25519.X86.wd_write_self]; exact hsame
    · rw [VG.Proof.X25519.X86.wd_write_ne _ _ (by omega_using [hof, hj, hn]) (by omega_using [hof, hn]) (by omega_using [hj, e])]
      exact h.words j (by omega_using [hj, e])

theorem outWords_ok {s₀ sF : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hsF : sF.wr = s₀.wr) : ∀ n ≤ 8, ∀ s, VG.Proof.X25519.X86.OInv s₀ sF 0 s →
    WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (sc (X2 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s (VG.Proof.X25519.X86.OInv s₀ sF n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (VG.Proof.X25519.X86.outWords_ok hp hsF n (by omega_using [hn]) s h) fun s₁ h₁ =>
      VG.Proof.X25519.X86.outWord_ok hp hsF (by omega_using [hn]) h₁)

theorem restore_eq : restore =
    .mov .eax (.reg .edi) :: (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) := rfl

/-- The saved registers restored. -/
theorem restore_ok {x : BitVec 32} {s s₀ : State} (hc : VG.Proof.X25519.X86.Ctx 4096 x s) (hs : Spill.Saved s.mem (addr x) s₀.gpr VG.Proof.X25519.X86.savedSlots) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .esp = s.gpr .esp ∧ ∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r := by
  rw [VG.Proof.X25519.X86.restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  refine Spill.restore_ok _ (by decide)
    (fun p h => by
      rw [ea, u₁.rd, u₁.wr]; exact hc.inRW (by have := VG.Proof.X25519.X86.savedSlots_bound p (by revert p h; decide); omega_using [this])
        (by decide))
    (by rw [ea, u₁.mem]; exact hs.sub (by decide)) fun s' r' => WP.block_nil ⟨by rw [r'.mem, u₁.mem],
      by rw [r'.other _ (by decide), u₁.other _ (by decide)],
      fun r hr hsp => r'.regs r (by revert hsp; revert hr; revert r; decide)⟩

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Main`. -/
section

/-!
# X25519 on x86 (32-bit): the whole function

The setup, the ladder, the last swap, the inversion and the result, composed:
`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_eq`), and restores the
callee-saved registers.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem x25519_code : Impl.X25519.X86.x25519 =
    .seq (.block setup) (.seq (.seq (.block [.mov .esi (.imm 255)]) (.loop (.block VG.Impl.X25519.X86.step) .ne))
      (.seq (.block lastSwap) (.seq Impl.X25519.X86.invert (.block finish)))) := rfl

theorem finish_eq : finish = VG.Impl.X25519.X86.ops ([.mul X2 X2 T1] : List Op) ++ (freeze X2 ++ (.mov .esi (.mem (at_ .esp 4)) ::
    (((List.range 8).flatMap fun k => ([.mov .eax (.mem (sc (X2 + 4 * k))), .store (at_ .esi (4 * k)) .eax] :
      List Instr)) ++ restore))) := by
  simp only [finish, VG.Impl.X25519.X86.ops, List.flatMap_cons, List.flatMap_nil, Op.code, List.append_nil, List.append_assoc,
    List.cons_append]

/-- The result `r`, as the words of its value at `[x + X2]`, to `out`, and the registers restored. -/
theorem finish_ok {s₀ s : State} (hp : VG.Proof.X25519.X86.Pre s₀) (hb : VG.Proof.X25519.X86.Base (arg s₀ 3) (VG.Proof.X25519.X86.kOf s₀) s₀ s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧
      Spec.X25519.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 32 =
        encodeUCoordinate (VG.Proof.X25519.X86.F s.mem (arg s₀ 3) X2 * VG.Proof.X25519.X86.F s.mem (arg s₀ 3) T1) := by
  have hfit := hp.sc_fit
  rw [VG.Proof.X25519.X86.finish_eq]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.ops_ok (lo := 288) [.mul X2 X2 T1] hb.ctx (by decide)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
  have b₁ := hb.ops k₁ f₁
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.freeze_ok b₁.ctx (lo := 288) (o := X2) (by decide)) fun s₂ ⟨k₂, f₂, e₂⟩ => ?_)
  have b₂ := b₁.ops k₂ (VG.Proof.X25519.X86.frame_wide hfit (lo := 288) (by decide) (by decide) f₂)
  -- The value: fully reduced.
  have hv : VG.Proof.X25519.X86.fe s₂.mem (arg s₀ 3) X2 = (VG.Proof.X25519.X86.F s.mem (arg s₀ 3) X2 * VG.Proof.X25519.X86.F s.mem (arg s₀ 3) T1).val := by
    rw [e₂, ← toFe_val]
    have := e₁ X2 (by decide)
    simp only [X86.run, VG.Proof.X25519.X86.opOut, VG.Proof.X25519.X86.opVal, Function.update_self] at this
    exact congrArg Fin.val this
  refine Wp.wp_ldm (B := s₂.gpr .esp) (o := 4) rfl (by rw [b₂.esp, b₂.rd, b₂.wr]; exact hp.argIn (i := 0) (by decide))
    fun s₃ u₃ => ?_
  have o₃ : VG.Proof.X25519.X86.OInv s₀ s₃ 0 s₃ := ⟨by rw [u₃.other _ (by decide)]; exact b₂.ctx.edi,
    by rw [u₃.gpr, b₂.esp]; exact hp.arg_same b₂.frame (i := 0) (by decide), rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, b₂.wr]
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.outWords_ok hp w₃ 8 (Nat.le_refl _) s₃ o₃) fun s₄ o₄ => ?_)
  have c₄ : VG.Proof.X25519.X86.Ctx 4096 (arg s₀ 3) s₄ := ⟨o₄.edi, hfit, by rw [o₄.wr, w₃]; exact hp.sc_in, by decide⟩
  -- The saved words, unchanged by the stores to `out`.
  have sv : Spill.Saved s₄.mem (addr (arg s₀ 3)) s₀.gpr VG.Proof.X25519.X86.savedSlots := b₂.saved.of_readW fun p hq => by
    have := VG.Proof.X25519.X86.savedSlots_bound p hq
    show VG.Proof.X25519.X86.wd s₄.mem (arg s₀ 3) p.2 = VG.Proof.X25519.X86.wd s₂.mem (arg s₀ 3) p.2
    rw [VG.Proof.X25519.X86.wd_frame o₄.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
      rw [VG.Proof.X25519.X86.scR_eq]; exact VG.Proof.X25519.X86.sub_sub hfit (Nat.zero_le _) (by omega_using [this]) (by omega_using [this]),
      u₃.mem]
  refine WP.mono (VG.Proof.X25519.X86.restore_ok c₄ sv) fun s₅ ⟨m₅, esp₅, g₅⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_⟩
    · by_cases h : r = .esp
      · subst h; rw [esp₅, o₄.esp, u₃.other _ (by decide), b₂.esp]
      · exact g₅ r hr h
    · rw [m₅]
      have r₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₃.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
        o₄.frame.readW (Region.contains_self _ _) (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_out)
          (by decide)
      rw [r₄, u₃.mem]
      exact b₂.frame.readW (Region.contains_self _ _) (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc)
        (by decide)
  · rw [m₅, encodeUCoordinate_eq]
    refine bytesAt_leBytes_words32 _ _ _ fun j hj => ?_
    have hof := hp.out_fit
    rw [← addr_eq (by omega_using [hof, hj]), ← VG.Proof.X25519.X86.wd, o₄.words j hj, u₃.mem, ← hv, Nat.pow_mul]
    exact (VG.Proof.X25519.X86.num_digit j (f := fun k => VG.Proof.X25519.X86.wv s₂.mem (arg s₀ 3) (X2 + 4 * k)) (fun _ _ => VG.Proof.X25519.X86.wv_lt _ _ _) hj).symm

theorem ladderAfter_255_eq (k : Nat) (x1 : Fe) :
    ladderAfter k x1 255 = { x2 := 1, z2 := 0, x3 := x1, z3 := 1, swap := 0 } := rfl

/-- The function's correctness. -/
theorem x25519_correct {s₀ : State} (hp : VG.Proof.X25519.X86.Pre s₀) :
    WP isa Impl.X25519.X86.x25519 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X25519.x25519X86.post s₀ s' := by
  rw [VG.Proof.X25519.X86.x25519_code]
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.setup_ok hp) fun s₁ ⟨b₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  refine WP.seq (WP.seq (Wp.wp_movi fun s₂ u₂ => WP.block_nil ?_))
  have b₂ : VG.Proof.X25519.X86.Base (arg s₀ 3) (VG.Proof.X25519.X86.kOf s₀) s₀ s₂ := b₁.of_frame (o := 288) (n := 640) (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.rd u₂.wr (by rw [u₂.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  have L₂ : VG.Proof.X25519.X86.LInv (arg s₀ 3) (VG.Proof.X25519.X86.kOf s₀) (VG.Proof.X25519.X86.uOf s₀) s₀ 255 s₂ :=
    ⟨b₂, u₂.gpr, by rw [u₂.mem]; exact x1₁, by rw [u₂.mem, VG.Proof.X25519.X86.ladderAfter_255_eq]; exact x2₁,
      by rw [u₂.mem, VG.Proof.X25519.X86.ladderAfter_255_eq]; exact z2₁, by rw [u₂.mem, VG.Proof.X25519.X86.ladderAfter_255_eq]; exact x3₁,
      by rw [u₂.mem, VG.Proof.X25519.X86.ladderAfter_255_eq]; exact z3₁, by rw [u₂.mem, VG.Proof.X25519.X86.ladderAfter_255_eq]; exact sw₁⟩
  refine WP.mono (VG.Proof.X25519.X86.ladderLoop_ok L₂) fun s₃ L₃ => ?_
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.lastSwap_ok L₃) fun s₄ ⟨b₄, x2₄, z2₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.X86.invert_ok b₄) fun s₅ ⟨b₅, t1₅, x2₅⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.X86.finish_ok hp b₅) fun s₆ ⟨abi, out⟩ => ⟨abi, ?_⟩
  show Spec.X25519.bytesAt s₆.mem ((arg s₀ 0).setWidth 64) 32 = _
  rw [out, t1₅, x2₅, x2₄, z2₄, x25519_eq]

end VG.Proof.X25519.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86.Verified`. -/
section

/-!
# X25519 on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is a pointer plus a constant or the counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 4096], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.X25519.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.X25519.X86.τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.X25519.X86.τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [VG.Proof.X25519.X86.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X25519.x25519X86.pre s₁) (h₂ : Proof.X25519.x25519X86.pre s₂)
    (hpub : Proof.X25519.x25519X86.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.X25519.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.X25519.X86.wf₀ hp₁, VG.Proof.X25519.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.X25519.X86.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.X25519.X86.outR, a0, a3]
  · simp only [VG.Proof.X25519.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86.pre Proof.X25519.x25519X86.pub
    Impl.X25519.X86.x25519 :=
  VG.Taint.constantTime (A := taint) VG.Proof.X25519.X86.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.X25519.X86.agree₀ h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.X25519.X86.satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519X86.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86.x25519 s t s' ∧ abiPreserved s s' ∧ Proof.X25519.x25519X86.post s s' :=
  VG.Proof.X25519.X86.x25519_correct (Pre.of s hs)

theorem x25519_verified :
    Verified X86.target Impl.X25519.X86.x25519 (Spec.X25519.x25519Contract X86.abi) :=
  Verified.of_correct VG.Proof.X25519.X86.x25519_ok VG.Proof.X25519.X86.x25519_ct (by
    have a0 : arg VG.Proof.X25519.X86.satState 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.X25519.X86.satState 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.X25519.X86.satState 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.X25519.X86.satState 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.X25519.X86.satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.x25519X86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, e, esp] using Proof.X25519.X86.satState)

end VG.Proof.X25519.X86

end

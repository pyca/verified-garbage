module

public import VerifiedGarbage.Proof.Dsa.Arm.ContextCall
public import VerifiedGarbage.Impl.Dsa.Arm.Core
import VerifiedGarbage.Proof.Dsa.Arm.Bytes
public import VerifiedGarbage.Proof.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Exponent
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Dsa.Encoding

/-! ### `Dsa.Arm.CoreBase`, which only this module used -/

section

/-!
# DSA on 32-bit ARM: operands

An operand is the caller's bytes at a pointer saved in the header of the
working space, or computed bytes in the working space past the arithmetic
(`pointerValue`). `Ready` says an operand's bytes can be read and lie apart
from the arithmetic's 4960 bytes, which every operation may change (with the
header's first 64 bytes, where the exponentiation keeps `m'`, its mask and the
registers it saves: `arithRanges`); the saved pointers, at offsets 64
to 120, are kept (`pointerValue_keep`). `pointer_ok`, `load_ok`,
`store_ok` and `setup_ok` are the steps of every operation of
`Impl/Dsa/Arm/Core.lean`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg dpVal)

theorem field_bounds (f : Field) : 64 ≤ Impl.Dsa.Arm.Layout.field f ∧ Impl.Dsa.Arm.Layout.field f + 4 ≤ 120 := by
  cases f <;> decide

/-- The saved pointers and lengths lie below the mask. -/
theorem field_saved {f : Field} (hf : f ≠ .mask) : Impl.Dsa.Arm.Layout.field f + 4 ≤ 116 := by
  cases f <;> first | decide | exact absurd rfl hf

/-- The registers an operation may write. -/
def coreClob : List Reg := .r11 :: .lr :: dclob

/-- The memory the arithmetic may change: the header's first 64 bytes,
and the slots of a context of up to 48 words. -/
def arithRanges : List (Nat × Nat) := [(0, 64), (256, 4704)]

theorem contextBytes_le {n : Nat} (hn : n ≤ 48) : contextBytes n ≤ 4960 := by
  simp only [contextBytes, slot, stride]; omega_using [hn]

/-- Ranges within the arithmetic's. -/
theorem Outs.arith {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960)) : Outs base arithRanges m m' :=
  fun x hx => O x fun r hr => by
    have h1 := hx (0, 64) (by simp [arithRanges])
    have h2 := hx (256, 4704) (by simp [arithRanges])
    have := h r hr
    simp only at h1 h2
    omega_using [h1, h2, this]

theorem Outs.of_slot {base : Addr} {n i : Nat} {m m' : Mem} (O : Outside base (slot n i) (8 * n) m m')
    (hi : i < 12) (hn : n ≤ 48) : Outs base arithRanges m m' :=
  Outs.arith (Outs.of_outside O (List.mem_singleton_self _)) fun r hr => by
    have := slot_bound (n := n) hi
    have := contextBytes_le hn
    have := slot_header n i
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [stride] at *
    omega_arith

theorem setupRanges_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil, or_false] at *
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega_arith

theorem streamRanges_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ streamRanges n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [streamRanges, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil, or_false] at *
  rintro r (rfl | rfl | rfl | rfl) <;> simp only <;> omega_using [hn]

theorem scratch_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ Impl.Dsa.Arm.Pow.scratch n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [Impl.Dsa.Arm.Pow.scratch, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil,
    or_false] at *
  rintro r (rfl | rfl) <;> simp only <;> omega_arith

/-! ## Operands -/

/-- The address of an operand. -/
def pointerValue (base : Addr) (s : State) : Pointer → BitVec 32
  | .input f => s.mem.readW (off base (Impl.Dsa.Arm.Layout.field f)) 32
  | .local o => s.gpr .r12 + BitVec.ofNat 32 o
  | .signatureS => s.mem.readW (off base (Impl.Dsa.Arm.Layout.field .signature)) 32 +
      s.mem.readW (off base (Impl.Dsa.Arm.Layout.field .qLen)) 32

/-- A computed operand's offset is a `movw` immediate. -/
def PtrOk : Pointer → Prop
  | .local o => o < 2 ^ 16
  | .input f => f ≠ .mask
  | .signatureS => True

/-- An operand of `len` bytes that can be read and lies apart from the arithmetic. -/
structure Ready (s : State) (base : Addr) (p : Pointer) (len : Nat) : Prop where
  ok : PtrOk p
  fits : (pointerValue base s p).toNat + len ≤ 2 ^ 32
  reads : ∀ e k, e + k ≤ len → InRegions (s.rd ++ s.wr) (State.addr (pointerValue base s p) + BitVec.ofNat 64 e) k
  apart : Region.Disjoint ⟨State.addr (pointerValue base s p), len⟩ ⟨base, 4960⟩

/-- An operand's bytes. -/
abbrev operand (base : Addr) (s : State) (p : Pointer) (len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s p)) len)

theorem field_keep {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) {f : Field} (hf : f ≠ .mask) :
    m'.readW (off base (Impl.Dsa.Arm.Layout.field f)) 32 = m.readW (off base (Impl.Dsa.Arm.Layout.field f)) 32 :=
  (Mem.readW_congr fun i hi => (O _ fun r hr => by
    have := field_bounds f
    have := field_saved hf
    have := hO r hr
    rw [ofs_off base (by omega_arith)]
    omega_arith).symm).symm

theorem pointerValue_keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} (h12 : t.gpr .r12 = s.gpr .r12)
    (O : Outs base rs s.mem t.mem) (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) {p : Pointer} (hp : PtrOk p) :
    pointerValue base t p = pointerValue base s p := by
  cases p with
  | input f => exact field_keep O hO hp
  | «local» o => simp only [pointerValue, h12]
  | signatureS => simp only [pointerValue, field_keep O hO (f := .signature) (by decide),
      field_keep O hO (f := .qLen) (by decide)]

/-- The arithmetic and the computed operands keep the saved pointers. -/
theorem arith_hdr : ∀ r ∈ arithRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide

theorem Ready.keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} {p : Pointer} {len : Nat}
    (R : Ready s base p len) (h12 : t.gpr .r12 = s.gpr .r12) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (O : Outs base rs s.mem t.mem) (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) : Ready t base p len := by
  have P := pointerValue_keep h12 O hO R.ok
  exact ⟨R.ok, by rw [P]; exact R.fits, by rw [P, hrd, hwr]; exact R.reads, by rw [P]; exact R.apart⟩

theorem Ready.keep_rest {base : Addr} {rs : List (Nat × Nat)} {ws : List Reg} {s t : State} {p : Pointer}
    {len : Nat} (R : Ready s base p len) (K : Rest ws s t) (h12 : .r12 ∉ ws := by decide)
    (O : Outs base rs s.mem t.mem) (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) : Ready t base p len :=
  R.keep (K.gpr _ h12) K.rd K.wr O hO

/-- An operand's bytes are kept by stores apart from them. -/
theorem Ready.bytes {base : Addr} {rs : List (Nat × Nat)} {s t : State} {p : Pointer} {len : Nat}
    (R : Ready s base p len) (O : Outs base rs s.mem t.mem) (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 4960) :
    Spec.Rsa.bytesAt t.mem (State.addr (pointerValue base s p)) len =
      Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s p)) len :=
  outs_bytes O (by have := R.fits; omega_using [this]) (fun r hr => by have := hO r hr; omega_using [this])
    fun r hr => R.apart.sub_right (Offset.sub_base base (hO r hr))

/-- An operand's bytes after the arithmetic. -/
theorem Ready.arith {base : Addr} {s t : State} {p : Pointer} {len : Nat} (R : Ready s base p len)
    (h12 : t.gpr .r12 = s.gpr .r12) (O : Outs base arithRanges s.mem t.mem) :
    operand base t p len = operand base s p len := by
  rw [operand, operand, pointerValue_keep h12 O arith_hdr R.ok, R.bytes O (by decide)]

/-! ## Steps of every operation -/

/-- `r11` = the operand's address. -/
theorem pointer_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size) {p : Pointer}
    (hp : PtrOk p) :
    WP isa (.block (Core.pointer p)) s fun t =>
      t.gpr .r11 = pointerValue base s p ∧ Rest [.r4, .r11] s t ∧ t.mem = s.mem := by
  cases p with
  | input f =>
    have := field_bounds f
    exact wp_ldr (by omega_using [this]) (hs.ea12 (by omega_using [hz, this])) (hs.read (by omega_using [hz, this])) fun t u =>
      WP.block_nil ⟨u.gpr, u.rest (by decide), u.mem⟩
  | «local» o =>
    exact wp_ptr (is := []) (by decide) hp fun t u => WP.block_nil ⟨u.gpr, u.rest (by decide), u.mem⟩
  | signatureS =>
    have := field_bounds .signature
    have := field_bounds .qLen
    refine wp_ldr (by omega_arith) (hs.ea12 (by omega_arith)) (hs.read (by omega_arith)) fun t₁ u₁ => ?_
    have w₁ := hs.of_upd u₁ (by decide)
    refine wp_ldr (by omega_using [this]) (w₁.ea12 (by omega_using [hz, this])) (w₁.read (by omega_using [hz, this])) fun t₂ u₂ => ?_
    refine wp_dp (op2_reg _ _) fun t u₃ => WP.block_nil ⟨?_, ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
      (u₃.rest (by decide)), by rw [u₃.mem, u₂.mem, u₁.mem]⟩
    rw [u₃.gpr, dpVal, u₂.other .r11 (by decide), u₁.gpr, u₂.gpr, u₁.mem]
    rfl

/-- `[dst] = ` an operand's bytes. -/
theorem load_ok {s : State} {base : Addr} {size n len dst : Nat} {p : Pointer} (hs : Ws s base size)
    (hz : 120 ≤ size) (R : Ready s base p len) (ho : dst + 8 * n ≤ size) (h16 : dst + len < 2 ^ 16)
    (hpad : 8 * n ≤ len + 4096) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hd : dst + 8 * n ≤ 4960) :
    WP isa (Core.load n len dst p) s fun t => Ws t base size ∧
      val32 t.mem base dst (2 * n) = operand base s p len ∧
      Rest [.r4, .r8, .r9, .r10, .r11] s t ∧ Outside base dst (8 * n) s.mem t.mem := by
  unfold Core.load
  refine WP.seq (WP.mono (pointer_ok hs hz R.ok) fun u ⟨Pu, Ru, Mu⟩ => ?_)
  have wu := hs.of_rest Ru (by decide)
  refine WP.mono (loadComponent_ok wu ho h16 hpad (by rw [Pu]; have := R.fits; omega_using [this]) h4 hlen hw4
    (fun d hd' => by rw [Pu, Ru.rd, Ru.wr]; exact R.reads d 4 hd')
    (by rw [Pu]; exact R.apart.sub_right (Offset.sub_base base hd))) fun t ⟨wt, Vt, Rt, Ot⟩ =>
    ⟨wt, by rw [Vt, Pu, Mu], (Ru.mono (by decide)).trans (Rt.mono (by decide)), by rw [← Mu]; exact Ot⟩

/-- The bytes at `[output]` = the result slot of a context of `n` words. -/
theorem store_ok {s : State} {base : Addr} {size n len output : Nat} (hs : Ws s base size)
    (hn : (len + 7) / 8 = n) (h4 : 4 ≤ len) (hw4 : len % 4 = 0)
    (hb : slot n 9 + 8 * n ≤ size) (h16 : slot n 9 + len < 2 ^ 16)
    (ho : output + len ≤ size) (h16o : output < 2 ^ 16) (hsep : slot n 9 + 8 * n ≤ output) :
    WP isa (Core.store len output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len (val32 s.mem base (slot n 9) (len / 4)) ∧
      Rest [.r3, .r4, .r8, .r9, .r10, .r11] s t ∧ Outside base output len s.mem t.mem := by
  have nw := hs.nowrap
  unfold Core.store
  rw [hn]
  simp only [Core.pointer, List.append_assoc]
  refine WP.seq (wp_ptr (d := .r11) (by decide) h16o fun u₁ v₁ => ?_)
  simp only [allOnes, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u₂ v₂ => wp_dp (op2_imm (by decide)) fun u₃ v₃ =>
    wp_mov (op2_reg _ _) fun u v₄ => WP.block_nil ?_
  have Ru : Rest [.r3, .r4, .r11] s u := (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    (v₃.rest (by decide))).trans (v₄.rest (by decide))
  have wu := hs.of_rest Ru (by decide)
  have r11 : u.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 output := by
    rw [v₄.other .r11 (by decide), v₃.other .r11 (by decide), v₂.other .r11 (by decide), v₁.gpr]
  have pa : State.addr (u.gpr .r11) = off base output := by
    rw [r11]
    have := wu.ea (r := .r12) (K := 0) (d := output) (BitVec.add_zero _).symm (by omega_using [h4, ho])
    rwa [Nat.zero_add, Ru.gpr .r12 (by decide)] at this
  have pn : (u.gpr .r11).toNat = base.toNat + output := by
    rw [r11, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (by omega_using [h16o] : output < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [h4, ho, nw])]
  have r3 : u.gpr .r3 = if true then BitVec.allOnes 32 else 0 := by
    rw [v₄.gpr, v₃.gpr, dpVal, v₂.gpr]; decide
  have mu : u.mem = s.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have r9 : resS n + len ≤ output := by simp only [resS]; omega_using [hn, hsep]
  have hd : Region.Disjoint ⟨off base (resS n), len⟩ ⟨off base output, len⟩ :=
    Offset.disjoint base (.inl r9) (by omega_using [h16o, r9]) (by omega_using [h16, h16o])
  refine WP.mono (storeComponent_ok (input := resS n) (len := len) wu true r3 (by simp only [resS]; omega_using [hn, hb]) (by simp only [resS]; omega_using [h16]) h4 hw4
    (by rw [pn]; omega_using [ho, nw])
    (fun e k hek => by rw [pa]; exact Offset.add_add base output e ▸ wu.write (by omega_using [ho, hek]))
    (by rw [pa]; exact hd))
    fun t ⟨_, Vt, Rt, Ot⟩ => ⟨?_, (Ru.mono (by decide)).trans (Rt.mono (by decide)), ?_⟩
  · simpa only [pa, mu, ite_true, resS] using Vt
  · rw [pa, mu] at Ot
    exact outside_rebase Ot (by omega_using [h16, h16o])

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA on 32-bit ARM: the arithmetic operations

Each operation sets up a context for a modulus given by its saved pointer
(`setup_ok`), loads its operands, computes, and stores its result's `len`
big-endian bytes at an offset `output` of the working space past the
arithmetic (`power_ok`, `productMod_ok`, `sum_ok`, `reduce_ok`); an
exponentiation loads the modulus and calls `vg_dsa_pow_{n}_{e}`, which sets
up the context itself (`Pow.call_ok`). It changes only the arithmetic and its
output (`Stage`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- What an operation keeps: the registers but `coreClob`, and the memory but
the arithmetic's and the output's. -/
structure Stage (base : Addr) (s t : State) (output len : Nat) : Prop where
  rest : Rest coreClob s t
  mem : Outs base (arithRanges ++ [(output, len)]) s.mem t.mem

theorem Outs.arith_out {base : Addr} {m m' : Mem} (O : Outs base arithRanges m m') (output len : Nat) :
    Outs base (arithRanges ++ [(output, len)]) m m' :=
  O.mono fun _ hr => List.mem_append_left _ hr

theorem Outs.out {base : Addr} {m m' : Mem} {output len : Nat} (O : Outside base output len m m') :
    Outs base (arithRanges ++ [(output, len)]) m m' :=
  Outs.of_outside O (by simp)

/-- A modulus of `len` bytes: its context's size. -/
structure Width (len n : Nat) : Prop where
  n_eq : n = (len + 7) / 8
  four : 4 ≤ len
  max : len ≤ 384
  word : len % 4 = 0

theorem Width.bounds {len n : Nat} (w : Width len n) : 0 < n ∧ n ≤ 48 ∧ len ≤ 8 * n ∧ 8 * n ≤ len + 7 := by
  have := w.n_eq; have := w.four; have := w.max; omega_arith

theorem slot_lt {n i : Nat} (hn : n ≤ 48) (hi : i < 12) : 256 ≤ slot n i ∧ slot n i + 8 * n + 8 ≤ 4960 := by
  have := slot_bound (n := n) hi
  have := contextBytes_le hn
  have := slot_header n i
  simp only [stride] at *
  omega_arith

/-- The modulus's value below `2^(8 len)`. -/
theorem operand_lt (base : Addr) (s : State) (p : Pointer) (len : Nat) :
    operand base s p len < 256 ^ len := by
  have H := decodeBE_lt (Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s p)) len)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at H
  exact H

theorem pow256_words {len : Nat} (hw : len % 4 = 0) : 256 ^ len = 2 ^ (32 * (len / 4)) := by
  rw [show 32 * (len / 4) = 8 * len by omega_arith, Nat.pow_mul]

/-- The context of the modulus at a saved pointer, without unused constants. -/
theorem setup_ok {s : State} {base : Addr} {size len n m : Nat} {modulus : Field} (hs : Ws s base size)
    (hz : 4960 ≤ size) (w : Width len n) (R : Ready s base (.input modulus) len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Core.setup len modulus) s fun t => Context n m base size t ∧
      Outs base arithRanges s.mem t.mem ∧ Rest coreClob s t := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have cb := contextBytes_le n48
  unfold Core.setup
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) R (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  refine WP.mono (Context.light_ok wu (by omega_arith) n0 n48 (by rw [← hm]; exact Vu) hm1 hodd)
    fun t ⟨ct, Ot, Rt⟩ => ⟨ct, ?_, (Ru.mono (by decide)).trans (Rt.mono (by decide))⟩
  exact (Outs.of_slot (i := 0) Ou (by decide) n48).trans (Outs.arith Ot (setupRanges_arith n48))

/-- The result slot of a context, below the modulus, in its `len` bytes. -/
theorem result_bytes {mem : Mem} {base : Addr} {n len m : Nat} (hw : len % 4 = 0) (hl : len ≤ 8 * n)
    (hm : m < 256 ^ len) (hv : val32 mem base (slot n 9) (2 * n) < m) :
    val32 mem base (slot n 9) (len / 4) = val32 mem base (slot n 9) (2 * n) :=
  val32_prefix_of_lt (by omega_arith) (by rw [← pow256_words hw]; omega_arith)

theorem power_ok {s : State} {base : Addr} {size len expLen n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (he4 : 4 ≤ expLen) (he : expLen ≤ len) (hwe : expLen % 4 = 0)
    (Rq : Ready s base (.input modulus) len) (Ra : Ready s base a len) (Rb : Ready s base b expLen)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.power len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len ^ operand base s b expLen % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have cb := contextBytes_le n48
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.power
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) he4 (by omega_arith) hwe
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  -- The values.
  have M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b expLen := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  have ek : (expLen + 3) / 4 ≤ 2 * n := by omega_arith
  have E₂ : val32 u₂.mem base (slot n 11) ((expLen + 3) / 4) = operand base s b expLen := by
    rw [val32_prefix_of_lt ek (by rw [B₂']; exact decoded_exponent_fits _ _ _), B₂']
  refine WP.seq (WP.mono (Pow.call_ok w₂ (by omega_arith) n0 n48 (by omega_arith) ek M₂ hm1 hodd)
    fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, E₂]

theorem productMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (Rq : Ready s base (.input modulus) len) (Ra : Ready s base a len) (Rb : Ready s base b len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.productMod len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len * operand base s b len % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have cb := contextBytes_le n48
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.productMod
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  have M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  refine WP.seq (WP.mono (Pow.mulCall_ok w₂ (by omega_arith) n0 n48 M₂ hm1 hodd) fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, B₂']

theorem sum_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (Rq : Ready s base (.input .q) len) (Ra : Ready s base a len) (Rb : Ready s base b len)
    (hm : operand base s (.input .q) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (hA : operand base s a len < m) (hB : operand base s b len < m)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.sum len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len ((operand base s a len + operand base s b len) % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.sum
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (setup_ok hs hz w Rq hm hm1 hodd) fun u ⟨cu, Ou, Ru⟩ => ?_)
  have Rau := Ra.keep_rest Ru (O := Ou) (hO := arith_hdr)
  have Rbu := Rb.keep_rest Ru (O := Ou) (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) cu.ws (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  have c₁ := cu.of_slot w₁ O₁ (by decide)
  have Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) c₁.ws (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  have c₂ := c₁.of_slot w₂ O₂ (by decide)
  have K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  have R₂' : Rest coreClob s u₂ := (Ru.trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  have A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou)
  have B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou
  refine WP.seq (WP.mono (ordinaryAdd_ok c₂ (by rw [A₂]; exact hA) (by rw [B₂']; exact hB))
    fun u₃ ⟨c₃, K₃, V₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) c₃.ws w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((K₃.rest.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith K₃.streamRanges (streamRanges_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  have lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, B₂']

/-! ## Reductions -/

/-- The byte count of a reduction. -/
def countValue (base : Addr) (s : State) : Core.Count → Nat
  | .imm len => len
  | .field f => (s.mem.readW (off base (Impl.Dsa.Arm.Layout.field f)) 32).toNat

def CountOk : Core.Count → Prop
  | .imm len => len < 2 ^ 16
  | .field f => f ≠ .mask

theorem countValue_keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} (O : Outs base rs s.mem t.mem)
    (hO : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1) {c : Core.Count} (hc : CountOk c) :
    countValue base t c = countValue base s c := by
  cases c with
  | imm len => rfl
  | field f => exact congrArg BitVec.toNat (field_keep O hO hc)

/-- `lr = r11 + count`. -/
theorem countEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    {c : Core.Count} (hc : CountOk c) :
    WP isa (.block (Core.countEnd c)) s fun t =>
      t.gpr .lr = s.gpr .r11 + BitVec.ofNat 32 (countValue base s c) ∧ Rest [.lr] s t ∧ t.mem = s.mem := by
  cases c with
  | imm len =>
    refine wp_movw fun t₁ u₁ => wp_dp (op2_reg _ _) fun t u₂ => WP.block_nil
      ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r11 (by decide), movw_ofNat hc, BitVec.add_comm]
    rfl
  | field f =>
    have := field_bounds f
    refine wp_ldr (by omega_arith) (hs.ea12 (by omega_arith)) (hs.read (by omega_arith)) fun t₁ u₁ => wp_dp (op2_reg _ _) fun t u₂ =>
      WP.block_nil ⟨?_, (u₁.rest (by decide)).trans (u₂.rest (by decide)), by rw [u₂.mem, u₁.mem]⟩
    have e : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
      apply BitVec.eq_of_toNat_eq; simp
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r11 (by decide), countValue, e, BitVec.add_comm]

/-- `count` bytes at `input` reduced modulo `q`. -/
theorem reduce_ok {s : State} {base : Addr} {size len n m output : Nat} {count : Core.Count} {input : Pointer}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (Rq : Ready s base (.input .q) len)
    (hc : CountOk count) (Ri : Ready s base input (countValue base s count))
    (hm : operand base s (.input .q) len = m) (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.reduce len count input output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s input (countValue base s count) % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s9 := slot_lt (i := 9) n48 (by decide)
  have cb := contextBytes_le n48
  have nw := hs.nowrap
  have mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.reduce
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  have Riu := Ri.keep_rest Ru (O := Ou') (hO := arith_hdr)
  have Cu := countValue_keep Ou' arith_hdr hc
  rw [← Cu] at Riu
  refine WP.seq (VG.Proof.X25519.Arm.WP.append (pointer_ok wu (by omega_arith) Riu.ok) fun v ⟨Pv, Rv, Mv⟩ =>
    WP.mono (countEnd_ok (wu.of_rest Rv (by decide)) (by omega_arith) hc) fun x ⟨Lx, Rx, Mx⟩ => ?_)
  have Rux : Rest [.r4, .r11, .lr] u x := (Rv.mono (by decide)).trans (Rx.mono (by decide))
  have wx := wu.of_rest Rux (by decide)
  have Cv : countValue base v count = countValue base u count :=
    countValue_keep (rs := []) (fun x _ => by rw [Mv]) (by simp) hc
  have r11 : x.gpr .r11 = pointerValue base u input := by rw [Rx.gpr .r11 (by decide), Pv]
  rw [Cv, Pv] at Lx
  have cl : countValue base s count < 2 ^ 32 := by
    cases count with
    | imm len => exact Nat.lt_trans hc (by decide)
    | field f => exact BitVec.isLt _
  have Vx : val32 x.mem base (slot n 0) (2 * n) = m := by rw [Mx, Mv]; exact Vu.trans hm
  have hrx : InRegions (x.rd ++ x.wr) (State.addr (pointerValue base u input)) (countValue base u count) := by
    have := Riu.reads 0 (countValue base u count) (by omega_arith)
    rw [Rux.rd, Rux.wr]
    simpa only [BitVec.add_zero] using this
  refine WP.seq (WP.mono (Pow.reduceCall_ok wx (by omega_arith) n0 n48 Vx hm255 hodd r11 Lx Riu.fits
    (by rw [Cu]; exact cl) hrx (Riu.apart.sub_right (Region.sub_prefix cb))) fun y ⟨wy, Vy, Oy, Ry⟩ => ?_)
  refine WP.mono (store_ok (output := output) wy w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, ((Ru.mono (by decide)).trans (Rux.mono (by decide))).trans
      ((Ry.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out Ou' _ _).trans (Outs.arith_out (Outs.arith (by rw [Mx, Mv] at Oy; exact Oy)
        (scratch_arith n48)) _ _)).trans (Outs.out Ot)⟩
  have lt : val32 y.mem base (slot n 9) (2 * n) < m := by rw [Vy]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt, Vy, Mx, Mv, Cu]
  exact congrArg (fun v => Spec.Dsa.encodeBE len (v % m)) (Ri.arith (Ru.gpr .r12 (by decide)) Ou')

end VG.Proof.Dsa.Arm

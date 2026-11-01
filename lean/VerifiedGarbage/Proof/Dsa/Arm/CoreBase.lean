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
  simp only [contextBytes, slot, stride]; omega

/-- Ranges within the arithmetic's. -/
theorem Outs.arith {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960)) : Outs base arithRanges m m' :=
  fun x hx => O x fun r hr => by
    have h1 := hx (0, 64) (by simp [arithRanges])
    have h2 := hx (256, 4704) (by simp [arithRanges])
    have := h r hr
    simp only at h1 h2
    omega

theorem Outs.of_slot {base : Addr} {n i : Nat} {m m' : Mem} (O : Outside base (slot n i) (8 * n) m m')
    (hi : i < 12) (hn : n ≤ 48) : Outs base arithRanges m m' :=
  Outs.arith (Outs.of_outside O (List.mem_singleton_self _)) fun r hr => by
    have := slot_bound (n := n) hi
    have := contextBytes_le hn
    have := slot_header n i
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [stride] at *
    omega

theorem setupRanges_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil, or_false] at *
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem exponentRanges_arith {n k : Nat} (hn : n ≤ 48) (hk : k ≤ 2 * n) :
    ∀ r ∈ exponentRanges n k, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [exponentRanges, productRanges, maskO, contextBytes, slot, stride, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at *
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem streamRanges_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ streamRanges n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [streamRanges, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil, or_false] at *
  rintro r (rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem scratch_arith {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ Impl.Dsa.Arm.Pow.scratch n, r.1 + r.2 ≤ 64 ∨ (256 ≤ r.1 ∧ r.1 + r.2 ≤ 4960) := by
  have := contextBytes_le hn
  simp only [Impl.Dsa.Arm.Pow.scratch, contextBytes, slot, stride, List.mem_cons, List.not_mem_nil,
    or_false] at *
  rintro r (rfl | rfl) <;> simp only <;> omega

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
    rw [ofs_off base (by omega)]
    omega).symm).symm

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
  outs_bytes O (by have := R.fits; omega) (fun r hr => by have := hO r hr; omega)
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
    exact wp_ldr (by omega) (hs.ea12 (by omega)) (hs.read (by omega)) fun t u =>
      WP.block_nil ⟨u.gpr, u.rest (by decide), u.mem⟩
  | «local» o =>
    exact wp_ptr (is := []) (by decide) hp fun t u => WP.block_nil ⟨u.gpr, u.rest (by decide), u.mem⟩
  | signatureS =>
    have := field_bounds .signature
    have := field_bounds .qLen
    refine wp_ldr (by omega) (hs.ea12 (by omega)) (hs.read (by omega)) fun t₁ u₁ => ?_
    have w₁ := hs.of_upd u₁ (by decide)
    refine wp_ldr (by omega) (w₁.ea12 (by omega)) (w₁.read (by omega)) fun t₂ u₂ => ?_
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
  refine WP.mono (loadComponent_ok wu ho h16 hpad (by rw [Pu]; have := R.fits; omega) h4 hlen hw4
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
    have := wu.ea (r := .r12) (K := 0) (d := output) (BitVec.add_zero _).symm (by omega)
    rwa [Nat.zero_add, Ru.gpr .r12 (by decide)] at this
  have pn : (u.gpr .r11).toNat = base.toNat + output := by
    rw [r11, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (by omega : output < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]
  have r3 : u.gpr .r3 = if true then BitVec.allOnes 32 else 0 := by
    rw [v₄.gpr, v₃.gpr, dpVal, v₂.gpr]; decide
  have mu : u.mem = s.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have r9 : resS n + len ≤ output := by simp only [resS]; omega
  have hd : Region.Disjoint ⟨off base (resS n), len⟩ ⟨off base output, len⟩ :=
    Offset.disjoint base (.inl r9) (by omega) (by omega)
  refine WP.mono (storeComponent_ok (input := resS n) (len := len) wu true r3 (by simp only [resS]; omega) (by simp only [resS]; omega) h4 hw4
    (by rw [pn]; omega)
    (fun e k hek => by rw [pa]; exact Offset.add_add base output e ▸ wu.write (by omega))
    (by rw [pa]; exact hd))
    fun t ⟨_, Vt, Rt, Ot⟩ => ⟨?_, (Ru.mono (by decide)).trans (Rt.mono (by decide)), ?_⟩
  · simpa only [pa, mu, ite_true, resS] using Vt
  · rw [pa, mu] at Ot
    exact outside_rebase Ot (by omega)

end VG.Proof.Dsa.Arm

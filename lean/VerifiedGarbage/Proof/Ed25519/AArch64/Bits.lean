module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ed25519.AArch64.BitByte`, which this module and modules that import it used -/

section

/-! Byte stores and expansion of one scalar byte into eight bits. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega_using [h])
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    off base d = off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => ofs base x) h
    simp only [ofs_off' base hd, ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) : (m.writeW (off base d) v) x = m x := by
  rw [writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (ofs_off' base hd) hx

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((((b.setWidth 64 >>> j) &&& BitVec.ofNat 64 1).setWidth 32).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := fun b j _ => by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]; exact bitByte 64 (by decide) b j

theorem expandScalarBit_ok {s : State} {base : Addr} (hs : Scr s base)
    (i j : Nat) (hi : i < 64) (hj : j < 8)
    (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block (expandScalarBit j)) s fun t =>
      (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (off base (768 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have _hcap : workSize true = 8192 := rfl
  have hw : InRegions s.wr (off base (768 + (8 * i + j))) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (by omega_using [hi, hj, _hcap]) (by omega_using [hi, hj])⟩
  have he : off base (8 * i) + BitVec.ofNat 64 (768 + j) = off base (768 + (8 * i + j)) := by
    rw [Offset.add_add]; exact congrArg (off base) (by omega_using [])
  apply WP.of_runBlock
  simp only [expandScalarBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show j < Size.x.bits from by change j < 64; omega_using [hj],
    addr, State.store, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, hp, hone, hb, he, hw, Nat.mod_one,
    show 768 + j < 4096 * 1 from by omega_using [hj], and_self,
    ite_true, ite_false, reduceCtorEq, bit_byte b j hj,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, True.intro, rfl, ?_⟩
  · simp only [hr, ite_false]
  · rfl

structure BitKeep (base : Addr) (i n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x2 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base (768 + 8 * i) n s.mem t.mem

theorem BitKeep.scratch {base : Addr} {i n : Nat} {s t : State}
    (h : BitKeep base i n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scalarBitPrefix_ok {s : State} {base : Addr} (hs : Scr s base)
    (i n : Nat) (hi : i < 64) (hn : n ≤ 8) (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block ((List.range n).flatMap expandScalarBit)) s fun t => BitKeep base i n s t ∧
      ∀ j < n, t.mem (off base (768 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩, fun _ h => by omega⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega_using [hn]) hp hone hb) fun t ⟨hk, hv⟩ => ?_
    refine WP.mono (expandScalarBit_ok (hk.scratch hs) i n hi (by omega_using [hn])
      ((hk.gpr _ (by decide)).trans hp) ((hk.gpr _ (by decide)).trans hone) b ((hk.gpr _ (by decide)).trans hb))
      fun u ⟨ug, ur, uw, usp, um⟩ => ?_
    refine ⟨⟨fun r hr => (ug r hr).trans (hk.gpr r hr), ur.trans hk.rd, uw.trans hk.wr, usp.trans hk.sp, ?_⟩, ?_⟩
    · intro p hp
      rw [um, writeW8_outside _ _ _ (by omega_using [hi, hn]) (by omega_using [hp]), hk.mem p (by omega_using [hp])]
    · intro j hj
      rw [um, writeW8_apply]
      by_cases h : j = n
      · subst j; rw [ite_eq_left rfl]
      · rw [ite_eq_right (fun he => h (by
          have hh := (off_eq_iff base (by omega_using [hi, hn, hj]) (by omega_using [hi, hn])).mp he
          omega_using [hh]))]
        exact hv j (by omega_using [hj, h])

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.BitRead`. -/

@[expose] public section

section
/-! Load the next scalar byte and calculate its bit-output address. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

theorem scalarByteRead_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i : Nat) (hi : i < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block [.add .x .x8 .x1 .x19, .ldrb .x8 .x8 0,
      .lsl .x .x9 .x19 3, .add .x .x9 .x0 .x9]) s fun t =>
      t.gpr .x8 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x9 = off base (8 * i) ∧
      Keeps [.x8, .x9] s t := by
  have hshift : (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega_using [hi] : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [hi] : 8 * i < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (0 : Nat) < 4096 * 1 from by decide, show (0 : Nat) % 1 = 0 from rfl,
    show (3 : Nat) < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, hc, hs.x0, hshift, BitVec.add_zero, BitVec.setWidth_eq, hr, read_byte,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.setWidth_setWidth (by decide), True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Expand all scalar bits, without X25519's clamping. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure BitsKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.x8, .x9, .x2, .x19, .x11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o n s.mem t.mem

theorem BitsKeep.scratch {base : Addr} {o n : Nat} {s t : State}
    (h : BitsKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BitsKeep.trans {base : Addr} {o n : Nat} {s t u : State}
    (h : BitsKeep base o n s t) (k : BitsKeep base o n t u) : BitsKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem BitsKeep.mono {base : Addr} {o n o' n' : Nat} {s t : State}
    (h : BitsKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : BitsKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem scalarByteBits_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i count : Nat) (hi : i < count) (hn : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) (hone : s.gpr .x11 = BitVec.ofNat 64 1) :
    WP isa (.block (scalarByteBits count)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x8 != 0) = decide (i + 1 ≠ count) ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧
      BitsKeep base (768 + 8 * i) 8 s t ∧
      ∀ j < 8, t.mem (off base (768 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1) := by
  rw [scalarByteBits, List.append_assoc, WP.block_append_iff]
  refine WP.mono (scalarByteRead_ok hs i (by omega_using [hi, hn]) hc hp hr) fun a ⟨av, ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitPrefix_ok (hs.of_keeps ka (by decide)) i 8 (by omega_using [hi, hn]) (by decide)
    ap ((ka.gpr _ (by decide)).trans hone) _ av) fun b ⟨kb, bv⟩ => ?_
  refine WP.mono (powersNext_ok b i count hi hn
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hc))) fun t ⟨tc, tz, kt⟩ => ?_
  refine ⟨tc, tz, ?_, ⟨fun r hr => ?_, kt.rd.trans (kb.rd.trans ka.rd),
    kt.wr.trans (kb.wr.trans ka.wr), kt.sp.trans (kb.sp.trans ka.sp), ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hone]
  · have h8 : r ≠ .x8 := fun he => hr (by simp [he])
    have h9 : r ≠ .x9 := fun he => hr (by simp [he])
    have h2 : r ≠ .x2 := fun he => hr (by simp [he])
    have h19 : r ≠ .x19 := fun he => hr (by simp [he])
    exact (kt.gpr r (by simp [h8, h19])).trans
      ((kb.gpr r h2).trans (ka.gpr r (by simp [h8, h9])))
  · rw [kt.mem, ← ka.mem]; exact kb.mem
  · rw [kt.mem]; exact bv

structure BitsInv (s₀ : State) (base k : Addr) (count i : Nat) (s : State) : Prop where
  scratch : Scr s base
  ptr : s.gpr .x1 = k
  counter : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x11 = BitVec.ofNat 64 1
  keep : BitsKeep base 768 (8 * count) s₀ s
  bits : ∀ t < 8 * i, s.mem (off base (768 + t)) =
    BitVec.ofNat 8 (((s₀.mem (off k (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem scalarBitsLoop_ok {s₀ : State} {base k : Addr} (count : Nat) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s₀.rd ++ s₀.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    ∀ i s, i < count → BitsInv s₀ base k count i s →
      WP isa (.loop (.block (scalarByteBits count)) (.nonzero .x .x8)) s fun t => BitsInv s₀ base k count count t := by
  intro i s hi h
  refine WP.loop (M := isa) (body := .block (scalarByteBits count)) (c := .nonzero .x .x8)
    (Q := fun t => BitsInv s₀ base k count count t)
    (fun n s => ∃ i, n = count - i ∧ i < count ∧ BitsInv s₀ base k count i s) ?_
    (count - i) s ⟨i, rfl, hi, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (scalarByteBits_ok h.scratch i count hi hn h.counter h.ptr
    (by rw [h.keep.rd, h.keep.wr]; exact hr i hi) h.one) fun t ⟨tc, tz, tone, tk, tb⟩ => ?_
  have hbyte : s.mem (off k i) = s₀.mem (off k i) := h.keep.mem _ (by have := hd i hi; omega_using [hn, this])
  have inv : BitsInv s₀ base k count (i + 1) t := by
    refine ⟨tk.scratch h.scratch, (tk.gpr _ (by decide)).trans h.ptr, tc, tone,
      h.keep.trans (tk.mono (by omega_using []) (by omega_using [hi])), fun j hj => ?_⟩
    by_cases hp : j < 8 * i
    · rw [tk.mem _ (by rw [ofs_off' base (by omega_using [hn, hi, hj])]; omega_using [hp]), h.bits j hp]
    · have e := tb (j - 8 * i) (by omega_using [hj])
      rw [show 8 * i + (j - 8 * i) = j by omega_using [hp], hbyte] at e
      rw [e, show j / 8 = i by omega_using [hj, hp], show j % 8 = j - 8 * i by omega_using [hj, hp]]
  by_cases he : i + 1 = count
  · exact Or.inl ⟨by simp only [eval, read_x, tz, he, show decide (count ≠ count) = false from decide_eq_false (not_not_intro rfl)], he ▸ inv⟩
  · exact Or.inr ⟨by simp only [eval, read_x, tz, decide_eq_true he],
      count - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], inv⟩

theorem input_byte (m : Mem) (k : Addr) (count j : Nat) (hj : j < count) :
    (Spec.Ed25519.bytesAt m k count).getD j 0 = m (off k j) := by
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem scalarBitsInit_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0, .movz .w .x11 1 0]) s fun t =>
      t.gpr .x19 = 0 ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧ Keeps [.x19, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem expandScalarBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBits count) s fun t => BitsKeep base 768 (8 * count) s t ∧
      ∀ j < 8 * count, t.mem (off base (768 + j)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k count) / 2 ^ j) % 2) := by
  rw [scalarBits]
  refine WP.seq (WP.mono (scalarBitsInit_ok s) fun a ⟨ac, aone, ka⟩ => ?_)
  have init : BitsInv s base k count 0 a := by
    refine ⟨hs.of_keeps ka (by decide), (ka.gpr _ (by decide)).trans hp, ac, aone,
      ⟨fun r hr => ka.gpr r (fun hm => hr ((by decide : [Reg.x19, .x11] ⊆ [Reg.x8, .x9, .x2, .x19, .x11]) hm)), ka.rd, ka.wr, ka.sp, ?_⟩, fun j hj => by omega⟩
    rw [ka.mem]; exact Outside.refl _ _ _ _
  refine WP.mono (scalarBitsLoop_ok count hn hr hd 0 a hn0 init) fun t h => ?_
  refine ⟨h.keep, fun j hj => ?_⟩
  rw [h.bits j hj]
  have hb := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt s.mem k count) j
  rw [← decodeLE_eq, input_byte _ _ _ _ (by omega_using [hj])] at hb
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb ⊢
  exact congrArg (BitVec.ofNat 8) hb.symm

end VG.Proof.Ed25519.AArch64
